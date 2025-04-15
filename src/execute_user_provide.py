#----------#
# Developer: Chester Huang
# Date: 2024/11/05
# Description: Parallel execution for accurate correction property, with user-provided constraints
#----------#


import time
import numpy as np
import math
from multiprocessing import Pool
from smt_partition_merge import *


import os
from contextlib import redirect_stdout
import argparse
from timebudget import timebudget
import datetime
import tblib.pickling_support
import sys

##Import special codes
from Dataset import special_codes
from Dataset import qldpc_codes

sys.setrecursionlimit(1000000)

### Handling errors in Pools ###
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()
    
    def re_raise(self):
        raise self.ee.with_traceback(self.tb)

### Load the subtask in each thread ###
def worker(task_id, err_vals, info, opt):

    try:
        start = time.time()
        if opt == 'x':
            if info is not None:
                smttime, res = seq_cond_checker_user(packed_x, err_vals, info, opt)
            else:
                smttime, res = seq_cond_checker(packed_x, err_vals, opt)
            
        else:
            if info is not None:
                smttime, res = seq_cond_checker_user(packed_z, err_vals, info, opt)
            else: 
                smttime, res = seq_cond_checker(packed_z, err_vals, opt)
        end = time.time()
        cost = end - start 
        return task_id, smttime, str(res)

    except Exception as e:
        print(e)
        return task_id, ExceptionWrapper(e)

### Estimate the difficulty of the task by combination ###
def estimate_difficulty(remained_qubits, remained_ones):
    n = remained_qubits
    k = remained_ones
    
    if k >= n:
        return 2 ** n
    k = min(k, n - k)
    
    return sum(math.comb(n, i) for i in range(k + 1))

### Generating subtasks by enumerating variables ###
class subtask_generator:
    def __init__(self, distance, numq, max_proc_num, method) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        self.method = method
        self.value = 2 if method == 'discrete' else (4 / 3)

        self.num_qubits = numq
        self.tasks = []
        self.nonzero_len = (self.distance**2 - 1) // 2
        
        self.assigned_bit_thres = 16
        
        self.target_task_num =  max_proc_num * 2
        self.full_difficulty = estimate_difficulty(self.num_qubits, distance - 1)
        self.parti_diffi_thres = self.full_difficulty // self.target_task_num

    ### Judging terminate or not ###
    def easy_enough_I(self, remained_qubit_num, remained_one_num):
        if remained_qubit_num == 1:
            return True
       
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num
        
        ### For verification task ###

        if int(self.value * assigned_one_num * self.distance) + assigned_bit_num < self.num_qubits:
            return False
        
        return True
    
    def easy_enough_II(self, remained_qubit_num, remained_one_num):
        if remained_qubit_num == 1:
            return True
       
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num
        
        ### For verification task ###
        if  int(4 * assigned_one_num * self.distance // 3) + assigned_bit_num < self.num_qubits:
            return False
        
    ### Constraint II: The errors come from a restricted set (maybe the whole set)
    def generate_tasks_II(self, remained_qubit_num, remained_one_num, curr_enum_qubits: list):
        
        if self.easy_enough_II(remained_qubit_num, remained_one_num):
            self.tasks.append(list(curr_enum_qubits))
            return

        curr_enum_qubits.append(0)
        
        self.generate_tasks_II(remained_qubit_num - 1, remained_one_num, curr_enum_qubits)
        curr_enum_qubits.pop()
        
        if remained_one_num > 0 :
            curr_enum_qubits.append(1)
            
            self.generate_tasks_II(remained_qubit_num - 1, remained_one_num - 1, curr_enum_qubits)
            curr_enum_qubits.pop()

    ### Constraint I: The number of 1s in each length d segment is at most 1
    def generate_tasks_I(self, remained_qubit_num, remained_one_num, curr_seg_count, curr_enum_qubits: list):
        
        # easy_judgment = self.easy_enough_I(remained_qubit_num, remained_one_num) if cstype == 'discrete' else self.easy_enough_II(remained_qubit_num, remained_one_num)
        if self.easy_enough_I(remained_qubit_num, remained_one_num):
            self.tasks.append(list(curr_enum_qubits))
            return
        
        if remained_qubit_num % self.distance == 0:
            curr_seg_count = 0

        curr_enum_qubits.append(0)
        
        self.generate_tasks_I(remained_qubit_num - 1, remained_one_num, curr_seg_count, curr_enum_qubits)
        curr_enum_qubits.pop()
        
        if remained_one_num > 0 and curr_seg_count < 1:
            curr_enum_qubits.append(1)
            
            self.generate_tasks_I(remained_qubit_num - 1, remained_one_num - 1, curr_seg_count + 1, curr_enum_qubits)
            curr_enum_qubits.pop()

    def __call__(self):
        ## Both local and discrete constraints are imposed ##
        if self.method == 'combined':
            err_len = (self.distance**2 - 1) // 2
            begin = np.random.randint(0, int(self.num_qubits // 4))
            support_len = int(3 * self.num_qubits // 4)
            support_range = np.arange(begin, begin + support_len)
            err_set = np.sort(np.random.choice(support_range, err_len, replace = False))
            free_set = [i for i in range(self.num_qubits) if i not in err_set]
            self.generate_tasks_I(self.nonzero_len, self.distance - 1, 0, [])
            return self.tasks, (err_set, free_set)
        
        ## Only local constraint is imposed ##
        ## Local: error can only happen in a specific(randomly choice) region ##
        elif self.method == 'local':
            err_len = (self.distance**2 - 1) // 2
            begin = np.random.randint(0, int(self.num_qubits // 4))
            support_len = int(3 * self.num_qubits // 4)
            support_range = np.arange(begin, begin + support_len)
            err_set = np.sort(np.random.choice(support_range, err_len, replace = False))
            free_set = [i for i in range(self.num_qubits) if i not in err_set]
            self.generate_tasks_II(self.nonzero_len, self.distance - 1,  [])
            return self.tasks, (err_set, free_set)
        
        ## Only discrete constraint is imposed ##
        ## Discrete: Uniformly divide the total qubits into  segments, 
        # within each segment there exists no more than one error. 
        elif self.method == 'discrete':
            self.generate_tasks_I(self.num_qubits, self.distance - 1, 0, [])
            return self.tasks

processed_job = 0
solved_job = 0
unsolved_job = 0
sat_job = 0
unsat_job = 0

### Print current Progress ###
def get_current_infos(not_done = True):
    curr_time = time.time()
    cost_time = curr_time - start_time
    estimated_time = cost_time / processed_job * total_job
    left_time = estimated_time - cost_time
    
    ret = ""
    if not_done:
        ret += " ++++++ show progress ++++++ " + "\n"
    ret += "start time: " + time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(start_time)) + "\n"
    ret += "current time: " + time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(curr_time)) + "\n"
    ret += "cost time: " + str(datetime.timedelta(seconds=cost_time)) + "\n"
    if not_done:
        ret += "left time: " + str(datetime.timedelta(seconds=left_time)) + "\n"
        ret += "estimated time: " + str(datetime.timedelta(seconds=estimated_time)) + "\n"
        ret += "estimated finished time: " + time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(start_time + estimated_time)) + "\n"
    ret += "instance per seconed(all process): {:.2f}".format(processed_job / cost_time) + "\n"
    ret += "instance average runtime(s): {:.2f}".format(cost_time * max_process_num / processed_job) + "\n"
    if not_done:
        ret += "finished persent: {:.2f}%".format(processed_job / total_job * 100.0) + "\n"
    ret += "processed jobs: {}".format(processed_job) + "\n"
    
    unprocessed_job = total_job - processed_job
    ret += "unprocessed jobs: {}".format(unprocessed_job) + "\n"
    return ret

### Process the return value of the task ###       
def process_callback(result):
    # print(result)
    global task_info
    global err_info
    global is_sat
    if isinstance(result[1], ExceptionWrapper):
        task_id = result[0]
        print(task_info[task_id])
        err_info.append(result[1])
        return
    global processed_job
    global last_print
    
    task_id, time_cost, res_smt = result
    task_info[task_id].append(time_cost)
    task_info[task_id].append(res_smt)

    ## Find counterexample, print
    if res_smt == 'sat':
        is_sat = 1

        ti = task_info[task_id]
        print("Counter example found, there exists errors cannot be corrected.\n")
        print('Counterexample Info:\n')
        print(f'rank: {task_id} | id: {ti[0]} | time: {ti[-2]} | result: {ti[-1]}\n')
        print(ti[1])
        print(f'{" | ".join(ti[2])}\n')
        print("About to terminate")
        # pool.terminate()

    curr_time = time.time()
    processed_job += 1
    if curr_time - last_print > 60.0:
        info = "{}/{}: finish job file[{}], cost_time: {}" \
                .format(processed_job, total_job, task_id, time_cost)
        print(info)
        print(task_info[task_id])
        print(get_current_infos())
        sys.stdout.flush()
        last_print = curr_time
    
def process_error(error):
    print(f'error: {error}')

### Pre-process the tasks ###
def analysis_task(task_id: int, task: list):
    num_bit = 0
    num_one = 0
    one_pos = []
    for i, bit in enumerate(task):
        if bit == 1:
            num_one += 1
            one_pos.append(i)
        num_bit += 1
    num_zero = num_bit - num_one
    info = [f'num_bit: {num_bit}', f'num_zero: {num_zero}', f'num_one: {num_one}', f'one_pos: {one_pos}']
    return [task_id, task, info]

### Checking the condition in parallel ###
@timebudget 
def cond_checker_usrprov(matrix, dx, dz, max_proc_num, cstype, is_sym = False):
    global task_info
    global packed_x
    global packed_z
    global total_job
    global start_time
    global max_process_num
    global err_info
    global last_print
    global info_x
    global info_z
    global is_sat
    is_sat = 0
    
    max_process_num = max_proc_num
    start_time = time.time()
    last_print = start_time
    numq = matrix.shape[1] // 2
    ### Generate tasks w.r.t the supposed distance ### 
    tg_x = subtask_generator(dz, numq, max_proc_num, cstype)
    tg_z = subtask_generator(dx, numq, max_proc_num, cstype)
    if cstype == 'discrete':
        tasks_x = tg_x()
        tasks_z = tg_z()
        info_x, info_z = None, None
    else:
        tasks_x, info_x = tg_x()
        tasks_z, info_z = tg_z()
        
    print("Task generated. Start checking.")
    
    total_job = len(tasks_x) + len(tasks_z)
    print(f"total_job: {total_job}")
    
    ## Generate the verification condition ##
    is_discrete = False if cstype == 'local' else True
    packed_x, packed_z = cond_generator(matrix, dx, dz, is_discrete, is_sym)
    end_gen = time.time()
    print(f"cond generation time: {end_gen - start_time}")
    
    task_info = []
    err_info = []
    ## Start checking ## 
    with Pool(processes = max_proc_num) as pool:
        result_objects = []
        for i, task in enumerate(tasks_x):
            opt = 'x'    
            task_info.append(analysis_task(i, task))
            result_objects.append(pool.apply_async(worker, (i, task, info_x, opt), callback=process_callback, error_callback=process_error))
            
        for i, task in enumerate(tasks_z):
            opt = 'z'
            task_info.append(analysis_task(i + len(tasks_x), task))
            result_objects.append(pool.apply_async(worker, (i + len(tasks_x), task, info_z, opt), callback=process_callback, error_callback=process_error))
        pool.close()
        [res.wait() for res in result_objects]
        pool.join()
    
    for i, ei in enumerate(err_info):
        ei.re_raise()

    if is_sat == 0: 
        print("No counterexample found, all errors can be corrected.")

    print("Finish all jobs. Checking time:", time.time() - end_gen)



def sur_cond_checker_usrprov(distance, max_proc_num, cstype):
    matrix = surface_matrix_gen(distance)
    cond_checker_usrprov(matrix, distance, distance, max_proc_num, cstype, is_sym = True)

if __name__ == "__main__":
    tblib.pickling_support.install()

    Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                   [1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
    Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])
  
    parser = argparse.ArgumentParser(description='Process the distance and constraints.')
    parser.add_argument('--cpucount', type = int, default = 16, help = 'The number of CPUs')
    parser.add_argument('--distance', type = int, default = 9, help = 'The distance of the code')
    parser.add_argument('--constraint', type = str, default = 'discrete', help = 'The constraint type')
    
    args = parser.parse_args()
    d = args.distance
    max_proc_num = args.cpucount
    matrix = surface_matrix_gen(d)
    cstype = args.constraint
    output_dir = './eval-Output'
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    with open(f'{output_dir}/usrprov_{d}_{cstype}.txt', 'w') as f:
        with redirect_stdout(f):
            cond_checker_usrprov(matrix, d, d, max_proc_num, cstype)

    
    
  

