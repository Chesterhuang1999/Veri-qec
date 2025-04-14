#----------#
# Developer: Chester Huang
# Date: 2024/11/10
# Description: Parallel execution for detection property, tanner code 
#----------#


import time
import numpy as np
import math
from multiprocessing import Pool, Manager
from smt_detect_only import *
from itertools import combinations
from timebudget import timebudget
import datetime
import tblib.pickling_support
import os 
from contextlib import redirect_stdout
import sys
import argparse

##Import special codes
from Dataset import special_codes
from Dataset import qldpc_codes

sys.setrecursionlimit(1000000)

#### Handling exceptions in multiprocessing ####
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()
    
    def re_raise(self):
        raise self.ee.with_traceback(self.tb)

#### Load the subtask in each thread ####   
def worker(task_id, err_vals, opt): 
    try:
        start = time.time()
        
        if opt == 'x':
            smttime, res = seq_cond_checker_detect_bzla(packed_x, err_vals, opt)
            errs_enum = [f"ez_{ind + 1}" for ind, val in enumerate(err_vals) if val == 1]
        else:
            smttime, res = seq_cond_checker_detect_bzla(packed_z, err_vals, opt)
            errs_enum = [f"ex_{ind + 1}" for ind, val in enumerate(err_vals) if val == 1]
        end = time.time()
        cost = end - start 
        
        return task_id, smttime, str(res)
        
    except Exception as e:
        return task_id, ExceptionWrapper(e)

#### Estimate the difficulty of the task by combination ####
def estimate_difficulty(remained_qubits, remained_ones):
    n = remained_qubits
    k = remained_ones
    
    if k >= n:
        return 2 ** n
    return math.comb(n, k)
   
#### Generating subtasks by enumerating variables ####
class subtask_generator:
    def __init__(self, distance, numq, max_proc_num, checktype, is_Ham7) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        self.checktype = checktype
        
        self.num_qubits = numq
        self.Ham7 = is_Ham7
        self.tasks = []
        
       
        self.target_task_num =  2 * (10 ** 4)
        self.full_difficulty = estimate_difficulty(self.num_qubits, distance - 1)
        self.parti_diffi_thres = self.full_difficulty // self.target_task_num

    ### Judging terminate or not ###
    def easy_enough(self, remained_qubit_num, remained_one_num, checktype):
        if remained_qubit_num == 1:
            return True
        if remained_qubit_num <= remained_one_num + 1:
            return True
       
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num
        
        ## For Tanner code detection ##
        if self.Ham7:
            if checktype == 'x':
                if 12 * assigned_one_num * self.distance +  assigned_bit_num < self.num_qubits:
                    return False
            else:
                if 7 * assigned_one_num * self.distance +  assigned_bit_num < self.num_qubits:
                    return False
        ## For detection other than Tanner code ##
        else:
            if 4 * assigned_one_num * self.distance + 3 * assigned_bit_num < self.num_qubits:
                return False
        
     
        
        return True
        
    ### Recursively enumerate the variables ###
    def generate_tasks(self, checktype, remained_qubit_num, remained_one_num, curr_enum_qubits: list):
        
        if self.easy_enough(remained_qubit_num, remained_one_num, checktype):
            self.tasks.append(list(curr_enum_qubits))
            return

        

        if remained_one_num > 0:

            curr_enum_qubits.append(1)
            self.generate_tasks(checktype, remained_qubit_num - 1, remained_one_num - 1, curr_enum_qubits)
            curr_enum_qubits.pop()


        curr_enum_qubits.append(0)
        self.generate_tasks(checktype, remained_qubit_num - 1, remained_one_num, curr_enum_qubits)
        curr_enum_qubits.pop()
        

    def __call__(self):
        self.generate_tasks(self.checktype, self.num_qubits, self.distance - 1, [])
        return self.tasks


#### Task generator with fixed tasks, fixed by err_inds ####
def task_generator_fixed(err_inds, numq, count):
    tasks = []
    n = len(err_inds)
    for k in range(1, count + 1):
        subp = list(combinations(err_inds, n - k))
        for j in range(len(subp)):
            bin_arr = np.zeros(numq, dtype = int)
            for i in subp[j]:
                bin_arr[i] = 1

            tasks.append(bin_arr)
    return tasks    


processed_job = 0
solved_job = 0
unsolved_job = 0
sat_job = 0
unsat_job = 0


#### Print current Progress ####
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


#### Process the return value of the task ####
def process_callback(result, pool):

    global err_info
    global is_sat
    if isinstance(result[1], ExceptionWrapper):
        task_id = result[0]
        err_info.append(result[1])
        return
    global processed_job
    global last_print
    
    task_id, time_cost, res_smt = result
    ## Find counterexample, terminate the process ##
    if res_smt == 'sat':
        is_sat = 1
        
        print("Counterexample found, there exists errors cannot be corrected.\n")
        print('Counterexample Info:\n')
        print(f'rank: {task_id} | time: {time_cost}')
     
        print("About to terminate")
        
        pool.terminate()

    ## Find unknown instance, step forward ##    
    elif res_smt == 'unknown':
        
        print('Difficult instances, information:')
        print(f'rank: {task_id} | time: {time_cost}')
       
    ### Print the current process ###
    curr_time = time.time()
    processed_job += 1
    if curr_time - last_print > 60.0:
        info = "{}/{}: finish job file[{}], cost_time: {}" \
                .format(processed_job, total_job, task_id, time_cost)
        print(info)
        
        print(get_current_infos())
        sys.stdout.flush()
        last_print = curr_time
    
def process_error(error):
    print(f'error: {error}')

#### Pre-processing the tasks ####
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
    info = [num_bit, num_zero, num_one, one_pos]
    # info = [f'num_bit: {num_bit}', f'num_zero: {num_zero}', f'num_one: {num_one}', f'one_pos: {one_pos}']
    return [task_id, task, info]


#### Checking the condition in parallel ####
@timebudget 
def cond_checker_Tanner(matrix, dx, dz, max_proc_num, is_sym = False):
    
    global packed_x
    global packed_z
    global total_job
   
    global start_time
    global max_process_num
    global err_info
    global last_print
    global is_sat
    is_sat = 0
    
    max_process_num = max_proc_num
    start_time = time.time()
    ## Generate the verification condition ##
    numq = matrix.shape[1] // 2
    is_Ham7 = False if numq != 343 else True
    packed_x, packed_z = cond_generator(matrix, dx, dz, is_Ham7, is_sym)
    end_gen = time.time()
    print(f"Condition generation time: {end_gen - start_time}")

    ## Generate tasks w.r.t supposed distances ##
    unknown_info = []
    tg_x = subtask_generator(dz, numq, max_proc_num, 'z', is_Ham7)
    tasks_x = tg_x() 
    tg_z = subtask_generator(dx, numq, max_proc_num, 'x', is_Ham7)
    tasks_z = tg_z() 
    total_job = len(tasks_x) + len(tasks_z)
    
    print(f"tasks for X error: {len(tasks_z)} | tasks for Z error: {len(tasks_x)}")
    print(f"total_job: {total_job}")

    print("Task generated. Start checking.")
   
    start_time = time.time()
    last_print = start_time
    
    err_info = []
    ## Start checking ##
    with Pool(processes = max_proc_num) as pool1:
        result_objects = []
        for i, task in enumerate(tasks_z):
            opt = 'z'    
            
            result_objects.append(pool1.apply_async(worker, (i, task, opt), 
                                                callback= lambda result: process_callback(result, pool1), 
                                                error_callback=process_error))
        for i, task in enumerate(tasks_x):
            opt = 'x'
            
            result_objects.append(pool1.apply_async(worker, (i + len(tasks_z), task, opt), 
                                                callback=lambda result: process_callback(result, pool1), 
                                                error_callback=process_error))
        pool1.close()
        pool1.join()
    endt_x = time.time()
   
    if is_sat == 0: 
        print("No counterexample found, all errors can be detected.\n")
   
    print(f"Check time: {endt_x - start_time}")
    

    for i, ei in enumerate(err_info):   
        ei.re_raise()

if __name__ == "__main__":
    tblib.pickling_support.install()

    Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                   [1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
    Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])
    Ham523 = np.array([[1,1,0,1,0], [0,1,0,1,1]])
    Ham532 = np.array([[1,1,1,0,0],[1,0,0,1,0],[0,1,0,0,1]])
    Rep51 = np.array([[1, 1, 0, 0, 0],
                  [1, 0, 1, 0, 0],
                  [1, 0, 0, 1, 0],
                  [1, 0, 0, 0, 1]])
    Par54 = np.array([[1, 1, 1, 1, 1]])
    Par76 = np.array([[1, 1, 1, 1, 1, 1, 1]])
    Rep71 = np.array([[1, 1, 0, 0, 0, 0, 0],
                  [1, 0, 1, 0, 0, 0, 0],
                  [1, 0, 0, 1, 0, 0, 0],
                  [1, 0, 0, 0, 1, 0, 0],
                  [1, 0, 0, 0, 0, 1, 0],
                  [1, 0, 0, 0, 0, 0, 1]])
    matrix = qldpc_codes.stabs_Tanner(1, 1, Par54, Rep51)
 
    #### Parsing input parameters ####
    parser = argparse.ArgumentParser(description='Error detection for quantum codes')
    parser.add_argument('--cpucount', type = int, default = 16, help = 'The number of CPU cores')
    parser.add_argument('--basis', type = str, default = 'Ham7', help = 'The basis type')
 
    args = parser.parse_args()
    
    max_proc_num = args.cpucount
    basis = args.basis
    output_dir = './eval-Output'
    matrix = qldpc_codes.stabs_Tanner(1, 1, Par54, Rep51) if basis == 'Rep5' else qldpc_codes.stabs_Tanner(1, 1, Ham743, Ham733)
    with open(f'{output_dir}/detect_Tanner_{basis}.txt', 'w') as f:
        
        with redirect_stdout(f):
            cond_checker_Tanner(matrix, 4, 4, max_proc_num)
    
    
