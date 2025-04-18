#----------#
# Developer: Chester Huang
# Date: 2024/11/05
# Description: Parallel execution for accurate detection property
# Without Tanner code ( the termination condition for Tanner code requires re-design)
#----------#

import time
import numpy as np
import math
from multiprocessing import Pool, Manager
from smt_detect_only import *
from itertools import combinations
from condition_multiq import surface_matrix_gen
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
### Handling errors in pools
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
            smttime, res = seq_cond_checker_detect(packed_x, err_vals, opt)
            errs_enum = [f"ez_{ind + 1}" for ind, val in enumerate(err_vals) if val == 1]
        else:
            smttime, res = seq_cond_checker_detect(packed_z, err_vals, opt)
            errs_enum = [f"ex_{ind + 1}" for ind, val in enumerate(err_vals) if val == 1]
        end = time.time()
        cost = end - start 
      
        return task_id, smttime, str(res[0])
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
    def __init__(self, distance, numq, value, max_proc_num) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        self.value = value
       
        self.num_qubits = numq
        self.tasks = []
        
        self.target_task_num =  2 * (10 ** 4)
        self.full_difficulty = estimate_difficulty(self.num_qubits, distance - 1)
        self.parti_diffi_thres = self.full_difficulty // self.target_task_num

     ### Judging terminate or not ###
    def easy_enough(self, remained_qubit_num, remained_one_num):
        if remained_qubit_num == 1:
            return True
        if remained_qubit_num <= remained_one_num + 1:
            return True
    
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num
        
        ### For detection task ###
        # Termination condition is decided by the problem size 
        ta, tb = self.value
    
        if int(ta * assigned_one_num * self.distance) + tb * assigned_bit_num < self.num_qubits:
            return False
        return True
        
     ### Recursively enumerate the variables ###
    def generate_tasks(self, remained_qubit_num, remained_one_num, curr_enum_qubits: list):
        
        if self.easy_enough(remained_qubit_num, remained_one_num):
            self.tasks.append(list(curr_enum_qubits))
            return

        if remained_one_num > 0:
            curr_enum_qubits.append(1)
            self.generate_tasks(remained_qubit_num - 1, remained_one_num - 1, curr_enum_qubits)
            curr_enum_qubits.pop()

        curr_enum_qubits.append(0)
        self.generate_tasks(remained_qubit_num - 1, remained_one_num, curr_enum_qubits)
        curr_enum_qubits.pop()
        
    def __call__(self):
        
        self.generate_tasks(self.num_qubits, self.distance - 1, [])
        return self.tasks


# Task generator with fixed tasks, fixed by err_inds
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

#### Process the return value of the task ####    
def process_callback(result, pool):
    # print(result)
    global task_info
    global err_info
    global is_sat
    
    ### Print the current process ###
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

    curr_time = time.time()
    processed_job += 1
    if curr_time - last_print > 300.0:
        info = "{}/{}: finish job file[{}], cost_time: {}" \
                .format(processed_job, total_job, task_id, time_cost)
        print(info)
        print(task_info[task_id])
        print(get_current_infos())
        sys.stdout.flush()
        last_print = curr_time
    ## Find counterexample, terminate the process ##
    if res_smt == 'sat':
        is_sat = 1
        opt = 'Z' if len(task_info) != total_job else 'X'

        ti = task_info[task_id]
        
        print(f"Counterexample found, there exists {opt} errors cannot be corrected.\n")
        print('Counterexample Info:\n')
        print(f'rank: {task_id} | id: {ti[0]} | time: {ti[-2]} | result: {ti[-1]}\n')
        print(ti[1])
        print(f'{" | ".join(ti[2])}\n')
        print("About to terminate")
        pool.terminate()
        
    
def process_error(error):
    print(f'error: {error}')

### Pre-processing the tasks ###
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
def cond_checker_detect(matrix, dx, dz, max_proc_num, is_sym = False):
    global task_info
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
    start_gen = time.time()
    # last_print = start_time
    numq = matrix.shape[1] // 2
    ### Manually set the termination condition, determined by the problem size
    ta = 4
    tb = 3
    choice = [6, 4, 0, 0, 4.8, 4, 5.15, 5, 0, 5]
    if dx >= 17:
        ta = choice[dx - 17]
    if 17 <= dx <= 23: 
        tb = 3
    elif dx == 24 or dx == 26:
        tb = 4
    value = (ta, tb)
    ## Generate tasks w.r.t supposed distances ##
    tg_x = subtask_generator(dz, numq, value, max_proc_num)
    tasks_x = tg_x() 
    tg_z = subtask_generator(dx, numq, value, max_proc_num)
    tasks_z = tg_z() 
    total_job = len(tasks_x) + len(tasks_z)
    print(f"Check condition: dx = {dx}, dz = {dz}")
    print(f"tasks for X error: {len(tasks_z)} | tasks for Z error: {len(tasks_x)}")
    print(f"total_job: {total_job}")
    
    print("Task generated. Start checking.")
    ## Generate the verification condition ##
    packed_x, packed_z = cond_generator(matrix, dx, dz, False, is_sym)
    end_gen = time.time()
    print(f"verification condition generation time for dt = {dx}: {end_gen - start_gen:.3f} sec")
    print(f"-----------------")
    start_time = time.time()
    last_print = start_time
    task_info = []
    err_info = []
    ## Start checking ##
    with Pool(processes = max_proc_num) as pool1:
        result_objects = []
        for i, task in enumerate(tasks_x):
            opt = 'x'    
            task_info.append(analysis_task(i, task))
            result_objects.append(pool1.apply_async(worker, (i, task, opt), 
                                                callback= lambda result: process_callback(result, pool1), 
                                                error_callback=process_error))
        pool1.close()
        pool1.join()
    endt_z = time.time()

    if is_sat == 0: 
        print("No counterexample for Z error is found, all errors can be detected.\n")
        # print(f"-----------------")
    else:
        
        print(f"Time to detect a Z-type error: {endt_z - end_gen:.3f} sec")
        print("------------------")
    is_sat = 0
    

    with Pool(processes = max_proc_num) as pool2:
        result_objects = []
        for i, task in enumerate(tasks_z):
            opt = 'z'
            task_info.append(analysis_task(i + len(tasks_x), task))
            result_objects.append(pool2.apply_async(worker, (i + len(tasks_x), task, opt), 
                                                callback=lambda result: process_callback(result, pool2), 
                                                error_callback=process_error))
        pool2.close()
        pool2.join()

    endt_x = time.time()
   
    
    if is_sat == 0: 
        print("No counterexample for X error is found, all errors can be detected.\n")
        # print(f"-----------------")
    else:
        print(f"Time to detect an X-type error: {endt_x - endt_z:.3f} sec")
        # print(f"-----------------")
        
        
    print(f"All tasks finished, total time for verification: {endt_x - start_time:.3f} sec")
    
    for i, ei in enumerate(err_info):   
        ei.re_raise()
    
    print(f"cond_checker_detect took {endt_x - start_gen:.3f} sec")
    
### Checker for surface code ###
def sur_cond_checker_detect(distance, max_proc_num):
    matrix = surface_matrix_gen(distance)
    if distance > 23:
        print("Exceed the limit for verifying correctness.")
    else:
        print("Verifying the correctness when dt = d")
        cond_checker_detect(matrix, distance, distance, max_proc_num, is_sym = True)
        
    ## Detect abnormal cases 
    print("-------------")
    print("Detecting counterexamples when dt = d + 1")
    cond_checker_detect(matrix, distance + 1, distance + 1, max_proc_num, is_sym = True)
    print(f"----------------------")

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
    classical734 = np.array([[1, 1, 0, 1, 0, 0, 0],
                        [0, 1, 1 ,0, 1, 0, 0],
                        [0, 0, 1, 1, 0, 1, 0],
                        [0, 0, 0, 1, 1, 0, 1],
                        [1, 0, 0, 0, 1, 1, 0],
                        [0, 1, 0, 0, 0, 1, 1],
                        [1, 0, 1, 0, 0, 0, 1]], dtype = int)
    matrix = qldpc_codes.stabs_Tanner(1, 1, Ham743, Ham733)
    
    n = matrix.shape[1] // 2
    k = matrix.shape[0] - n
  
    

    #### Parsing input parameters ####
    parser = argparse.ArgumentParser(description='Error detection for quantum codes')
    parser.add_argument('--cpucount', type = int, default = 16, help = 'The number of CPU cores')
    parser.add_argument('--code', type = str, default = 'camp_howard', help = 'The code type')
    parser.add_argument('--p1', type = int, default = 2, help = 'The parameter for the code')
    parser.add_argument('--p2', type = int, default = 2, help = 'The parameter for the code')
    args = parser.parse_args()
    user_input = args.code
    max_proc_num = args.cpucount
    
    ### Set the default output directory ###
    output_dir = './eval-Output'
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    file_name = f'{output_dir}/detection_{user_input}'
    
    if user_input == 'surface':
        if args.p1 is None:
            raise ValueError("The parameters are not provided.")
        d = args.p1
        
        file_name += f"_{d}.txt"
        with open(file_name, 'w') as f:
            with redirect_stdout(f):
                
                sur_cond_checker_detect(d, max_proc_num)
    

    if user_input == 'camp_howard':
       
        if args.p1 is None and args.p2 is None:
            raise ValueError("The parameters are not provided.")
        k = args.p1 if args.p1 is not None else args.p2
            
        file_name += f"_{k}.txt"
        matrix = special_codes.stabs_camp_howard(k)
        with open(file_name, 'w') as f:
            with redirect_stdout(f):
                cond_checker_detect(matrix, 4, 2, max_proc_num)
       
        
    elif user_input == 'triorthogonal':
      
        if args.p1 is None or args.p2 is None:
            raise ValueError("The parameters are not provided.")
        k = args.p1 
        
        dx = args.p2
        matrix = special_codes.stabs_triotho(k)
        file_name += f"_{k}_{dx}_2.txt"
        with open(file_name, 'w') as f:
            with redirect_stdout(f):
                cond_checker_detect(matrix, dx, 2, max_proc_num)
  
        
    elif user_input == 'basic_color':
        # m = int(input("Enter the params: "))
        matrix = special_codes.stabs_832code()
        if args.p1 is None or args.p2 is None:
            raise ValueError("The parameters are not provided.")
        dx,dz = args.p1, args.p2
        
        file_name += f"_{dx}_{dz}.txt"
        with open(file_name, 'w') as f:
            with redirect_stdout(f):
                cond_checker_detect(matrix, dx, dz, max_proc_num)
        # cond_checker_detect(matrix, dx, dz, max_proc_num)
    elif user_input == 'carbon':
        
        matrix = special_codes.stabs_carbon()
        # print("Check condition: dx = 4, dz = 4")
        file_name += ".txt"
        with open(file_name, 'w') as f:
            with redirect_stdout(f):
                cond_checker_detect(matrix, 4, 4, max_proc_num)
        # cond_checker_detect(matrix, 4, 4, max_proc_num)
    elif user_input == 'hyp_prod':
        # if isinstance(args.p1, 'numpy.ndarray'):
        #     if isinstance(args.p2, 'numpy.ndarray'):
        #         matrix = qldpc_codes.stabs_hyp_prod(args.p1, args.p2)
        #     else:
        #         matrix = qldpc_codes.stabs_hyp_prod(args.p1, args.p1)
        # else:
        print("verify with default case")
        matrix = qldpc_codes.stabs_hyp_prod(classical734, classical734)
        
        file_name += ".txt"     
        # with open(file_name, 'w') as f:
        #     with redirect_stdout(f):
        #         cond_checker_detect(matrix, 4, 4, max_proc_num)
        cond_checker_detect(matrix, 4, 4, max_proc_num)