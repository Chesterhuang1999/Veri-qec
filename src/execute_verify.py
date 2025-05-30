#----------#
# Developer: Chester Huang
# Date: 2024/11/05
# Description: Parallel execution for accurate correction property
#----------#


import time
import numpy as np
import math
from multiprocessing import Pool
import os
from contextlib import redirect_stdout
from smt_partition_merge import *

import argparse
from timebudget import timebudget
import datetime
import tblib.pickling_support
import sys

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
            smttime, res = seq_cond_checker(packed_x, err_vals, opt)
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
    def __init__(self, distance, numq, max_proc_num, checktype) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        self.checktype = checktype
        
        self.num_qubits = numq
        self.tasks = []
        
        
    ### Judging terminate or not ###
    def easy_enough(self, remained_qubit_num, remained_one_num, checktype):
        if remained_qubit_num == 1:
            return True
      
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num
        

        ### Termination condition for verification task ###
        if checktype == 'z':
            if 2 * assigned_one_num * self.distance  + assigned_bit_num < self.num_qubits :
                return False
        else:
            if 2 * assigned_one_num * self.distance  + assigned_bit_num < self.num_qubits :
                return False
        
        return True
        
    ### Recursively enumerate the variables ###
    def generate_tasks(self, checktype, remained_qubit_num, remained_one_num, curr_enum_qubits: list):
        
        if self.easy_enough(remained_qubit_num, remained_one_num, checktype):
            self.tasks.append(list(curr_enum_qubits))
            return

        curr_enum_qubits.append(0)
        self.generate_tasks(checktype, remained_qubit_num - 1, remained_one_num, curr_enum_qubits)
        curr_enum_qubits.pop()
        
        if remained_one_num > 0 :
            curr_enum_qubits.append(1)
            self.generate_tasks(checktype, remained_qubit_num - 1, remained_one_num - 1, curr_enum_qubits)
            curr_enum_qubits.pop()

    def __call__(self):
       
        self.generate_tasks(self.checktype, self.num_qubits, self.distance - 1, []) 
        return self.tasks

processed_job = 0
solved_job = 0
unsolved_job = 0
sat_job = 0
unsat_job = 0

### Print current Progress ###
def get_current_infos(not_done = True):
    ## Get current time, time already costs, and estimated finish time. 
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
def process_callback(result, pool):
    
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
    ## Find counterexample, terminate the process 
    if res_smt == 'sat':
        is_sat = 1
        
        ti = task_info[task_id]
        print("Counter example found, there exists errors cannot be corrected.\n")
        print('Counterexample Info:\n')
        print(f'rank: {task_id} | id: {ti[0]} | time: {ti[-2]} | result: {ti[-1]}\n')
        print(ti[1])
        print(f'{" | ".join(ti[2])}\n')
        print("About to terminate")
        
        pool.terminate()


    curr_time = time.time()
    processed_job += 1
    if curr_time - last_print > 300:
        info = "{}/{}: finish job file[{}], cost_time: {}" \
                .format(processed_job, total_job, task_id, time_cost)
        print(info)
        print(task_info[task_id])
        print(get_current_infos())
        sys.stdout.flush()
        last_print = curr_time
    
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

def cond_checker_verify(matrix, dx, dz, max_proc_num, is_sym = False):
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
    start_time = time.time()
    last_print = start_time
    numq = matrix.shape[1] // 2
    ## Generate the verification condition ##
    packed_x, packed_z = cond_generator(matrix, dx, dz, False, is_sym)
    ## Generate tasks w.r.t supposed distances ##
    tg_x = subtask_generator(dz, numq, max_proc_num, 'z')
    tasks_x = tg_x()
    tg_z = subtask_generator(dx, numq, max_proc_num, 'x')
    tasks_z = tg_z()
    
    print("Task generated. Start checking.")
    total_job = len(tasks_x) + len(tasks_z)
    end_gen = time.time()
    print(f"total_job: {total_job}")

    print(f"tasks for X error: {len(tasks_z)} | tasks for Z error: {len(tasks_x)}") 
    print(f"verification condition generation time: {end_gen - start_time:.3f} sec")
    print(f"-----------------")
    task_info = []
    err_info = []
    ## Start checking ##
    with Pool(processes = max_proc_num) as pool:
        result_objects = []
        for i, task in enumerate(tasks_x):
            opt = 'x'    
            task_info.append(analysis_task(i, task))
            result_objects.append(pool.apply_async(worker, (i, task, opt), 
                                                   callback= lambda result: process_callback(result, pool), 
                                                   error_callback=process_error))
        for i, task in enumerate(tasks_z):
            opt = 'z'
            task_info.append(analysis_task(i + len(tasks_x), task))
            result_objects.append(pool.apply_async(worker, (i + len(tasks_x), task, opt), 
                                                   callback=lambda result: process_callback(result, pool), 
                                                   error_callback=process_error))
        pool.close()
        [res.wait() for res in result_objects]
        pool.join()
    ## Deal with possible error info (for debugging) ##
    for i, ei in enumerate(err_info):
        ei.re_raise()

    if is_sat == 0: 
        print("No counterexample found, all errors can be corrected.\n")
    
    end_verify = time.time()
    print(f"All tasks finished, total time for verification: {end_verify - end_gen:.3f} sec")

    print(f"cond_checker_verify took {end_verify - start_time:.3f} sec")
   

### Checker for surface code ### 
def sur_cond_checker_verify(distance, max_proc_num):
    matrix = surface_matrix_gen(distance)
    cond_checker_verify(matrix, distance, distance, max_proc_num, is_sym = True)

if __name__ == "__main__":
    tblib.pickling_support.install()
    
    Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                   [1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
    Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])
    classical734 = np.array([[1, 1, 0, 1, 0, 0, 0],
                        [0, 1, 1 ,0, 1, 0, 0],
                        [0, 0, 1, 1, 0, 1, 0],
                        [0, 0, 0, 1, 1, 0, 1],
                        [1, 0, 0, 0, 1, 1, 0],
                        [0, 1, 0, 0, 0, 1, 1],
                        [1, 0, 1, 0, 0, 0, 1]], dtype = int)
   
    ## Parsing input parameters ##
    parser = argparse.ArgumentParser(description="Process some parameters.")
    parser.add_argument('--cpucount', type=int, default=8, help='The CPU counts.')
    parser.add_argument('--code', type=str, default='surface', help='The code type.')
    parser.add_argument('--param1', type=int, default = 3, help='Additional parameters of the code.')
    parser.add_argument('--param2', type=int, help='Additional parameters of the code.')

    args = parser.parse_args()
    max_proc_num = args.cpucount
    user_input = args.code
    ## Redirect output to another directory ##
    output_dir = "./eval-Output"
    os.makedirs(output_dir, exist_ok=True)
    file_name = f"correction_{user_input}"
    
    if user_input == 'surface':
        ## surface code, basic candidate for experiments ## 
        if args.param1 is None:
            raise ValueError("Please enter the distance.") 
        d = args.param1
        file_name += f"_{d}.txt"
    
        with open(os.path.join(output_dir, file_name), 'w') as f:
            with redirect_stdout(f):
                sur_cond_checker_verify(d, max_proc_num)
            
    elif user_input == 'steane':
        matrix = special_codes.stabs_steane()
        file_name += f".txt"
        with open(os.path.join(output_dir, file_name), 'w') as f:
            with redirect_stdout(f):
                cond_checker_verify(matrix, 3, 3, max_proc_num)
        
    elif user_input == 'reed_muller':
       # Quantum reed-muller code  
        if args.param1 is None and args.param2 is None:
            raise ValueError("Please enter parameters.")
        m = args.param1 if args.param1 is not None else args.param2
        matrix = special_codes.stabs_Reed_Muller(m)
        file_name += f"_{m}.txt"
        with open(os.path.join(output_dir, file_name), 'w') as f:
            with redirect_stdout(f):  
                cond_checker_verify(matrix, 3, 3, max_proc_num)
      
        
    elif user_input == 'dodecacode':
        matrix = special_codes.stabs_1115()
        file_name += f"_5.txt"
        with open(os.path.join(output_dir, file_name), 'w') as f:
            with redirect_stdout(f):
                cond_checker_verify(matrix, 5, 5, max_proc_num)
        
    elif user_input == 'XZZX':
        ## XZZX code, a variant of surface code ## 
        if args.param1 is None or args.param2 is None:
            raise ValueError("Both distances should be provided.")
        ## Enter the distances of X and Z ##
        dx = args.param1
        dz = args.param2
        matrix = special_codes.stabs_XZZX(dx, dz)
        file_name += f"_{dx}_{dz}.txt"
        with open(os.path.join(output_dir, file_name), 'w') as f:
            with redirect_stdout(f):
                cond_checker_verify(matrix, dx, dz, max_proc_num, is_sym = True)
        
    elif user_input == 'Honeycomb':
        ## Honeycomb code, consists of hexagon regions ##
        # Only support d = 3, d = 5 currently
        if args.param1 is None and args.param2 is None:
            raise ValueError("Both distances should be provided.")
        d = args.param1 if args.param1 is not None else args.param2
        assert d <= 5, "Only support d = 3, d = 5 currently."
        
        matrix = special_codes.stabs_honeycomb(d)
        file_name += f"_{d}.txt"
        with open(os.path.join(output_dir, file_name), 'w') as f:
            with redirect_stdout(f):
                cond_checker_verify(matrix, d, d, max_proc_num)
        

    elif user_input == 'Gottesman':
        ##[[2^r, 2^r-r-2, 3]] Gottesman code
        if args.param1 is None and args.param2 is None:
            raise ValueError("Shape parameter should be provided.")
        m = args.param1 if args.param1 is not None else args.param2
        matrix = special_codes.stabs_gottesman(m)
        file_name += f"_{m}.txt" 
        with open(os.path.join(output_dir, file_name), 'w') as f:
            with redirect_stdout(f):
                cond_checker_verify(matrix, 3, 3, max_proc_num)

    elif user_input == 'BB':
        ## Verify Bivariate bicycle code, from quantum LDPC code famly ##
        ## Due to the scale of the code, verification may take a long time ##
        if args.param1 is None or args.param2 is None:
            raise ValueError("Shape parameter should be provided.")
        mat1, mat2 = qldpc_codes.bivariate_bicycle(args.param1, args.param2)
        
    elif user_input == 'Others': #### User-defined code and properties
        file_path = input("Please enter the file path of the code:")
        dx = input("Enter dx:")
        dz = input("Enter dz:")
        dx,dz = int(dx), int(dz)
        try: 
            matrix = np.loadtxt(file_path, delimiter = ',', dtype = int)
            cond_checker_verify(matrix, dx, dz, max_proc_num)
        except Exception as e:
            print("Error loading the file:", e)
            sys.exit(1)

    
