## import system-based packages
import numpy as np
import datetime
import time
import cvc5
import math
from z3 import *
from multiprocessing import Pool
import tblib.pickling_support
import sys
from timebudget import timebudget

## import customized codes
from Dataset import qldpc_codes, linalg_GF, special_codes
from smt_testing_code import *
sys.setrecursionlimit(1000000)

## Handling errors
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()

    def re_raise(self):
        raise self.ee.with_traceback(self.tb)    

### Parallel checking ### 
def worker(task_id, err_vals, opt):
    try: 
        start = time.time()
        
        if opt == 'x':
            smttime, res = seq_cond_checker_testing(packed_x, err_vals, opt)
        else:
            smttime, res = seq_cond_checker_testing(packed_z, err_vals, opt)
        pos = np.where(err_vals == 1)[0]
        # print(resx, resz, len(pos), pos)
        # print(pos, res)
        # res = res[1] if res[0] == 'True' else res[0]
        with open('Details/surface_code_testing_opt-9.txt', 'a') as f:
            f.write(f'id: {task_id} | err_counts: {len(pos)} | err_pos: {pos}\n')
            f.write(f'error_type: {opt} | result: {res} \n')
        # print(resx, resz)
        end = time.time()
        cost = end - start

        return task_id, cost
    except Exception as e:
        return task_id, ExceptionWrapper(e)
##Random generate samples for testing
def random_sample(N, D, probs):
    max_ham_weight = D - 1
    elems = np.arange(D - 1) + 1
    
    # num_ones = np.random.randint(1, max_ham_weight + 1)
    num_ones = np.random.choice(elems, 1, p = probs)[0]
    # print(num_ones)
    indices = np.random.choice(N, num_ones, replace = False)
    # bin_arr = np.zeros(length, dtype = int)
    # bin_arr[indices] = 1

    return indices
def random_sample_fixd(N, D):
    
    num_ones = (D - 1) // 2
    indices = np.random.choice(N, num_ones, replace = False)
    return indices
def task_generator(numq, distance, max_sample_num):
    tasks = []
    cnt = 0 
    uniq_samples = set()
    p0 = 1 / (2 - math.pow(1/2, distance - 2))
    probs = [p0]
    for i in range(1, distance - 1):
        probs.append(probs[-1] / 2)
    while cnt < max_sample_num:
        sample = random_sample(numq, distance, probs)
        if tuple(sample) not in uniq_samples:
            uniq_samples.add(tuple(sample))
            cnt += 1
            bin_arr = np.zeros(numq, dtype = int)
            bin_arr[sample] = 1
            tasks.append(bin_arr)
    
    return tasks
            


processed_job = 0
solved_job = 0
unsolved_job = 0
sat_job = 0 
unsat_job = 0

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

    
def process_callback(result):
    # print(result)
    global task_info
    global err_info

    if isinstance(result[1], ExceptionWrapper):
        task_id = result[0]
        print(task_info[task_id])
        err_info.append(result[1])
        return
    global processed_job
    global last_print
    
    task_id, time_cost = result
    
    task_info[task_id].append(time_cost)
    curr_time = time.time()
    processed_job += 1
    if curr_time - last_print > 10.0:
        info = "{}/{}: finish job file[{}], cost_time: {}" \
                .format(processed_job, total_job, task_id, time_cost)
        print(info)
        print(task_info[task_id])
        print(get_current_infos())
        sys.stdout.flush()
        last_print = curr_time
    
def process_error(error):
    print(f'error: {error}')

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

@timebudget
def cond_checker_testing(matrix, dx, dz, max_sample_num, max_proc_num):
    global task_info
    global packed_x
    global packed_z
    global total_job
    global start_time
    global max_process_num
    global err_info
    global last_print
    
    max_process_num = max_proc_num
    start_time = time.time()
    last_print = start_time
    numq = matrix.shape[1] // 2
    
    tasks_x = task_generator(numq, dz, max_sample_num)
    tasks_z = task_generator(numq, dx, max_sample_num)
    # lists = []
    # with open(f'Details/testing_example_9.txt', 'r') as f:
    #     while True:
    #         line1 = f.readline().strip()[1:]
    #         line2 = f.readline().strip()
    #         line3 = f.readline().strip()[:-1]   
    #         if not line1:
    #             break
    #         line = line1 + " " + line2 + " " + line3
    #         bin_arr = np.zeros(numq, dtype = int)
    #         for i, bit in enumerate(line.split()):
    #             bin_arr[i] = int(bit)
    #         # list_elements = [int(element) for element in line.split()]
            
    #         lists.append(bin_arr)
    # # print(lists[0])
    # tasks_x = lists
    # tasks_z = lists
    print("Task generated. Start checking.")
    print(f"total_job: {len(tasks_x) + len(tasks_z)}")
    total_job = len(tasks_x) + len(tasks_z)
    task_info = []
    err_info = []
    packed_x, packed_z = formulagen_testing(matrix, dx, dz)
    time_gen = time.time() - start_time
    print(time_gen)
    with Pool(processes = max_proc_num) as pool:
        result_objects = []
        for i, task in enumerate(tasks_x):
            opt = 'x'
            task_info.append(analysis_task(i, task))

            result_objects.append(pool.apply_async(worker, (i, task, opt), callback=process_callback, error_callback=process_error))
        
        for i, task in enumerate(tasks_z):
            xlen = len(tasks_x)
            task_info.append(analysis_task(i + xlen, task))
            result_objects.append(pool.apply_async(worker, (i + xlen, task, 'z'), callback=process_callback, error_callback=process_error))
        
        pool.close()
        [res.wait() for res in result_objects]
        pool.join()
    
    for i, ei in enumerate(err_info):
        ei.re_raise()

    # with open('unsorted_results.txt', 'w') as f:
    #     for i, ti in enumerate(task_info):
    #         f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-1]}\n')
    #         f.write(f'{ti[1]}\n')
    #         f.write(f'{" | ".join(ti[2])}\n')
   
    task_info.sort(key=lambda x: x[-1])

    with open('sorted_results.txt', 'w') as f:
        for i, ti in enumerate(task_info):
            f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-1]}\n')
            f.write(f'{ti[1]}\n')
            f.write(f'{" | ".join(ti[2])}\n')
   

    
    processed_job = 0
    unprocessed_job = 0


def sur_cond_checker_testing(distance, max_sample_num, max_proc_num):
    matrix = surface_matrix_gen(distance)   
    cond_checker_testing(matrix, distance, distance, max_sample_num, max_proc_num)



if __name__ == "__main__": 
    tblib.pickling_support.install()

    distance = 9
    max_sample_num = 250
    max_proc_num = 250
    Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                   [1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
    Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])
    # Rep51 = np.array([[1, 1, 0, 0, 0],
    #               [1, 0, 1, 0, 0],
    #               [1, 0, 0, 1, 0],
    #               [1, 0, 0, 0, 1]])
    # Par54 = np.array([[1, 1, 1, 1, 1]])
    # Rep31 = np.array([[1, 1, 0],
    #               [1, 0, 1]])
    # Par32 = np.array([[1, 1, 1]])

    matrix = qldpc_codes.stabs_Tanner(1, 1, Ham743, Ham733)
    # matrix = special_codes.stabs_triotho(2)
    # print(matrix)
    n = matrix.shape[1] // 2
    k = matrix.shape[0] - n
    
    dx_max = min([np.count_nonzero(matrix[n - k + i]) for i in range(k)])
    dz_max = min([np.count_nonzero(matrix[n + i]) for i in range(k)])
    print(n, dx_max, dz_max)
    cond_checker_testing(matrix, dx_max, dz_max, max_sample_num, max_proc_num)

    # sur_cond_checker_testing(distance, max_sample_num, max_proc_num)
    # print(task_generator(25, 5, 10))
  
    
    
