import time
import numpy as np
import math
from multiprocessing import Pool
from smt_partition_merge import *
# from smt_detect_only import *

from timebudget import timebudget
import datetime
import tblib.pickling_support
import sys

##Import special codes
from Dataset import special_codes
from Dataset import qldpc_codes

sys.setrecursionlimit(1000000)
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()
    
    def re_raise(self):
        raise self.ee.with_traceback(self.tb)


def worker(task_id, err_vals, info, opt):
    
    try:
        start = time.time()
        
        if opt == 'x':
            # smttime, res = seq_cond_checker(packed_x, err_vals, opt)
            smttime, res = seq_cond_checker_user(packed_x, err_vals, info, opt)
        else:
            # smttime, res = seq_cond_checker(packed_z, err_vals, opt)
            smttime, res = seq_cond_checker_user(packed_z, err_vals, info, opt)
        end = time.time()
        cost = end - start 

        return task_id, smttime, str(res)
    except Exception as e:
        print(e)
        return task_id, ExceptionWrapper(e)


def estimate_difficulty(remained_qubits, remained_ones):
    n = remained_qubits
    k = remained_ones
    # k = min(remained_ones, remained_qubits - remained_ones)
    if k >= n:
        return 2 ** n
    k = min(k, n - k)
    
    return sum(math.comb(n, i) for i in range(k + 1))

class subtask_generator:
    def __init__(self, distance, numq, max_proc_num, method) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        self.method = method
        # self.num_qubits = distance ** 2
        self.num_qubits = numq
        self.tasks = []
        self.nonzero_len = (self.distance**2 - 1) // 2
        # self.one_num_thres = distance // 2
        self.assigned_bit_thres = 16
        
        self.target_task_num =  max_proc_num * 2
        self.full_difficulty = estimate_difficulty(self.num_qubits, distance - 1)
        self.parti_diffi_thres = self.full_difficulty // self.target_task_num

    def easy_enough(self, remained_qubit_num, remained_one_num):
        if remained_qubit_num == 1:
            return True
        # if self.one_num_thres >= remained_one_num and \
        #     estimate_difficulty(remained_qubit_num, remained_one_num) <= self.parti_diffi_thres:
        #     return True
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.nonzero_len - remained_qubit_num
        
        # if assigned_one_num < 2:
        #     return False

        ### For detection task ###

        # if assigned_one_num * self.distance + 2 * assigned_bit_num < self.num_qubits:
        #     return False

        ### For verification task ###
        if  int(4 * assigned_one_num * self.distance // 3)  + assigned_bit_num  < self.nonzero_len:
            return False
        ### For condition II ###
        # if assigned_one_num * self.distance + assigned_bit_num // 2 < self.num_qubits: 
        #     return False
        return True
        # return False
    ### Constraint II: The errors come from a restricted set (maybe the whole set)
    def generate_tasks_II(self, remained_qubit_num, remained_one_num, curr_enum_qubits: list):
        # if remained_qubit_num == 0 \
        #    or estimate_difficulty(remained_qubit_num, remained_one_num) <= self.parti_diffi_thres:
        # if estimate_difficulty(remained_qubit_num, remained_one_num) <= self.parti_diffi_thres:
        if self.easy_enough(remained_qubit_num, remained_one_num):
            self.tasks.append(list(curr_enum_qubits))
            return

        curr_enum_qubits.append(0)
        # curr_seg_qubits.append(0)
        self.generate_tasks_II(remained_qubit_num - 1, remained_one_num, curr_enum_qubits)
        curr_enum_qubits.pop()
        
        if remained_one_num > 0 :
            curr_enum_qubits.append(1)
            # curr_seg_qubits.append(0)
            self.generate_tasks_II(remained_qubit_num - 1, remained_one_num - 1, curr_enum_qubits)
            curr_enum_qubits.pop()

    ### Constraint I: The number of 1s in each length d segment is at most 1
    def generate_tasks_I(self, remained_qubit_num, remained_one_num, curr_seg_count, curr_enum_qubits: list):
        
        if self.easy_enough(remained_qubit_num, remained_one_num):
            self.tasks.append(list(curr_enum_qubits))
            return
        
        if remained_qubit_num % self.distance == 0:
            curr_seg_count = 0

        curr_enum_qubits.append(0)
        # curr_seg_qubits.append(0)
        self.generate_tasks_I(remained_qubit_num - 1, remained_one_num, curr_seg_count, curr_enum_qubits)
        curr_enum_qubits.pop()
        
        if remained_one_num > 0 and curr_seg_count < 1:
            curr_enum_qubits.append(1)
            # curr_seg_qubits.append(0)
            self.generate_tasks_I(remained_qubit_num - 1, remained_one_num - 1, curr_seg_count + 1, curr_enum_qubits)
            curr_enum_qubits.pop()

    def __call__(self):
        if self.method == 'II':
            err_len = (self.distance**2 - 1) // 2
            begin = np.random.randint(0, int(self.num_qubits // 4))
            support_len = int(3 * self.num_qubits // 4)
            support_range = np.arange(begin, begin + support_len)
            err_set = np.sort(np.random.choice(support_range, err_len, replace = False))
            # err_set = np.sort(np.random.choice(self.num_qubits, err_len, replace = False))
            # begin = np.random.randint(0, self.num_qubits - self.nonzero_len)
            free_set = [i for i in range(self.num_qubits) if i not in err_set]
            self.generate_tasks_I(self.nonzero_len, self.distance - 1, 0, [])
            return self.tasks, (err_set, free_set)
        elif self.method == 'I':
            self.generate_tasks_I(self.num_qubits, self.distance - 1, 0, [])
            return self.tasks

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
    
    task_id, time_cost, res_smt = result
    task_info[task_id].append(time_cost)
    task_info[task_id].append(res_smt)
    
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
def cond_checker(matrix, dx, dz, max_proc_num, is_sym = False):
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
    # global is_counter
    # is_counter = 0
    max_process_num = max_proc_num
    start_time = time.time()
    last_print = start_time
    numq = matrix.shape[1] // 2
    
    tg_x = subtask_generator(dz, numq, max_proc_num, 'II')
    tasks_x, info_x = tg_x()
    tg_z = subtask_generator(dx, numq, max_proc_num, 'II')
    tasks_z, info_z = tg_z()
    print("Task generated. Start checking.")
    # print(info_x, info_z)
    total_job = len(tasks_x) + len(tasks_z)
    print(f"total_job: {total_job}")
    packed_x, packed_z = cond_generator(matrix, dx, dz, info_x, info_z, is_sym)
    end_gen = time.time()
    print(f"cond generation time: {end_gen - start_time}")
    # exit(0)
    task_info = []
    err_info = []
    
    with Pool(processes = max_proc_num) as pool:
        result_objects = []
        for i, task in enumerate(tasks_x):
            opt = 'x'    
            task_info.append(analysis_task(i, task))
            result_objects.append(pool.apply_async(worker, (i, task, info_z, opt), callback=process_callback, error_callback=process_error))
            # if (i % 50 == 0):
                #print(i, task)
        for i, task in enumerate(tasks_z):
            opt = 'z'
            task_info.append(analysis_task(i + len(tasks_x), task))
            result_objects.append(pool.apply_async(worker, (i + len(tasks_x), task, info_x, opt), callback=process_callback, error_callback=process_error))
        pool.close()
        [res.wait() for res in result_objects]
        pool.join()
    
    for i, ei in enumerate(err_info):
        ei.re_raise()

    # with open('unsorted_results.txt', 'w') as f:
    #     for i, ti in enumerate(task_info):
    #         f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-2]}| result: {ti[-1]}\n')
    #         f.write(f'{ti[1]}\n')
    #         f.write(f'{" | ".join(ti[2])}\n')
    # # for info in task_info:
    # #     print(info)
    # task_info.sort(key=lambda x: x[0])

    with open('sorted_results.txt', 'w') as f:
        for i, ti in enumerate(task_info):
            f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-2]} | result: {ti[-1]}\n')
            f.write(f'{ti[1]}\n')
            f.write(f'{" | ".join(ti[2])}\n')
            # 
    print("Finish all jobs. Checking time:", time.time() - end_gen)



def sur_cond_checker(distance, max_proc_num):
    matrix = surface_matrix_gen(distance)
    cond_checker(matrix, distance, distance, max_proc_num, is_sym = True)

if __name__ == "__main__":
    tblib.pickling_support.install()
    # dx = 3
    # dz = 3
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

    # code_to_func = {
    #     'surface': (surface_matrix_gen, 1),
    #     'steane': (special_codes.stabs_steane, 0),
    #     'reed_muller': (special_codes.stabs_Reed_Muller, 1),
    #     'dodecacode': (special_codes.stabs_1115, 0),
    #     'XZZX': (special_codes.stabs_XZZX, 2)
    # }
    # user_input = input("Enter the code type: ")
    # if user_input == 'surface':
    #     d = int(input("Enter the distance: "))
    #         # matrix = surface_matrix_gen(d)
    #     sur_cond_checker(d, max_proc_num)
    # elif user_input == 'steane':
    #     matrix = special_codes.stabs_steane()
    #     cond_checker(matrix, 3, 3, max_proc_num)
    # elif user_input == 'reed_muller':
    #     m = int(input("Enter the params: "))
    #     matrix = special_codes.stabs_Reed_Muller(m)
    #     cond_checker(matrix, 3, 3, max_proc_num)
    # elif user_input == 'dodecacode':
    #     matrix = special_codes.stabs_1115()
    #     cond_checker(matrix, 5, 5, max_proc_num)
    # elif user_input == 'XZZX':
    #     dx = int(input("Enter the dx: "))
    #     dz = int(input("Enter the dz: "))
    #     matrix = special_codes.stabs_XZZX(dx, dz)
    #     cond_checker(matrix, 5, 5, max_proc_num)
    # elif user_input == 'Honeycomb':
    #     d = int(input("Enter the distance: "))
    #     matrix = special_codes.stabs_honeycomb(d)
    #     cond_checker(matrix, d, d, max_proc_num)
    # dx_max = min([np.count_nonzero(matrix[n - k + i]) for i in range(k)]) 
    # dz_max = min([np.count_nonzero(matrix[n + i]) for i in range(k)])
    # print(dx_max, dz_max)
    # weight_min = min([np.count_nonzero(matrix[i]) for i in range(n - k)])
    # matrix = surface_matrix_gen(3)
    
    # print(matrix)
    sur_cond_checker(17, max_proc_num)
    # matrix = special_codes.stabs_steane()
    # cond_checker(matrix, 3, 3, max_proc_num)

