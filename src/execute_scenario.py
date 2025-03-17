import numpy as np
import datetime
import time
import cvc5

from z3 import *
from multiprocessing import Pool
import tblib.pickling_support
import sys
from timebudget import timebudget

## import customized codes
from Dataset import qldpc_codes, linalg_GF, special_codes
from smt_testing_meas_err import *
from logical_op_test import *
sys.setrecursionlimit(1000000)

## Handling errors
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()

    def re_raise(self):
        raise self.ee.with_traceback(self.tb)    

### Parallel checking ### 
def worker_test(task_id, meas_corr, rnds, err_vals, opt):
    try: 
        start = time.time()
        
        if opt == 'x':
            smttime, res = seq_checker_meas_err(packed_x, meas_corr, rnds, err_vals, opt)
        else:
            smttime, res = seq_checker_meas_err(packed_z, meas_corr, rnds, err_vals, opt)
        pos = np.where(err_vals == 1)[0]
        # print(resx, resz, len(pos), pos)
        # print(pos, res)
        # res = res[1] if res[0] == 'True' else res[0]
        # with open('Details/surface_code_testing_opt-31.txt', 'a') as f:
        #     f.write(f'id: {task_id} | err_counts: {len(pos)} | err_pos: {pos}\n')
        #     f.write(f'error_type: {opt} | result: {res} \n')
        # print(resx, resz)
        end = time.time()
        cost = end - start
    
        return task_id, cost, pos, res
    except Exception as e:
        return task_id, ExceptionWrapper(e)
def worker(task_id, err_vals, opt):
    
    try:
        start = time.time()
        
        if opt == 'x':
            # smttime, res = seq_cond_checker(packed_x, err_vals, opt)
            smttime, res = seq_cond_checker(packed_x, err_vals, opt)
        else:
            # smttime, res = seq_cond_checker(packed_z, err_vals, opt)
            smttime, res = seq_cond_checker(packed_z, err_vals, opt)
        end = time.time()
        cost = end - start 

        return task_id, smttime, str(res)
    except Exception as e:
        print(e)
        return task_id, ExceptionWrapper(e)

class subtask_generator:
    def __init__(self, distance, numq, max_proc_num) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        self.num_qubits = numq
        self.tasks = []

        self.assigned_bit_thres = 16
        
        self.target_task_num =  max_proc_num * 2
        self.full_difficulty = estimate_difficulty(self.num_qubits, distance - 1)
        self.parti_diffi_thres = self.full_difficulty // self.target_task_num

    def easy_enough(self, remained_qubit_num, remained_one_num):
        if remained_qubit_num == 1:
            return True
        
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num

        ### For verification task ###
        if 2 * assigned_one_num * self.distance + assigned_bit_num < self.num_qubits:
            return False

        return True

    def generate_tasks(self, remained_qubit_num, remained_one_num, curr_enum_qubits: list):

        if self.easy_enough(remained_qubit_num, remained_one_num):
            self.tasks.append(list(curr_enum_qubits))
            return

        curr_enum_qubits.append(0)
        self.generate_tasks(remained_qubit_num - 1, remained_one_num, curr_enum_qubits)
        curr_enum_qubits.pop()
        
        if remained_one_num > 0:

            curr_enum_qubits.append(1)
            self.generate_tasks(remained_qubit_num - 1, remained_one_num - 1, curr_enum_qubits)
            curr_enum_qubits.pop()
    
    def __call__(self):
        self.generate_tasks(self.num_qubits, self.distance - 1, [])
        return self.tasks
    
##Random generate samples for testing
def random_sample_test(numq, N, meas_cnt, rnds, D):
    max_ham_weight = (D - 1) // 2
    indices = []
    meas_cnt_single = meas_cnt // ((rnds - 1) * N)
    for i in range(rnds):
        num_ones = np.random.randint(1, max_ham_weight + 1)
        qbase = i * N * numq
        mbase = 0
        if i == 0:
            for cnt in range(N):
                qbase = qbase + cnt * numq 
                place_indice = np.arange(qbase, qbase + numq)
                if len(indices) == 0:
                    indices = np.random.choice(place_indice, num_ones, replace = False)
                else:
                    indices_i = np.random.choice(place_indice, num_ones, replace = False)
                    
                    indices = np.concatenate((indices, indices_i))
        else:
            for cnt in range(N):
                mbase = (N * (i - 1) + cnt) * meas_cnt_single
                qbase = qbase + cnt * numq
                
                place_indice = np.arange(qbase + mbase, qbase + numq + meas_cnt_single)
                indices_i = np.random.choice(place_indice, num_ones, replace = False)
                
                indices = np.concatenate((indices, indices_i))

    return indices

def task_generator_test(numq, N, meas_cnt, rnds, distance, max_sample_num):
    tasks = []
    cnt = 0 
    uniq_samples = set()
    while cnt < max_sample_num:
        sample = random_sample_test(numq, N, meas_cnt, rnds, distance)
        if tuple(sample) not in uniq_samples:
            uniq_samples.add(tuple(sample))
            cnt += 1
            bin_arr = np.zeros(numq * N * rnds + meas_cnt, dtype = int)
            bin_arr[sample] = 1
            tasks.append(bin_arr)
    
    return tasks
            

### periodcally output progress of jobs
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

def cond_checker_testing(matrix, dx, dz, rnds, N, max_sample_num, max_proc_num, circuit):
    global task_info
    global packed_x
    global packed_z
    global total_job
    global start_time
    global max_process_num
    global err_info
    global last_print
    task_info = []
    err_info = []
    max_process_num = max_proc_num
    start_time = time.time()
    last_print = start_time
    numq = matrix.shape[1] // 2
    if rnds > 1:
        for ind, gateinfo in circuit.items():
            prog_log = program_gen_logic(matrix, numq, N, gateinfo, 'surface')
            packed_x, packed_z, meas_corr_x, meas_corr_z = formula_gen_meas_err(matrix, dx, dz, rnds, N, prog_log)

            tasks_x = task_generator_test(numq, N, len(meas_corr_x), rnds, dz, max_sample_num)
            tasks_z = task_generator_test(numq, N, len(meas_corr_z), rnds, dx, max_sample_num)
            print("Task generated. Start checking.")
            print(f"total_job: {len(tasks_x) + len(tasks_z)}")
            total_job = len(tasks_x) + len(tasks_z)

            time_gen = time.time() - start_time
            print(time_gen)
            with Pool(processes = max_proc_num) as pool:
                result_objects = []
                for i, task in enumerate(tasks_x):
                    opt = 'x'
                    task_info.append(analysis_task(i, task))
                    result_objects.append(pool.apply_async(worker_test, (i, meas_corr_x, rnds, task, opt), callback=process_callback, error_callback=process_error))
                
                for i, task in enumerate(tasks_z):
                    xlen = len(tasks_x)
                    task_info.append(analysis_task(i + xlen, task))
                    result_objects.append(pool.apply_async(worker_test, (i + xlen, meas_corr_z, rnds, task, meas_corr_z, rnds, 'z'), callback=process_callback, error_callback=process_error))
                
                pool.close()
                [res.wait() for res in result_objects]
                pool.join()
            
            for i, ei in enumerate(err_info):
                ei.re_raise()
        
            task_info.sort(key=lambda x: x[-1])

            with open('sorted_results.txt', 'w') as f:
                for i, ti in enumerate(task_info):
                    f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-2]} | result: {ti[-1]}\n')
                    f.write(f'{ti[1]}\n')
                    f.write(f'{" | ".join(ti[2])}\n')
        
    else:
        for ind, gateinfo in circuit.items():
            prog_log = program_gen_logic(matrix, numq, N, gateinfo, 'steane')
            print(prog_log)
            packed_x, packed_z = formula_gen_combine(matrix, dx, dz, 1, N, prog_log)
            tgx = subtask_generator(numq * N, dz, max_proc_num)
            tgz = subtask_generator(numq * N, dx, max_proc_num)
            tasks_x = tgx()
            tasks_z = tgz()
            print("Task generated. Start checking.")
            print(f"total_job: {len(tasks_x) + len(tasks_z)}")
            total_job = len(tasks_x) + len(tasks_z)

            time_gen = time.time() - start_time
            print(time_gen)
            packed_x, packed_z = formula_gen_combine(matrix, dx, dz, 1, N, prog_log)
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
        
            task_info.sort(key=lambda x: x[-1])

            with open('sorted_results.txt', 'w') as f:
                for i, ti in enumerate(task_info):
                    f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-2]} | result: {ti[-1]}\n')
                    f.write(f'{ti[1]}\n')
                    f.write(f'{" | ".join(ti[2])}\n')
            
        

    

if __name__ == "__main__":
    # print(random_sample_test(9, 2, 8, 2, 3))
    matrix = special_codes.stabs_steane()
    GHZ = defaultdict(list)
    GHZ[0] = [['H', [2]]]
    GHZ[1] = [['CNOT', [2,1]], ['CNOT', [2, 3]]]
    cond_checker_testing(matrix, 3, 3, 1, 3, 0, 8, GHZ)