import time
import math
from multiprocessing import Pool, Process, cpu_count
from surface_code_partition import seq_cond_checker
from itertools import combinations
from timebudget import timebudget


def worker(distance, err_vals):
    # print(err_vals)
    start = time.time()
    res = seq_cond_checker(distance, err_vals)
    end = time.time()
    # print(res, end - start, err_vals)
    return res, end - start, err_vals
    # if str(res) == 'unsat':
    #     return end - start, err_vals
    # # return end - start, res
    # else:
    #     return end - start

def estimate_difficulty(remained_qubits, remained_ones):
    n = remained_qubits
    k = remained_onesß
    # k = min(remained_ones, remained_qubits - remained_ones)
    if k >= n:
        return 2 ** n
    k = min(k, n - k)
    return sum(math.comb(n, i) for i in range(k + 1))

class subtask_generator:
    def __init__(self, distance, max_proc_num) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        
        self.num_qubits = distance ** 2
        
        self.full_difficulty = estimate_difficulty(self.num_qubits, distance - 1)
        self.target_task_num =  max_proc_num * 2
        self.parti_diffi_thres = self.full_difficulty // self.target_task_num
        
        self.tasks = []

    
    def generate_tasks(self, remained_qubit_num, remained_one_num, curr_enum_qubits: list):
        # if remained_qubit_num == 0 \
        #    or estimate_difficulty(remained_qubit_num, remained_one_num) <= self.parti_diffi_thres:
        if estimate_difficulty(remained_qubit_num, remained_one_num) <= self.parti_diffi_thres:
            self.tasks.append(list(curr_enum_qubits))
            return

        curr_enum_qubits.append(0)
        self.generate_tasks(remained_qubit_num - 1, remained_one_num, curr_enum_qubits)
        curr_enum_qubits.pop()
        
        curr_enum_qubits.append(1)
        self.generate_tasks(remained_qubit_num - 1, remained_one_num - 1, curr_enum_qubits)
        curr_enum_qubits.pop()
    
    def __call__(self):
        self.generate_tasks(self.num_qubits, self.distance - 1, [])
        return self.tasks

# def process_callback(result):
#     print(result)
#     pass

@timebudget
def sur_cond_checker(distance, max_proc_num):
    tg = subtask_generator(distance, max_proc_num)
    tasks = tg()
    
    #//linxi debug
    # cnt = 0
    # for t in tasks:
    #     cnt += 1
    #     print(f'task-{cnt}: {t}')
    # exit(0)
    # worker(distance, tasks[0])
    #//linxi debug
    
    with Pool(processes = max_proc_num) as pool:
        for task in tasks:
            res = pool.apply_async(worker, (distance, task,))
            # res = pool.apply_async(worker, (distance, task,), callback=process_callback)
            # print(res.get())
        pool.close()
        pool.join()
        # res = pool.map(worker, tasks)
        # print(res)

if __name__ == "__main__":
    distance = 7
    max_proc_num = 30
    sur_cond_checker(distance, max_proc_num)