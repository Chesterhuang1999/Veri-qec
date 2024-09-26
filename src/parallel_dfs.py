import time
import math
from multiprocessing import Pool
from timebudget import timebudget


def estimate_difficulty(remained_qubits, remained_ones):
    n = remained_qubits
    k = remained_ones
    # k = min(remained_ones, remained_qubits - remained_ones)
    if k >= n:
        return 2 ** n
    k = min(k, n - k)
    # SUM C(n, i) for i \in [0, k]
    return sum(math.comb(n, i) for i in range(k + 1))

class subtask_generator:
    def __init__(self, distance, num_qubits, max_proc_num) -> None:
        self.distance = distance
        self.max_proc_num = max_proc_num
        
        self.num_qubits = num_qubits
        self.tasks = []
        
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
        assigned_bit_num = self.num_qubits - remained_qubit_num
        
        # if assigned_one_num < 2:
        #     return False
        
        if 2 * assigned_one_num * self.distance + assigned_bit_num < self.num_qubits:
            return False
        
        # if self.num_qubits - remained_qubit_num < self.assigned_bit_thres:
        #     return False
        
        # if self.num_qubits < 2 * remained_qubit_num:
        #     return False
        
        # assigned bits, assigned ones, remained bits, remained ones
        # f(a, b, c, d) = 
        
        # if estimate_difficulty(remained_qubit_num, remained_one_num) > self.parti_diffi_thres:
        #     return False
        
        return True
        # return False
    
    def generate_tasks(self, remained_qubit_num, remained_one_num, curr_enum_qubits: list):
        # if remained_qubit_num == 0 \
        #    or estimate_difficulty(remained_qubit_num, remained_one_num) <= self.parti_diffi_thres:
        # if estimate_difficulty(remained_qubit_num, remained_one_num) <= self.parti_diffi_thres:
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

task_info = []

def process_callback(result):
    # print(result)
    global task_info
    task_id, time_cost = result
    task_info[task_id].append(time_cost)

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
