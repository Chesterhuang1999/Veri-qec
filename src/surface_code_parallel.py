import sys
import time
import random
import subprocess
from multiprocessing import Pool, Process, cpu_count
from surface_code_partition import seq_cond_checker
from itertools import combinations
from timebudget import timebudget


def worker(args):
    start = time.time()
    distance, enum_qubit, pos = args
    err_vals = [0 for _ in range(enum_qubit)]
    for j in pos:
        err_vals[j] = 1
    res = seq_cond_checker(distance, err_vals)
    end = time.time()
    if str(res) == 'unsat':
        return end - start, pos
    # return end - start, res
    else:
        return end - start

@timebudget
def run_cond_check_main(distance, enum_qubit):
    err_vals = [0 for _ in range(enum_qubit)]
    seq_cond_checker(distance, err_vals)

@timebudget
def sur_cond_checker(distance, enum_qubit, max_proc_num):
    num_qubits = distance ** 2
    if enum_qubit > num_qubits:
        enum_qubit = num_qubits

 

    tasks = []
    for one_num in range(1, min(distance, enum_qubit + 1)):
        for pos in combinations(range(enum_qubit), one_num):
            tasks.append((distance, enum_qubit, pos))
    
    with Pool(processes = max_proc_num) as pool:
        cnt = 0
        # rng = random.Random(0)
        # random.shuffle(tasks, rng.random)
        for task in tasks:
            res = pool.apply_async(worker, (task,))
            cnt += 1
            # print(res.get())
        pool.close()
        pool.join()
        # res = pool.map(worker, tasks)
        # print(res)

    main_proc = Process(target=run_cond_check_main, args=(distance, enum_qubit))
    main_proc.start()

    main_proc.join()


if __name__ == "__main__":
    distance = 7
    enum_qubit = 10
    max_proc_num = 16
    sur_cond_checker(distance, enum_qubit, max_proc_num)