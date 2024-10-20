import time
import math
from multiprocessing import Pool
from surface_code_partition import cond_generator, sur_seq_cond_checker
from timebudget import timebudget
from parallel_dfs import *

def worker(task_id, info, err_vals):
    # print(err_vals)
    cond_x, cond_z, bit_width = info
    start = time.time()
    res = sur_seq_cond_checker(cond_x, cond_z, bit_width, err_vals)
    end = time.time()
    cost = end - start 
    # print(res, end - start, err_vals)
    return task_id, cost
    # if str(res) == 'unsat':
    #     return end - start, err_vals
    # # return end - start, res
    # else:
    #     return end - start


@timebudget
def sur_cond_checker(distance, numq, max_proc_num):
    global task_info
    info = cond_generator(distance)
    tg = subtask_generator(distance, numq, max_proc_num)
    tasks = tg()
    #//linxi debug
    # cnt = 0
    # for t in tasks:
    #     cnt += 1
    #     print(f'task-{cnt}: {t}')
    # exit(0)
    # worker(distance, tasks[0])
    # exit(0)
    #//linxi debug
    with Pool(processes = max_proc_num) as pool:
        result_objects = []
        for i, task in enumerate(tasks):

            task_info.append(analysis_task(i, task))
            # result_objects.append(pool.apply_async(worker, (i, distance, task,), 
            #                                        callback=process_callback,
            #                                        error_callback=process_error))
            result_objects.append(pool.apply_async(worker, (i, info, task,), 
                                                   callback=process_callback,
                                                   error_callback=process_error)) 
        pool.close()
        [res.wait() for res in result_objects]
        pool.join()
        
        # for task in tasks:
        #     # res = pool.apply_async(worker, (distance, task,))
        #     res = pool.apply_async(worker, (distance, task,), callback=process_callback)
        #     # print(res.get())
        # pool.close()
        # pool.join()

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


if __name__ == "__main__":
    D = 9
    max_proc_num = 256
    sur_cond_checker(D, D**2,  max_proc_num)
