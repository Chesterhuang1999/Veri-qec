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

## import customized functions
from Dataset import qldpc_codes, special_codes
from verifier import precond_generator
from encoder import tree_to_z3, VCgeneration
from condition import *

sys.setrecursionlimit(1000000)

## Handling errors
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()

    def re_raise(self):
        raise self.ee.with_traceback(self.tb)    



def smtencoding_testing(precond, program, postcond, decoder_cond, bit_width):
    variables = {}
    constraints = []
    # const_errors_to_z3(err_vals_tree.children[0], variables)
    cass_tree = VCgeneration(precond, program, postcond)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)

    decoder_tree, _, _ = precond_generator('skip', decoder_cond, 'true')
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr)

    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)
    # print(decoding_formula)
    substitution = And(*constraints)
    formula = And(substitution, decoding_formula)
    return formula, variables
def constrep_testing(expr, variables, consts):
    
    replace = []
    for i in consts.keys():
        replace.append((variables[i], consts[i]))
    formula_to_check = simplify(substitute(expr, replace))
    # print(formula_to_check)
    return formula_to_check

## Try use bitwuzla
def smtchecking_testing(formula):
    solver = SolverFor("QF_BV")
    solver.add(formula)
    # r = solver.check()
    # print(r)

    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic QF_BV)\n" + "\n".join(lines[1:]) + f"\n(get-model)"

    # tm = cvc5.TermManager()

    s2 = cvc5.Solver()
    s2.setOption('produce-models', 'true')  
    cvc5_parser = cvc5.InputParser(s2)

    cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

    sm = cvc5_parser.getSymbolManager()
    temp = 0
    while True:
        cmd = cvc5_parser.nextCommand()
        if cmd.isNull():
            #print(temp)
            break
        temp = cmd.invoke(s2, sm)
    
    r = s2.checkSat()
    correction = []
    if str(r) == 'sat':
        vars = sm.getDeclaredTerms()
        
        cvars = []
        for i in vars:
            vstr = i.getSymbol().split('_')
            if(len(vstr) == 2) and vstr[0] != 's':
                cvars.append(i)
        res_lines = (s2.getModel([], cvars)).decode('utf-8').splitlines()[1:-1]
        for i, line in enumerate(res_lines):
            
            if(line[-2] == '1'):
                elems = line.split(' ')
                # print(elems)
                correction.append(elems[1])

       
    return r, correction
def formulagen_testing(matrix, distance):
    num_qubits = matrix. shape[1] // 2
    k = matrix.shape[0] - num_qubits
    # max_errors = (distance - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    # max_errors = (distance - 1) // 2 
    # matrix = matrixrix_gen(distance)

    precond_x, precond_z = stab_cond_gen(matrix, num_qubits, k)
    postcond_x, postcond_z = precond_x, precond_z

    program_x, program_z = program_gen(matrix, num_qubits, k)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(matrix, num_qubits, k, distance, distance, 'test')
    
    packed_x = smtencoding_testing(precond_x, program_x, postcond_x, decoder_cond_x, bit_width)
    packed_z = smtencoding_testing(precond_z, program_z, postcond_z, decoder_cond_z, bit_width)

    return packed_x, packed_z
def seq_cond_checker_testing(packed_x, packed_z, err_vals):
    consts_x = {}
    consts_z = {}
    for i, ei in enumerate(err_vals):
        consts_x[f'ez_{(i+1)}'] = BitVecVal(ei,1)
        consts_z[f'ex_{(i+1)}'] = BitVecVal(ei,1)
    
    expr_x, variables_x = packed_x
    expr_z, variables_z = packed_z

    formula_x = constrep_testing(expr_x, variables_x, consts_x)
    formula_z = constrep_testing(expr_z, variables_z, consts_z)
    #print(formula_z)
    t3 = time.time()
    result_x = smtchecking_testing(formula_x)
    result_z = smtchecking_testing(formula_z)
    t4 = time.time()
    return t4 - t3, result_x, result_z 


def worker(task_id, err_vals):
    try: 
        start = time.time()
        smttime, resx, resz = seq_cond_checker_testing(packed_x, packed_z, err_vals)
        pos = np.where(err_vals == 1)[0]
        # print(resx, resz, len(pos), pos)
        # with open('Details/surface_code_testing-9.txt', 'a') as f:
        #     f.write(f'id: {task_id} | err_counts: {len(pos)} | err_pos: {pos} | time: {smttime}\n')
        #     f.write(f'result_x: {resx} | result_z: {resz}\n')
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
    global corr_info
    if isinstance(result[1], ExceptionWrapper):
        task_id = result[0]
        print(task_info[task_id])
        err_info.append(result[1])
        return
    global processed_job
    global last_print
    
    task_id, time_cost = result
    # if len(resx) > 1 or len(resz) > 1:
    #     corr_info[task_id] = [resx[1], resz[1]] ## print corrections 
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
# def sur_cond_checker_testing(distance, max_sample_num, max_proc_num):

    global task_info
    global packed_x
    global packed_z
    global total_job
    global start_time
    global max_process_num
    global err_info
    global last_print
    start = time.time()
    max_process_num = max_proc_num
    start_time = time.time()
    last_print = start_time
    #cond_x, cond_z = cond_generator(distance)
    numq = matrix.shape[1] // 2
    distance = dx
    tasks = task_generator(numq, distance, max_sample_num)
    print("Task generated. Start checking.")
    total_job = len(tasks)
    print(f"total_job: {total_job}")
    
    task_info = []
    err_info = []
    # corr_info = defaultdict(list)
    packed_x, packed_z = formulagen_testing(matrix, distance)
    end_gen = time.time()
    print(f"Generation time: {end_gen - start}")
    with Pool(processes = max_proc_num) as pool:
        result_objects = []
        for i, task in enumerate(tasks):
            # res = pool.apply_async(worker, (distance, task,))
            task_info.append(analysis_task(i, task))
            # result_objects.append(pool.apply_async(worker, (i, distance, task,), callback=process_callback, error_callback=process_error))
            result_objects.append(pool.apply_async(worker, (i, task,), callback=process_callback, error_callback=process_error))
            # print(res.get())
            # if (i % 50 == 0):
                #print(i, task)
        pool.close()
        #[res.wait() for res in result_objects]
        [res.wait() for res in result_objects]
        pool.join()
    
    for i, ei in enumerate(err_info):
        ei.re_raise()
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

    # print(len(task_info))
    # # print(task_info[1])
    # task_info.sort(key=lambda x: x[-1])

    # with open('sorted_results.txt', 'w') as f:
    #     for i, ti in enumerate(task_info):
    #         f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-1]}\n')
    #         f.write(f'{ti[1]}\n')
    #         f.write(f'{" | ".join(ti[2])}\n')
    end = time.time()

    
    processed_job = 0
    unprocessed_job = 0

    return round(end_gen - start, 5), round(end - end_gen, 5)
    # with open('corrections.txt', 'w') as f:
    #     for i, ti in enumerate(task_info):
    #         if i in corr_info.keys():
    #             f.write(f'rank: {i} | id: {ti[0]} |\n')  
    #             f.write(f'{ti[1]}\n')
    #             f.write(f'corrections:{corr_info[i]}\n')
def sur_cond_checker_testing(distance, max_sample_num, max_proc_num):
    matrix = surface_matrix_gen(distance)   
    t1, t2 = cond_checker_testing(matrix, distance, distance, max_sample_num, max_proc_num) 
    return t1, t2

if __name__ == "__main__": 
    tblib.pickling_support.install()
    
    # for i in range(1, 10):
    # test_time = []
    # smtsolve_time = []
    # gen_time = []
    # for i in range(2, 13):
    Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                   [1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
    Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])
    distance = 7
    max_sample_num = 500
    max_proc_num = 250
    matrix = qldpc_codes.stabs_Tanner(1, 1, Ham743, Ham733)
   
    n = matrix.shape[1] // 2
    k = matrix.shape[0] - n
    dx_max = min([np.count_nonzero(matrix[n - k + i]) for i in range(k)])
    minx = np.argmin([np.count_nonzero(matrix[n - k + i]) for i in range(k)])
    minz = np.argmin([np.count_nonzero(matrix[n + i]) for i in range(k)])
    dz_max = min([np.count_nonzero(matrix[n + i]) for i in range(k)])
    print(dx_max, dz_max)
    err_val1 = matrix[n - k + minx]
    err_val2 = matrix[n + minz]
    # t1, t2 = cond_checker_testing(matrix, distance, distance, max_sample_num, max_proc_num)
    # # t1, t2 = sur_cond_checker_testing(distance, max_sample_num, max_proc_num)
    # print(t1, t2)

    # smtsolve_time.append(t2)
    # gen_time.append(t1)
    
    # print(gen_time)
    # print(smtsolve_time)
    # distance = 7
    # max_sample_num = 500
    # max_proc_num = 250
    # timei = sur_cond_checker_testing(distance, max_sample_num, max_proc_num)
    # print(timei)
    # # runtime.append(timei)
    # print(timei)
    # with open(f'Details/testing_example_9.txt', 'w') as f:
    #     for task in tasks:
    #         f.write(f'{task}\n')
    # print(tasks[0])
    # lists = []
    # with open(f'Details/testing_example_7.txt', 'r') as f:
    #     while True:
    #         line1 = f.readline().strip()[1:]   
    #         line2 = f.readline().strip()[:-1]
    #         if not line1:
    #             break
    #         line = line1 + " " + line2
    #         list_elements = [int(element) for element in line.split()]
            
    #         lists.append(list_elements)

    # print(len(lists))
    # print(lists[0])
    # plt.plot(x, runtime, label = 'runtime')
    # plt.xlabel('distance')
    # plt.ylabel('runtime')
    # plt.legend()
    # plt.title('Runtime of Surface Code Checker')
    # plt.savefig('surface_code_test_runtime.png')
    # err_vals_test = task_generator(distance, 3)
    # print(err_vals_test)
    # packed_x, packed_z = formulagen_testing(distance)
    # for i in range(3):

    #     print(seq_cond_checker_testing(packed_x, packed_z, err_vals_test[i]))
    
    