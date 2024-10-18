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
from verifier import precond_generator
from encoder import tree_to_z3, VCgeneration
from condition import *
from Dataset import qldpc_codes, linalg_GF, special_codes
sys.setrecursionlimit(1000000)

## Handling errors
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()

    def re_raise(self):
        raise self.ee.with_traceback(self.tb)    



def smtencoding_testing(precond, program, postcond, decoder_cond, sum_cond, bit_width):
    variables = {}
    # const_errors_to_z3(err_vals_tree.children[0], variables)
    cass_tree = VCgeneration(precond, program, postcond)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)
    childs = cass_expr.children()
    logic_expr_list = []
    cass_expr_list = []
    for child in childs:
        name = child.children()[0].sexpr().split('_')[0]
        if name == 's':
            cass_expr_list.append(child)
        else:
            logic_expr_list.append(child)
    cass_expr = And(*cass_expr_list)
    if len(logic_expr_list) > 1:
        logic_expr = And(*logic_expr_list)
    else: 
        logic_expr = logic_expr_list[0]    
    decoder_tree, _, sum_tree = precond_generator('skip', decoder_cond, sum_cond)
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, [], False)
    decoder_expr = simplify(decoder_expr)
    var_corr = {}
    sum_expr = tree_to_z3(sum_tree.children[0], var_corr, bit_width, [], False)
    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)
    # print(decoding_formula)
    # substitution = And(*constraints)
    # formula = And(substitution, decoding_formula)
    return decoding_formula, logic_expr, sum_expr, variables, var_corr
def constrep_testing(expr, logic, variables, consts):
    
    replace = []
    for i in consts.keys():
        replace.append((variables[i], consts[i]))
    formula_to_check = simplify(substitute(expr, replace))
    logic = simplify(substitute(logic, replace))
    # print(formula_to_check)
    return formula_to_check, logic

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
    if str(r) == 'sat':
        vars = sm.getDeclaredTerms()
        correction = []
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

        return r

    return r

def smtchecking_opt(formula, logic_expr, sum_expr, var_corr):
    s = z3.Optimize()
    s.add(formula)
    s.minimize(sum_expr)
    r = s.check()
    if r == sat:
        m = s.model()
        replace = []
        corr = []
        for v in var_corr.values():
            # print(m[v])
            replace.append((v, m[v]))
            if m[v] == 1:
                corr.append((v, m[v]))

    result = simplify(substitute(logic_expr, replace))
    if result == True:
        return corr
    else:
        return result
    # return result, corr


def formulagen_testing(matrix, dx, dz):
    num_qubits = matrix.shape[1] // 2
    k = matrix.shape[0] - num_qubits
    bit_width = int(math.log2(num_qubits)) + 1 
    
    precond_x, precond_z = stab_cond_gen(matrix, num_qubits, k)
    postcond_x, postcond_z = precond_x, precond_z

    program_x, program_z = program_gen(matrix, num_qubits, k)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(matrix, num_qubits, k, dx, dz, 'test-opt')
    sum_x = f"sum i 1 {num_qubits} (cz_(i))"
    sum_z = f"sum i 1 {num_qubits} (cx_(i))"
    packed_x = smtencoding_testing(precond_x, program_x, postcond_x, decoder_cond_x, sum_x, bit_width)
    packed_z = smtencoding_testing(precond_z, program_z, postcond_z, decoder_cond_z, sum_z, bit_width)

    return packed_x, packed_z
# def formulagen_testing(distance):
#     num_qubits = distance**2
#     # max_errors = (distance - 1) // 2
#     bit_width = int(math.log2(num_qubits)) + 1
#     # max_errors = (distance - 1) // 2 
#     surface_mat = surface_matrix_gen(distance)

#     precond_x, precond_z = stab_cond_gen(surface_mat, num_qubits, 1)
#     postcond_x, postcond_z = precond_x, precond_z

#     program_x, program_z = program_gen(surface_mat, num_qubits, 1)
#     decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance, 'test-opt')
#     sum_x = f"sum i 1 {num_qubits} (cz_(i))"
#     sum_z = f"sum i 1 {num_qubits} (cx_(i))"
#     packed_x = smtencoding_testing(precond_x, program_x, postcond_x, decoder_cond_x, sum_x, bit_width)
#     packed_z = smtencoding_testing(precond_z, program_z, postcond_z, decoder_cond_z, sum_z, bit_width)

#     return packed_x, packed_z
# def seq_cond_checker_testing(packed_x, packed_z, err_vals):
#     consts_x = {}
#     consts_z = {}
#     for i, ei in enumerate(err_vals):
#         consts_x[f'ez_{(i+1)}'] = BitVecVal(ei,1)
#         consts_z[f'ex_{(i+1)}'] = BitVecVal(ei,1)
    
#     expr_x, logic_x, sum_x, variables_x, var_corr_x = packed_x
#     expr_z, logic_z, sum_z, variables_z, var_corr_z = packed_z

#     formula_x, logic_x = constrep_testing(expr_x, logic_x, variables_x, consts_x)
#     formula_z, logic_z = constrep_testing(expr_z, logic_z, variables_z, consts_z)
#     # print(formula_x, logic_x)
#     #print(formula_z)
#     t3 = time.time()
#     # result_x = smtchecking_testing(formula_x)
#     # result_z = smtchecking_testing(formula_z)
#     result_x = smtchecking_opt(formula_x, logic_x, sum_x, var_corr_x)
#     result_z = smtchecking_opt(formula_z, logic_z, sum_z, var_corr_z)
#     t4 = time.time()
#     return t4 - t3, result_x, result_z 
def seq_cond_checker_testing(packed_expr, err_vals, opt):
    consts = {}

    for i, ei in enumerate(err_vals):
        if opt == 'x':
            consts[f'ez_{(i+1)}'] = BitVecVal(ei,1)
        else:
            consts[f'ex_{(i+1)}'] = BitVecVal(ei,1)
    
    expr, logic, sum_expr, variables, var_corr = packed_expr
 

    formula, logic = constrep_testing(expr, logic, variables, consts)
    # formula_z, logic_z = constrep_testing(expr_z, logic_z, variables_z, consts_z)
    # print(formula)
    t3 = time.time()
 
    result = smtchecking_opt(formula, logic, sum_expr, var_corr)
    # result_z = smtchecking_opt(formula_z, logic_z, sum_z, var_corr_z)
    t4 = time.time()
    return t4 - t3, result



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
        with open('Details/surface_code_testing_opt-Tanner.txt', 'a') as f:
            f.write(f'id: {task_id} | err_counts: {len(pos)} | err_pos: {pos}\n')
            f.write(f'error_type: {opt} | result: {res} \n')
        # print(resx, resz)
        end = time.time()
        cost = end - start

        return task_id, cost
    except Exception as e:
        return task_id, ExceptionWrapper(e)
##Random generate samples for testing
def random_sample(N, D):
    max_ham_weight = D - 1
    num_ones = np.random.randint(1, max_ham_weight + 1)
    
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
    while cnt < max_sample_num:
        sample = random_sample_fixd(numq, distance)
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
    print(numq)
    
    tasks_x = task_generator(numq, dz, max_sample_num)
    tasks_z = task_generator(numq, dx, max_sample_num)
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
    # end = time.time()

    
    processed_job = 0
    unprocessed_job = 0

    # return round(end - start_time, 5)


def sur_cond_checker_testing(distance, max_sample_num, max_proc_num):
    matrix = surface_matrix_gen(distance)   
    cond_checker_testing(matrix, distance, distance, max_sample_num, max_proc_num)

    # # with open('unsorted_results.txt', 'w') as f:
    # #     for i, ti in enumerate(task_info):
    # #         f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-1]}\n')
    # #         f.write(f'{ti[1]}\n')
    # #         f.write(f'{" | ".join(ti[2])}\n')

    # # print(len(task_info))
    # # # print(task_info[1])
    # task_info.sort(key=lambda x: x[-1])

    # with open('sorted_results.txt', 'w') as f:
    #     for i, ti in enumerate(task_info):
    #         f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-1]}\n')
    #         f.write(f'{ti[1]}\n')
    #         f.write(f'{" | ".join(ti[2])}\n')
    # end = time.time()

    
    # processed_job = 0
    # unprocessed_job = 0

    # return round(end - start, 5)

if __name__ == "__main__": 
    tblib.pickling_support.install()

    distance = 20
    max_sample_num = 200
    max_proc_num = 240
    Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                   [1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
    Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])
    Rep51 = np.array([[1, 1, 0, 0, 0],
                  [1, 0, 1, 0, 0],
                  [1, 0, 0, 1, 0],
                  [1, 0, 0, 0, 1]])
    Par54 = np.array([[1, 1, 1, 1, 1]])
    Rep31 = np.array([[1, 1, 0],
                  [1, 0, 1]])
    Par32 = np.array([[1, 1, 1]])

    # matrix = qldpc_codes.stabs_Tanner(1, 1, Ham743, Ham733)
    matrix = special_codes.stabs_triotho(2)
    # print(matrix)
    # n = matrix.shape[1] // 2
    # k = matrix.shape[0] - n
    
    # dx_max = min([np.count_nonzero(matrix[n - k + i]) for i in range(k)])
    # dz_max = min([np.count_nonzero(matrix[n + i]) for i in range(k)])
    # print(n, dx_max, dz_max)
    # cond_checker_testing(matrix, dx_max, dz_max, max_sample_num, max_proc_num)

    # sur_cond_checker_testing(distance, max_sample_num, max_proc_num)
    
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
    
    
