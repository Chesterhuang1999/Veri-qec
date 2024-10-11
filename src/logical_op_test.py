import sys
from condition_multiq import *
from encoder import *
from parser_qec import get_parser
from lark.reconstruct import Reconstructor
from z3 import *
import matplotlib.pyplot as plt
from timebudget import timebudget 
from collections import defaultdict
from smtchecking_partition import *
import re
import cvc5
from parallel_dfs import *

sys.setrecursionlimit(10**6)

### Verification steps: I. Generate the program and assertion from the check matrix and the required logical operations
###                     II. Generate the decoding conditions and error conditions
###                    III. Transform those conditions into a z3 SMT expression
###                    IV. Check the satisfiability of the SMT expression


### Scenario I: 
@timebudget
def code_checker_basic(matrix, numq, k, dx, dz):
    t1 = time.time()
    ex_max = (dx - 1) // 2
    ez_max = (dz - 1) // 2
    bit_width = int(math.log2(numq)) + 1
    precond = stab_cond_gen(matrix, numq, k)
    postcond = precond 
    program = program_gen(matrix, numq, k)
    decoder_cond = decode_cond_gen(matrix, numq, k)
    
### Scenario II: Logical operations on encoded qubits
def seq_checker_logical(args, err_vals):
    numq, d, code, prog_log, poc, pe, dec, sym, flag = args
    emax = (d - 1) // 2
    bit_width = int(math.log2(numq)) + 1
    # program_log = program_gen_logic(matrix, numq, N, gateinfo, code)
    program = ';'.join([prog_log, pe])
    if flag == 'x':
        erc = f"sum i 1 {numq} (ez_(i)) <= {emax}"
        egt = f"sum i 1 {numq} (ez_(i)) <= {d - 1}"
        err_val_expr = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        err_val_str = ' && '.join(err_val_expr)
    elif flag == 'z':
        erc = f"sum i 1 {numq} (ex_(i)) <= {emax}"
        egt = f"sum i 1 {numq} (ex_(i)) <= {d - 1}"
        err_val_expr = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        err_val_str = ' && '.join(err_val_expr) 
    _, _, prc_tree = precond_generator(prog_log, poc, poc)
    prc = re.sub(r'\s*_\s*','_', Reconstructor(parser = get_parser()).reconstruct(prc_tree))
    formula = smtencoding_parti(code, [prc, program, poc], [erc, egt, err_val_str], dec, sym, bit_width)
    result = smtchecking(formula)
    return result

def worker_logical(task_id, args, err_vals):
    start = time.time()
    res = seq_checker_logical(args, err_vals)
    end = time.time()
    cost = end - start
    if res.isSat() == False:
        print(task_id)
    return task_id, cost
@timebudget
def check_single_layer(args, max_proc_num):
    global task_info
    distance, numq = args[1], args[0]
    tg = subtask_generator(distance, numq, max_proc_num)
    tasks = tg()
    with Pool(processes = max_proc_num) as pool:
        result_objects = []
        for i, task in enumerate(tasks):
            # res = pool.apply_async(worker, (distance, task,))
            task_info.append(analysis_task(i, task))
            result_objects.append(pool.apply_async(worker_logical, (i, args, task,), callback=process_callback, error_callback=process_error))
            # print(res.get())
        pool.close()
        #[res.wait() for res in result_objects]
        [res.wait() for res in result_objects]
        pool.join()

    print(task_info)
    task_info.sort(key=lambda x: x[-1])
    
    # with open('sorted_results.txt', 'w') as f:
    #     for i, ti in enumerate(task_info):
    #         f.write(f'rank: {i} | id: {ti[0]} | time: {ti[-1]}\n')
    #         f.write(f'{ti[1]}\n')
    #         f.write(f'{" | ".join(ti[2])}\n')

    task_info.clear()

@timebudget
def checker_logical(matrix, numq, k, N, dx, dz, circuit):
    # precond = stab_cond_gen(matrix, numq, k)
    max_proc_num = 16
    pocx, pocz = stab_cond_gen_multiq(matrix, numq, k, N)
    code = 'surface'
    pex, pez = program_gen_qec(matrix, numq, k,  N)
    decx, decz = decode_cond_gen_multiq(matrix, numq, k, N, dx, dz)
    groups = sym_gen(dx, dz)
    symx, symz = [], []
    for value in groups.values():
        k, l = value[0], value[1]
        symx.append(f"ex_({k + 1}) <= ex_({l + 1})")
        symz.append(f"ez_({k + 1}) <= ez_({l + 1})")
    symx, symz = '&&'.join(symx), '&&'.join(symz)

    for ind, gateinfo in circuit.items():
        #args = [matrix, numq, k, N, dx, dz, gateinfo, code, pcx, pcz, pex, pez]
        prog_log = program_gen_logic(matrix, numq, N, gateinfo, code)
        args_x = [numq, dx, code, prog_log, pocx, pex, decx, symx, 'x']
        args_z = [numq, dz, code, prog_log, pocz, pez, decz, symz, 'z']
        # task_info_x = []
        # task_info_z = []
        check_single_layer(args_x, max_proc_num)
        check_single_layer(args_z, max_proc_num)
        #err_vals = enum_generator(numq, enum_qbits)
        #cond_checker(args,)
        


### Scenario III: Errors during decoding (complicated model, use only surface code as an example)

@timebudget
def code_checker_error(matrix, numq, k, dx, dz):
    pass
#


### Scenario IV: Errors during both

if __name__ == "__main__" : 
    matrix = surface_matrix_gen(3)
    # DJ = defaultdict(list)
    # DJ[1] = [['H', [1]], ['H',[2]], ['H', [3]]]
    # DJ[2] = [['CNOT', [1,2]], ['CNOT', [1,3]]]
    # DJ[3] = [['H', [1]], ['H',[2]]]
    H = defaultdict(list)
    H[1] = [['H', [1]], ['H', [2]]]
    checker_logical(matrix, 9, 1, 2, 3, 3, H)