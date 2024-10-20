import numpy as np
import datetime
import time
import cvc5
import bitwuzla
import math
from z3 import *
from multiprocessing import Pool
import tblib.pickling_support
import sys
from timebudget import timebudget
import matplotlib.pyplot as plt
## import customized functions
from verifier import precond_generator
from encoder import tree_to_z3, VCgeneration
from condition_multiq import *

sys.setrecursionlimit(1000000)

## Handling errors
class ExceptionWrapper(object):
    def __init__(self, ee):
        self.ee = ee
        _, _, self.tb = sys.exc_info()

    def re_raise(self):
        raise self.ee.with_traceback(self.tb)    

def smtencoding_meas_err(precond, program, postcond, decoder_cond, sum_cond, bit_width):
    variables = {}
    constraints = []
    # const_errors_to_z3(err_vals_tree.children[0], variables
    # cass_tree, midrnd_trees = VCgeneration(precond, program, postcond)
    result = VCgeneration(precond, program, postcond)
    cass_tree = result[0]
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
    if len(result) > 1:
        midrnd_trees = result[1]
        midrnd_exprs = []
        for aux in midrnd_trees:
            expr = tree_to_z3(aux, variables, bit_width, [], False)
            midrnd_exprs.append(expr)
            # print(expr)
        midrnd_expr = And(*midrnd_exprs)
    # print(midrnd_expr)
    decoder_tree, _, sum_tree = precond_generator('skip', decoder_cond, sum_cond)
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr)
    # print(decoder_expr)
    var_corr = {}
    sum_expr = simplify(tree_to_z3(sum_tree.children[0], var_corr, bit_width, {}, False ))
    if len(result) > 1:
        decoding_formula = simplify(And(cass_expr, midrnd_expr, decoder_expr))
    else:
        decoding_formula = simplify(And(cass_expr, decoder_expr))
    # decoding_formula = simplify(decoding_formula)
    # print(decoding_formula)
    substitution = And(*constraints)
    formula = And(substitution, decoding_formula)
    return formula, logic_expr, sum_expr, variables, var_corr
def constrep_meas_err(formula, logic, variables, consts):
    replace = []
    for i in consts.keys():
        replace.append((variables[i], consts[i]))   
    
    return simplify(substitute(formula, replace)), simplify(substitute(logic, replace))

def smtchecking_meas_err(formula, logic_expr, sum_expr, var_corr): 
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
    print(logic_expr)
    result = simplify(substitute(logic_expr, replace))
    if result == True:
        return corr
    else:
        return result

## Sequential checker for meas errs 
def formula_gen_meas_err(mat, dx, dz, rnds, N):
    ## mat: check matrix, dx, dz: distance, rnd: measurement rounds per layer; N; number of logical qubits;
    numq = mat.shape[1] // 2
    # k = mat.shape[0] - numq
    bit_width = int(math.log2(numq * N * rnds)) + 1
    program_x, program_z = program_gen_qec_mul(mat, numq, N, rnds)

    postcond_x, postcond_z  = stab_cond_gen_multiq(mat, numq, N)
    decoder_cond_x, decoder_cond_z, meas_corr_x, meas_corr_z = decode_cond_gen_mul(mat, numq, N, rnds, dx, dz) 
    precond_x, precond_z = postcond_x, postcond_z
    sum_x = ""
    sum_z = ""
    for ci in meas_corr_x:
        sum_x = sum_x + f"c_({ci}) +"
    for ci in meas_corr_z:
        sum_z = sum_z + f"c_({ci}) +"
    
    sum_x += f"sum i 1 {numq * N * rnds} (cz_(i))"
    sum_z += f"sum i 1 {numq * N * rnds} (cx_(i))" 
    
    # print(precond_x, program_x, postcond_x)
    packed_x = smtencoding_meas_err(precond_x, program_x, postcond_x, decoder_cond_x, sum_x, bit_width)
    packed_z = smtencoding_meas_err(precond_z, program_z, postcond_z, decoder_cond_z, sum_z, bit_width)
    
    return packed_x, packed_z, meas_corr_x, meas_corr_z


def seq_checker_meas_err(packed_expr, meas_corr, err_vals, opt):
    consts = {}
    numq = len(err_vals) - len(meas_corr)
    
    for i in range(numq):
        if opt == 'x':
            consts[f'ez_{i+1}'] = BitVecVal(err_vals[i], 1)
        else:
            consts[f'ex_{i+1}'] = BitVecVal(err_vals[i], 1)
    for i, cr in enumerate(meas_corr):
        consts[f'e_{cr}'] = BitVecVal(err_vals[i + numq], 1)
    

    
    ## Assignments for meas errors
    # for i, ei in enumerate():

    expr, logic_expr, sum_expr, variables, var_corr = packed_expr
    # print(variables)
    formula, logic_expr = constrep_meas_err(expr, logic_expr, variables, consts)
    
    result = smtchecking_meas_err(formula, logic_expr, sum_expr, var_corr)
    
    return result
# def seq_checker_meas_err(packed_x, packed_z, err_vals):
#     consts_x = {}
#     consts_z = {}
#     for i, ei in enumerate(err_vals):
#         consts_x[f'ez_{i + 1}'] = BitVecVal(ei, 1)
#         consts_z[f'ex_{i + 1}'] = BitVecVal(ei, 1)
    
#     expr_x, variables_x = packed_x
#     print(variables_x)
#     # print(variables_x)
#     expr_z, variables_z = packed_z
    
#     formula_x = constrep_meas_err(expr_x, variables_x, consts_x)
#     # print(formula_x)
#     formula_z = constrep_meas_err(expr_z, variables_z, consts_z)

#     t3 = time.time()
#     result_x = smtchecking_meas_err(formula_x)
#     result_z = smtchecking_meas_err(formula_z)  
#     t4 = time.time()
    
#     return t4 - t3, result_x, result_z
if __name__ == '__main__':
    dx, dz = 3, 3
    mat = surface_matrix_gen(dx)
    n = mat.shape[1] // 2
    k = mat.shape[0] - n
    # nonzero_x = np.where(np.any(mat[:n-k,:n] != 0, axis=1))[0]
    # nonzero_z = np.where(np.any(mat[:n-k,n:] != 0, axis=1))[0]
    
    N = 1
    rnds = 2
    packed_x, packed_z, meas_corr_x, meas_corr_z = formula_gen_meas_err(mat, dx, dz, rnds, N)
    # print(meas_corr_x, meas_corr_z)
    meas_err_cnt_x =  len(meas_corr_x)
    meas_err_cnt_z =  len(meas_corr_z)
   
    err_vals_x = np.zeros(dx * dz * N * rnds + meas_err_cnt_x)
    err_vals_z = np.zeros(dx * dz * N * rnds + meas_err_cnt_z)
    err_vals_x[1] = 1
    err_vals_x[2] = 1
    err_vals_z[1] = 1
    err_vals_z[2] = 1
    print(seq_checker_meas_err(packed_x, meas_corr_x, err_vals_x, 'x'))
    print(seq_checker_meas_err(packed_z, meas_corr_z, err_vals_z, 'z'))
    # err_val_x[1] = 1
    # print(seq_checker_meas_err(packed_x, packed_z, err_val_test))