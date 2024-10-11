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

def smtencoding_meas_err(precond, program, postcond, decoder_cond, bit_width):
    variables = {}
    constraints = []
    # const_errors_to_z3(err_vals_tree.children[0], variables
    # cass_tree, midrnd_trees = VCgeneration(precond, program, postcond)
    result = VCgeneration(precond, program, postcond)
    cass_tree = result[0]
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)
    # print(cass_expr)
    if len(result) > 1:
        midrnd_trees = result[1]
        midrnd_exprs = []
        for i, aux in enumerate(midrnd_trees):
            expr = tree_to_z3(aux, variables, bit_width, [], False)
            midrnd_exprs.append(expr)
            # print(expr)
        midrnd_expr = And(*midrnd_exprs)
    decoder_tree = precond_generator('skip', decoder_cond, 'true')[0]
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr)
    print(decoder_expr)
    if len(result) >1:
        decoding_formula = simplify(And(cass_expr, midrnd_expr, decoder_expr))
    else:
        decoding_formula = simplify(And(cass_expr, decoder_expr))
    # decoding_formula = simplify(decoding_formula)
    # print(decoding_formula)
    substitution = And(*constraints)
    formula = And(substitution, decoding_formula)
    return formula, variables
def constrep_meas_err(formula, variables, consts):
    replace = []
    for i in consts.keys():
        replace.append((variables[i], consts[i]))   
    
    return simplify(substitute(formula, replace))

def smtchecking_meas_err(formula): 
    solver = Solver()
    solver.add(formula)

    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic QF_BV)\n" + "\n".join(lines[1:]) + f"\n(get-model)"

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
## Sequential checker for meas errs 
def formula_gen_meas_err(mat, dx, dz, rnds, N):
    ## mat: check matrix, dx, dz: distance, rnd: measurement rounds per layer; N; number of logical qubits;
    numq = mat.shape[1] // 2
    # k = mat.shape[0] - numq
    bit_width = int(math.log2(numq)) + 1
    program_x, program_z = program_gen_qec_mul(mat, numq, N, rnds)
    # print(program_x)
    postcond_x, postcond_z  = stab_cond_gen_multiq(mat, numq, N)
    decoder_cond_x, decoder_cond_z = decode_cond_gen_mul(mat, numq, N, rnds, dx, dz) 
    precond_x, precond_z = postcond_x, postcond_z

    # print(precond_x, program_x, postcond_x)
    packed_x = smtencoding_meas_err(precond_x, program_x, postcond_x, decoder_cond_x, bit_width)
    packed_z = smtencoding_meas_err(precond_z, program_z, postcond_z, decoder_cond_z, bit_width)
    
    return packed_x, packed_z
   
def seq_checker_meas_err(packed_x, packed_z, err_vals):
    consts_x = {}
    consts_z = {}
    for i, ei in enumerate(err_vals):
        consts_x[f'ez_{i + 1}'] = BitVecVal(ei, 1)
        consts_z[f'ex_{i + 1}'] = BitVecVal(ei, 1)
    expr_x, variables_x = packed_x
    # print(variables_x)
    expr_z, variables_z = packed_z
    
    formula_x = constrep_meas_err(expr_x, variables_x, consts_x)
    print(formula_x)
    formula_z = constrep_meas_err(expr_z, variables_z, consts_z)

    t3 = time.time()
    result_x = smtchecking_meas_err(formula_x)
    result_z = smtchecking_meas_err(formula_z)  
    t4 = time.time()
    
    return t4 - t3, result_x, result_z
if __name__ == '__main__':
    mat = surface_matrix_gen(3)
    N = 1
    rounds = 2
    packed_x, packed_z = formula_gen_meas_err(mat, 3, 3, 2, 1)
    err_val_test = np.zeros(9 * N * rounds)
    err_val_test[1] = 1
    print(seq_checker_meas_err(packed_x, packed_z, err_val_test))