import numpy as np
import datetime
import time

import math
from z3 import *
import sys

## import customized functions
from verifier import precond_generator
from encoder import tree_to_z3, VCgeneration
from condition import *
from Dataset import qldpc_codes, linalg_GF, special_codes

sys.setrecursionlimit(1000000)

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
# def smtchecking_testing(formula):
#     solver = SolverFor("QF_BV")
#     solver.add(formula)
#     # r = solver.check()
#     # print(r)

#     formula_smt2 = solver.to_smt2()
#     lines = formula_smt2.splitlines()
#     formula_smt2 = f"(set-logic QF_BV)\n" + "\n".join(lines[1:]) + f"\n(get-model)"

#     # tm = cvc5.TermManager()

#     s2 = cvc5.Solver()
#     s2.setOption('produce-models', 'true')  
#     cvc5_parser = cvc5.InputParser(s2)

#     cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

#     sm = cvc5_parser.getSymbolManager()
#     temp = 0
#     while True:
#         cmd = cvc5_parser.nextCommand()
#         if cmd.isNull():
#             #print(temp)
#             break
#         temp = cmd.invoke(s2, sm)
    
#     r = s2.checkSat()
#     if str(r) == 'sat':
#         vars = sm.getDeclaredTerms()
#         correction = []
#         cvars = []
#         for i in vars:
#             vstr = i.getSymbol().split('_')
#             if(len(vstr) == 2) and vstr[0] != 's':
#                 cvars.append(i)
#         res_lines = (s2.getModel([], cvars)).decode('utf-8').splitlines()[1:-1]
#         for i, line in enumerate(res_lines):
            
#             if(line[-2] == '1'):
#                 elems = line.split(' ')
#                 # print(elems)
#                 correction.append(elems[1])

#         return r

#     return r

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


def seq_cond_checker_testing(packed_expr, err_vals, opt):
    consts = {}

    for i, ei in enumerate(err_vals):
        if opt == 'x':
            consts[f'ez_{(i+1)}'] = BitVecVal(ei,1)
        else:
            consts[f'ex_{(i+1)}'] = BitVecVal(ei,1)
    
    expr, logic, sum_expr, variables, var_corr = packed_expr
 

    formula, logic = constrep_testing(expr, logic, variables, consts)
    
    t3 = time.time()
 
    result = smtchecking_opt(formula, logic, sum_expr, var_corr)
    
    t4 = time.time()
    return t4 - t3, result


if __name__ == "__main__":
    pass