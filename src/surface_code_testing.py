import numpy as np
from verifier import precond_generator
from encoder import tree_to_z3, const_errors_to_z3, VCgeneration
from condition import *
import time
import cvc5
import math
from collections import defaultdict
from z3 import *
from surface_code_partition_merge import smtchecking, sym_gen, cond_generator


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

    substitution = And(*constraints)
    formula = And(substitution, decoding_formula)
    return formula, variables
def constrep_testing(expr, variables, consts):
    
    replace = []
    for i in consts.keys():
        replace.append((variables[i], consts[i]))
    formula_to_check = simplify(substitute(expr, replace))
    return formula_to_check

## Try use bitwuzla
def smtchecking_testing(formula):
    solver = SolverFor("QF_BV")
    solver.add(formula)
    r = solver.check()
    print(r)

    model = solver.model()
    print(model)
    # formula_smt2 = solver.to_smt2()
    # lines = formula_smt2.splitlines()
    # formula_smt2 = f"(set-logic QF_BV)\n" + "\n".join(lines[1:])

    # # tm = cvc5.TermManager()

    # s2 = cvc5.Solver()
    # s2.setOption('produce-models', 'true')  
    # cvc5_parser = cvc5.InputParser(s2)

    # cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

    # sm = cvc5_parser.getSymbolManager()
    # while True:
    #     cmd = cvc5_parser.nextCommand()
    #     if cmd.isNull():
    #         break
    #     cmd.invoke(s2, sm)
    
    # r = s2.checkSat()
    return r
def formulagen_testing(distance):
    num_qubits = distance**2
    max_errors = (distance - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    max_errors = (distance - 1) // 2 
    surface_mat = surface_matrix_gen(distance)

    precond_x, precond_z = stab_cond_gen(surface_mat, num_qubits, 1)
    postcond_x, postcond_z = precond_x, precond_z

    program_x, program_z = program_gen(surface_mat, num_qubits, 1)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance)
    
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
    t3 = time.time()
    result_x = smtchecking_testing(formula_x)
    result_z = smtchecking_testing(formula_z)
    t4 = time.time()
    return t4 - t3, result_x, result_z 



if __name__ == "__main__": 
    distance = 3
    err_vals = [1,0,0,0,0,0,0,0,0]

    packed_x, packed_z = formulagen_testing(distance)
    print(seq_cond_checker_testing(packed_x, packed_z, err_vals))