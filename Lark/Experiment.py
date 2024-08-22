import numpy as np
import time
import math
import sys
from lark import Lark, Transformer, Tree
from data import * 
from verifier import *
from z3 import *
from multiprocessing import Pool
from timebudget import timebudget


sys.setrecursionlimit(1000000)
import bitwuzla
@timebudget
def surface_code_verifier(distance):
# distance = 5 
    t1 = time.time()
    num_qubits = distance**2
    bit_width = int(math.log2(num_qubits)) + 1 
    max_errors = (distance - 1) // 2
    surface_mat = surface_matrix_gen(distance)  
    precond = stab_cond_gen(surface_mat, num_qubits, 1) 
    postcond = precond
    program = program_gen(surface_mat, num_qubits, 1)
    err_cond = f"sum i 1 {num_qubits} (ex_(i)) <= {max_errors} && sum i 1 {num_qubits} (ez_(i)) <= {max_errors}"
    decoder_cond = decode_cond_gen(surface_mat, num_qubits, 1)

    cass_expr = VCgeneration(precond, program, postcond)
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_variables = {}
    err_expr = simplify(tree_to_z3(err_tree.children[0], err_variables, bit_width))
    decoder_variables = {}
    decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],decoder_variables, bit_width))

    t2 = time.time()
    var_list = [var for var in list(decoder_variables.values()) if var not in list(err_variables.values())]
    decoding_formula = And(cass_expr, decoder_expr)
    t3 = time.time()
    solver = Solver()
    print(t2 - t1, t3 - t2)
    solver.add(ForAll(var_list, Not(Implies(err_expr, decoding_formula))))

    if solver.check() == sat:
        print("The assertion is not correct!")
        print("Counterexample: ", solver.model())
    else:
        print("The assertion is correct!")


    