import numpy as np
import time
import math
import sys
from lark import Lark, Transformer, Tree
from condition import * 
from verifier import *
from z3 import *
from multiprocessing import Pool
from timebudget import timebudget
import cvc5
from cvc5 import Kind
import matplotlib.pyplot as plt


sys.setrecursionlimit(1000000)
@timebudget
def surface_code_verifier(distance, encode_time):
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

    var_list = [var for var in list(decoder_variables.values()) if var not in list(err_variables.values())]
    decoding_formula = And(cass_expr, decoder_expr)
    # bzla = bitwuzla()
    solver = Solver()
    formula_to_check = ForAll(var_list, Not(Implies(err_expr, decoding_formula)))
    
    solver.add(formula_to_check)
    formula_smt = solver.to_smt2()
    t2 = time.time()
    encode_time.append(t2 - t1)
    # with open("formula.smt2", "w") as f:
    #     f.write(formula_smt)
    # tm = TermManager()
    # options = Options()
    # options.set(Option.PRODUCE_MODELS, True)
    # options.set(Option.SAT_SOLVER, 'cadical')
    # parser = Parser(tm, options) 
    # # # solver.add(formula_to_check)
    # res = parser.parse('formula.smt2')
    # assertions = parser.bitwuzla().get_assertions()

    # result = bzla.check_sat()
    # if result == Result.SAT:
    #     print("The assertion is not correct!")
    #     print("Counterexample: ", bzla.get_model())
    # else:
    #     print("The assertion is correct!")
    # if solver.check() == sat:
    #     print("The assertion is not correct!")
    #     print("Counterexample: ", solver.model())
    # else:
    #     print("The assertion is correct!")

encode_time = []
for i in range(1, 6):
    n = 2 * i + 1
    surface_code_verifier(n, encode_time)

x = [i for i in range(1, 6)]

plt.plot(x, encode_time, label = 'encode')
plt.legend()
plt.show()
# plt.savefig('surface_encode.png')