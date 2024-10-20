import sys
from condition import *
from verifier import *
from encoder import tree_to_z3
from z3 import *
import matplotlib.pyplot as plt
from timebudget import timebudget 

sys.setrecursionlimit(100000)
@timebudget
def sur_cond_checker(distance):
    t1 = time.time()
    num_qubits = distance**2
    max_errors = (distance - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    max_errors = (distance - 1) // 2 
    surface_mat = surface_matrix_gen(distance)
    precond = stab_cond_gen(surface_mat, num_qubits, 1) 
    #precond, cond2, x_inds, z_inds = surface(distance, 1)
    err_cond = f"sum i 1 {num_qubits} (ex_(i)) <= {max_errors} && sum i 1 {num_qubits} (ez_(i)) <= {max_errors}"
    postcond = precond
    #program = surface_program(distance,x_inds,z_inds)
    program = program_gen(surface_mat, num_qubits, 1)
    #decoder_cond = sur_decode_gen(x_inds, z_inds)
    decoder_cond = decode_cond_gen(surface_mat, num_qubits, 1)

    cass_expr = simplify(VCgeneration(precond, program, postcond))
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_variables = {}
    err_expr = simplify(tree_to_z3(err_tree.children[0], err_variables, bit_width))
    decoder_variables = {}
    decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],decoder_variables, bit_width))
    name_list = list(decoder_variables.keys())
    vsyn_list = []
    verr_list = []
    vcorr_list = []
    for name in name_list:
        sym, ind = name.split('_')
        if sym[0] == 's':
            vsyn_list.append(decoder_variables[name])
        elif sym[0] == 'c':
            vcorr_list.append(decoder_variables[name])
        else:
            verr_list.append(decoder_variables[name])
    var_list = [var for var in list(decoder_variables.values()) if var not in list(err_variables.values())]
    #print(simplify(And(cass_expr, decoder_expr)))
    #print(decoder_expr)
    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)
    solver = Solver()
    formula_to_check = ForAll(var_list, And(err_expr, Not(decoding_formula)))
    #print(formula_to_check)
    solver.add(formula_to_check)
    t2 = time.time()
    print(t2 - t1)
    if solver.check() == sat:
        print("The assertion is not correct!")
        print("Counterexample: ", solver.model())
    else:
        print("The assertion is correct!")
    t3 = time.time()
    print(t3 - t2)

@timebudget
def rep_cond_check(n):
    k = 1
    max_errors = (n - 1) // 2
    bit_width = int(math.log2(n)) + 1
    precond = rep_cond(n, k)
    postcond = rep_cond(n,k)
    program = rep_program(n)
    err_cond = f"sum i 1 {n} (e_(i)) <= {max_errors}"
    H = np.zeros((n, 2*n), dtype = int)
    for i in range(n - k):
        H[i][i] = 1
        H[i][i + 1] = 1
    print(H)
    decoder_cond = decode_cond_gen(H, n, k)
    cass_expr = simplify(VCgeneration(precond, program, postcond))
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_variables = {}
    err_expr = tree_to_z3(err_tree.children[0], err_variables, bit_width)
    decoder_variables = {}
    decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],decoder_variables, bit_width))
    name_list = list(decoder_variables.keys())
    print(cass_expr)
    print(err_expr)
    print(decoder_expr)

#rep_cond_check(5)
sur_cond_checker(5)