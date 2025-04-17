
from condition import surface_matrix_gen, stab_cond_gen, decode_cond_gen, program_gen
from smt_partition_merge import cond_generator, smtchecking
from verifier import precond_generator
from encoder import tree_to_z3, VCgeneration
from z3 import *
from timebudget import timebudget 
import time
import numpy as np

def program_gen_ser(H, n, k):   
    prog_parts = []
    prog_parts.append(f"for i in 1 to {n} do q_(i) *= ex_(i) X end; ")
    prog_parts.append(f"for i in 1 to {n} do q_(i) *= ez_(i) Z end; ")
    for i in range(n - k):
        if (np.all(H[i,:n] == 0) == False):
            prog_parts.append(f"s_({i + 1}) := meas")
            for j in range(n):
                if H[i][j] == 1:
                    prog_parts.append(f"(0,1,{j + 1})")
            prog_parts.append("; ")
        if (np.all(H[i,n:] == 0) == False):
            prog_parts.append(f"s_({i + 1}) := meas")
            for j in range(n):
                if H[i][j + n] == 1:
                    prog_parts.append(f"(1,0,{j + 1})")
            prog_parts.append(";")
    prog_parts.append(f"for i in 1 to {n} do q_(i) *= cx_(i) X end; ")
    prog_parts.append(f"for i in 1 to {n} do q_(i) *= cz_(i) Z end")
    return ''.join(prog_parts)

def smtencoding_serial(bit_width, precond, program, postcond, err_cond, err_gt, decoder_cond):
    variables = {}
    constraints = []
    ## generated from phases of stabilizers
    cass_tree = VCgeneration(precond, program, postcond)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)
    # print(cass_expr)
    ## The assumed condition for correctable errors
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True)
    err_gt_tree, _, _ = precond_generator('skip', err_gt, err_cond)
    err_gt_expr = tree_to_z3(err_gt_tree.children[0], variables, bit_width, [], False)
    ### Generate decoder's condition
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr) 
   
    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)

    substitution = And(*constraints)
    ### Not( err_gt_expr => And(substitution, err_expr => decoding_formula))
    ## Substitution is auxiliary, introduced to simplify summation
    
    formula = Or(Not(err_gt_expr), And(substitution, 
            Or(Not(err_expr), decoding_formula)))
    
    return formula, variables, constraints

def cond_generator_serial(matrix, dx, dz, is_discrete, is_sym = False):
    num_qubits = matrix.shape[1] // 2

    ez_max = (dz - 1) // 2
    ex_max = (dx - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    k = matrix.shape[0] - num_qubits
   
    precond_x, precond_z = stab_cond_gen(matrix, num_qubits, k)
    precond = precond_x + " && " + precond_z
    ## The correctable threshold determined by the supposed code distance.
    err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {ex_max}"
    err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {ez_max}"
    err_cond = err_cond_x + " && " + err_cond_z
    err_gt_z = f"sum i 1 {num_qubits} (ex_(i)) <= {2 * ex_max}"
    err_gt_x = f"sum i 1 {num_qubits} (ez_(i)) <= {2 * ez_max}" 
    err_gt = err_gt_x + " && " + err_gt_z
    ## Generate initial hoare triple without error condition 
    postcond = precond 
    
    program = program_gen_ser(matrix, num_qubits, k)
    ## Generate Decoder condition
    decoder_cond_x, decoder_cond_z = decode_cond_gen(matrix, num_qubits, k, dx, dz, 'verify')
    decoder_cond = decoder_cond_x + " && " + decoder_cond_z

    ## Generate the SMT encoding
    packed_expr = smtencoding_serial(bit_width, precond, program, postcond, err_cond,err_gt, decoder_cond)
    
    
    return packed_expr
    
## check surface code serially ##
def serial_cond_checker(distance):
    t1 = time.time()
    matrix = surface_matrix_gen(distance)
    packed_expr = cond_generator_serial(matrix, distance, distance, False, False)
    expr, variables, constraints = packed_expr
    vaux_list, verr_list, vdata_list = [], [], []
    # Collect all variables and select the 
    # syndromes as bounded variables, errors as existential variables
    for name, var in variables.items():
        if var.size() == 1:
            sym, _ = name.split('_')
            if(sym[0] not in ('e','p')):
                vdata_list.append(var)
            else:
                verr_list.append(var)
        else:
            vaux_list.append(var)
    var_list = vaux_list + vdata_list
    ## Include quantifiers to the expression
    formula_to_check = ForAll(var_list, Not(expr))
    
    result = smtchecking(formula_to_check)  
    if result == sat:
        print("The assertion is not correct!")
    else:
        print("No counterexample found, all errors can be corrected.")
    t2 = time.time()
    return t2 - t1, result



if __name__ == "__main__":
    t1 = time.time()
    d = 7
    matrix = surface_matrix_gen(d)
    
    print(serial_cond_checker(d))

    t2 = time.time()
    print(t2 - t1)