import sys
from data import *
from verifier import *
from encoder_z3 import tree_to_z3
from z3 import *
import matplotlib.pyplot as plt
from timebudget import timebudget 
import cvc5
sys.setrecursionlimit(1000000)
### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   

@timebudget
def smtencoding(precond, program, postcond, err_cond, err_vals, decoder_cond, bit_width):
    
    cass_expr = simplify(VCgeneration(precond, program, postcond))
    #print(cass_expr)
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_vals_tree, _, _ = precond_generator('skip', err_vals, err_cond)
    #err_variables = {}
    variables = {}
    constraints = []
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True)
    assigned_errs = {}
    err_vals_expr = tree_to_z3(err_vals_tree.children[0], assigned_errs, bit_width,  [], False)
    
    #err_expr = simplify(tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True))
    #decoder_variables = {}
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    #decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True))

    #decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],decoder_variables, bit_width))
    #var_list = [var for var in list(decoder_variables.values()) if var not in list(err_variables.values())]
    
    constraints.append(err_vals_expr)
    
    #print(err_gt_expr)
    vaux_list, verr_list, vdata_list = [], [], []
    # print(assigned_errs)
    for name, var in variables.items():
        if var.size() == 1:
            sym, ind = name.split('_')
            if(sym[0] != 'e'):
                vdata_list.append(var)
            else:
                if name not in assigned_errs:
                    verr_list.append(var)
                else:
                    vdata_list.append(var)
        else:
            vaux_list.append(var)

    var_list = vaux_list + vdata_list
    # print(var_list)
    # print(vdata_list)
    # print(verr_list)
    decoding_formula = And(cass_expr, decoder_expr)
    #decoding_formula = simplify(And(cass_expr, decoder_expr))
    substitution = And(*constraints)

    #formula_to_check = ForAll(var_list,  Or(Not(substitution), And(err_expr, Not(decoding_formula))))
    #formula_to_check = ForAll(verr_list, Exists(var_list, And(substitution, Or(Not(err_expr), decoding_formula))))
    #formula_to_check = ForAll(verr_list, Exists(var_list, Implies(err_gt_expr, And(substitution, Or(Not(err_expr), decoding_formula)))))
    # formula_to_check = ForAll(verr_list, Exists(var_list, Or(Not(err_gt_expr), And(substitution, Or(Not(err_expr), decoding_formula)))))
    #formula_to_check = ForAll(verr_list, And(substitution, Implies(err_expr, decoding_formula)))
    formula_to_check = ForAll(verr_list, Exists(var_list, And(err_vals_expr, substitution, Or(Not(err_expr), decoding_formula))))
    # 
    #print(formula_to_check)
    #print(formula_to_check)
    return formula_to_check


@timebudget 
def smtchecking(formula):
    #t = Tactic('solve-eqs')
    solver = Solver()
    solver.add(formula)
    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic BV)\n" + "\n".join(lines[1:])
    with open("formula.smt2", "w") as f:
        f.write(str(formula_smt2))
    tm = cvc5.TermManager()
    s2 = cvc5.Solver()
    s2.setOption('produce-models', 'true')  
    cvc5_parser = cvc5.InputParser(s2)

    cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

    sm = cvc5_parser.getSymbolManager()
    while True:
        cmd = cvc5_parser.nextCommand()
        if cmd.isNull():
            break
        cmd.invoke(s2, sm)
    
    r = s2.checkSat()
    
    print(r)
    return r

def seq_cond_checker(distance, err_vals):
    num_qubits = distance**2
    max_errors = (distance - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    max_errors = (distance - 1) // 2 
    surface_mat = surface_matrix_gen(distance)
    precond_x, precond_z = stab_cond_gen(surface_mat, num_qubits, 1) 
    #precond, cond2, x_inds, z_inds = surface(distance, 1)
    err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {max_errors}"
    err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {max_errors}"
    err_gt_z = f"sum i 1 {num_qubits} (ex_(i)) <= {distance - 1}"
    err_gt_x = f"sum i 1 {num_qubits} (ez_(i)) <= {distance - 1}"
    postcond_x, postcond_z = precond_x, precond_z
    err_val_exprs = []
    for i in range(len(err_vals)):
        if i > 0:
            err_val_exprs.append('&&')
        err_val_exprs.append(f'(ez_({i + 1})) == {err_vals[i]}')
    err_val_exprs_str = ' '.join(err_val_exprs)
    
    #program = surface_program(distance,x_inds,z_inds)
    program_x, program_z = program_gen(surface_mat, num_qubits, 1)
    #decoder_cond = sur_decode_gen(x_inds, z_inds)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance)
    formula_x = smtencoding(precond_x, program_x, postcond_x, 
                            err_cond_x, err_val_exprs_str, decoder_cond_x, bit_width)
    # formula_z = smtencoding(precond_z, program_z, postcond_z, err_cond_z, err_gt_z, decoder_cond_z, bit_width)
    result_x = smtchecking(formula_x)
    # result_z = smtchecking(formula_z)

@timebudget
def sur_cond_checker(distance, enum_bit):
    counter = 0
    # assert(enum_bit <= distance)
    num_qubits = distance**2
    if enum_bit > num_qubits:
        enum_bit = num_qubits
    mask = 2**enum_bit
    # for err_mask in range(3):
    for err_mask in range(mask):
        err_vals = []
        sum = 0
        for i in range(enum_bit):
            bit = (err_mask >> i) & 1
            err_vals.append(bit)
            sum += bit
        if sum >= distance:
            continue
        counter += 1
        
        seq_cond_checker(distance, err_vals)

encode_time = []
check_time = []

# (1 + t) ^ (d^2) <
# < d
# 0 * '1' -> 1 * '1' -> 2 * '1' -> 
# Debug

# seq_cond_checker(7, [0 for i in range(24)])
sur_cond_checker(7, 24)


#print(encode_time, check_time) 
# x = [2*i+1 for i in range(1, 5)]
# # #x.append(25)
# for i in x:
#     sur_cond_checker(i, encode_time, check_time)

# plt.plot(x, encode_time, label = "Encoding Time"
# plt.plot(x, check_time, label = "Checking Time")
# plt.xlabel('Code Distance')
# plt.ylabel('Time (s)')
# plt.title('Surface Code Verification Time')
# plt.legend()
# plt.savefig('surface_9.png')