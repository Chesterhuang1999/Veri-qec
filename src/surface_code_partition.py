import sys
from condition_gen import stab_cond_gen, surface_matrix_gen, program_gen, decode_cond_gen
from verifier import precond_generator
from encoder import tree_to_z3, const_errors_to_z3, VCgeneration
from z3 import *
from timebudget import timebudget 
import cvc5
from itertools import combinations
import math
sys.setrecursionlimit(1000000)
### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   

# @timebudget
def smtencoding(precond, program, postcond, err_cond, err_gt, err_vals, decoder_cond, bit_width):
    
    # print(cass_expr)
    err_vals_tree, _, _ = precond_generator('skip', err_vals, err_cond)
    variables = {}
    constraints = []
    const_errors_to_z3(err_vals_tree.children[0], variables)
    # print(variables)
    
    cass_tree = VCgeneration(precond, program, postcond)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)
    
    # print(f'cass_expr: {cass_expr}')
    # print(f'cass_tree: {cass_tree}')
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True)
    # err_expr = simplify(err_expr)
    # print(err_expr)
    err_gt_tree, _, _ = precond_generator('skip', err_gt, err_cond)
    err_gt_expr = tree_to_z3(err_gt_tree.children[0], variables, bit_width, [], False)
    # err_gt_expr = simplify(err_gt_expr)
    # print(err_gt_expr)
    
    #err_expr = simplify(tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True))
    #decoder_variables = {}
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr)
    #decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True))

    #decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],decoder_variables, bit_width))
    #var_list = [var for var in list(decoder_variables.values()) if var not in list(err_variables.values())]
    
    #print(err_gt_expr)
    vaux_list, verr_list, vdata_list = [], [], []
    # print(assigned_errs)
    for name, var in variables.items():
        if var.size() == 1:
            sym, ind = name.split('_')
            if(sym[0] != 'e'):
                vdata_list.append(var)
            elif not is_bv_value(var):
                verr_list.append(var)
        else:
            vaux_list.append(var)

    var_list = vaux_list + vdata_list
    # print(var_list)
    # print(vdata_list)
    # print(verr_list)
    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)
    
    #decoding_formula = simplify(And(cass_expr, decoder_expr))
    substitution = And(*constraints)
    #formula_to_check = ForAll(var_list,  Or(Not(substitution), And(err_expr, Not(decoding_formula))))
    #formula_to_check = ForAll(verr_list, Exists(var_list, And(substitution, Or(Not(err_expr), decoding_formula))))
    #formula_to_check = ForAll(verr_list, Exists(var_list, Implies(err_gt_expr, And(substitution, Or(Not(err_expr), decoding_formula)))))
    #formula_to_check = ForAll(verr_list, And(substitution, Implies(err_expr, decoding_formula)))

    ## SMT formula I: If #error <= max_err, then decoding formula is true
    formula_to_check = ForAll(verr_list, 
                              Exists(var_list, 
                                     Or(Not(err_gt_expr), 
                                        And(substitution, 
                                            Or(Not(err_expr), decoding_formula)))))
    ## SMT formula II: If #error > max_err, then no satisfiable decoding formula
    # formula_to_check = ForAll(vdata_list,
    #                           Exists(vaux_list,
    #                           And(Not(err_expr), err_gt_expr, 
    #                               substitution, Not(decoding_formula))))
    # print(formula_to_check)
    # Slow
    # formula_to_check = simplify(formula_to_check)
    # formula_to_check = ForAll(verr_list, 
    #                           Exists(var_list, 
    #                                  And(err_vals_expr, substitution, 
    #                                      Or(Not(err_expr), decoding_formula)
    #                                  )
    #                           )
    #                    )
    # 
    # print(formula_to_check)
    # with open("temp.txt", "w") as f:
    #     f.write(str(formula_to_check))
    # exit(0)
    return formula_to_check


# @timebudget 
def smtchecking(formula):
    #t = Tactic('solve-eqs')
    solver = Solver()
    solver.add(formula)
    # var_list = formula.get_vars()
    # print(var_list)
    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic BV)\n" + "\n".join(lines[1:])
    # with open("formula.smt2", "w") as f:
    #     f.write(str(formula_smt2))
    # exit(0)
    # tm = cvc5.TermManager()

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
    
    # if r.isSat():
    #     model = s2.getModel([],[])
    # print(model)
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

    err_val_exprs_x = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    err_val_exprs_str_x = ' && '.join(err_val_exprs_x)

    err_val_exprs_z = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    err_val_exprs_str_z = ' && '.join(err_val_exprs_z)
    
    program_x, program_z = program_gen(surface_mat, num_qubits, 1)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance)
    formula_x = smtencoding(precond_x, program_x, postcond_x, 
                            err_cond_x, err_gt_x, err_val_exprs_str_x,
                            decoder_cond_x, bit_width)
    # formula_z = smtencoding(precond_z, program_z, postcond_z, 
    #                         err_cond_z, err_gt_z, decoder_cond_z, bit_width)
    result_x = smtchecking(formula_x)
    # result_z = smtchecking(formula_z)
    # print(result_x)
    return result_x
    # print(result_x, result_z)

@timebudget
def sur_cond_checker(distance, enum_qubit):
    counter = 0
    # assert(enum_qubit <= distance)
    num_qubits = distance ** 2
    if enum_qubit > num_qubits:
        enum_qubit = num_qubits
    
    # if enum_qubit < distance:
    #     enum_qubit = distance
    
    # enum_qubit \in [1, d ^ 2]
    # one_num <= enum
    # error number:
    # [1, distance) [1, enum_qubit + 1)

    err_vals = [0 for _ in range(enum_qubit)]
    seq_cond_checker(distance, err_vals)
    for one_num in range(1, min(distance, enum_qubit + 1)):
        for pos in combinations(range(enum_qubit), one_num):
            # print(pos)
            err_vals = [0 for _ in range(enum_qubit)]
            for j in pos:
                err_vals[j] = 1
            # print(err_vals)
            seq_cond_checker(distance, err_vals)

# def sur_cond_checker_alt(num_qubits, enum_qubit):
#     counter = 0
#     # assert(enum_qubit <= distance)
#     # num_qubits = distance ** 2
#     if enum_qubit > num_qubits:
#         enum_qubit = num_qubits

#     err_vals = [0 for _ in range(enum_qubit)]
#     if num_qubits > enum_qubit + distance:
#         seq_cond_checker(num_qubits - enum_qubit, err_vals)

#     for one_num in range(1, min(distance, enum_qubit + 1)):
#         for pos in combinations(range(enum_qubit), one_num):
#             # print(pos)
#             err_vals = [0 for _ in range(enum_qubit)]
#             for j in pos:
#                 err_vals[j] = 1
#             # print(err_vals)
#             seq_cond_checker(distance, err_val)
# (1 + t) ^ (d^2) <
# < d
# 0 * '1' -> 1 * '1' -> 2 * '1' -> 
# Debug

if __name__ == '__main__':
    # sur_cond_checker(3, 1)
    sur_cond_checker(5, 4)
    # seq_cond_checker(7, [0 for i in range(24)])
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