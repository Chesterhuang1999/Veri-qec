import sys
from condition import stab_cond_gen, surface_matrix_gen, program_gen, decode_cond_gen
from verifier import precond_generator
from encoder import tree_to_z3, const_errors_to_z3, VCgeneration
from z3 import *
from timebudget import timebudget 
import time
import cvc5
from itertools import combinations
import math
from collections import defaultdict
import argparse
import json

sys.setrecursionlimit(1000000)

### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   
def smtencoding_constrep(expr, variables, constraints, err_vals):
    
    # cass_expr, decoder_expr, err_expr, err_gt_expr, sym_expr = expr
    err_vals_tree, _, _ = precond_generator('skip', err_vals, 'true')
    consts = {}
    const_errors_to_z3(err_vals_tree.children[0], consts)
    replace = []
    for i, ki in enumerate(consts.keys()):
        replace.append((variables[ki], consts[ki]))
    
    expr = simplify(substitute(expr, replace))
    # print(expr)
    vaux_list, verr_list, vdata_list = [], [], []
    # print(variables)
    for name, var in variables.items():
        if var.size() == 1:
            sym, _ = name.split('_')
            
            if(sym[0] not in ('e','p')):
                vdata_list.append(var)
            elif name not in consts.keys():
                verr_list.append(var)
        else:
            vaux_list.append(var)
    # print(verr_list)
    var_list = vaux_list + vdata_list
    # print(expr)
    ## SMT encoding
    ## SMT formula I: If #error <= max_err, then decoding formula is true
    # formula_to_check = ForAll(verr_list, 
    #                        Exists(var_list, 
    #                                   Or(Not(err_gt_expr), 
    #                                      And(substitution, 
    #                                          Or(Not(err_expr), Not(sym_expr), decoding_formula)
    #                                          ))))
    # formula_to_check = ForAll(verr_list, Exists(var_list, expr))
    # print(expr)
    formula_to_check = ForAll(var_list, Not(expr))
    # formula_to_check = expr
    # print(formula_to_check)
    ## SMT formula II: If #error > max_err, then no satisfiable decoding formula
    # formula_to_check = ForAll(vdata_list,
    #                           Exists(vaux_list,
    #                           And(Not(err_expr), err_gt_expr, 
    #                               substitution, Not(decoding_formula))))
    # print(formula_to_check)

    ## SMT formula III: Encode both directions together
    #formula_to_check = ForAll(verr_list, 
    #                        Exists(var_list, 
    #                            Or(Not(err_gt_expr), 
    #                                And(substitution, 
    #                                    Or(Not(err_expr), decoding_formula),
    #                                    Or(err_expr, Not(decoding_formula))
    #                                        ))))

    ## SMT formula IV: Apply symmetry condition
    # formula_to_check = ForAll(verr_list, 
    #                      Exists(var_list, 
    #                            Or(Not(err_gt_expr), 
    #                                And(substitution,
    #                                    Or(Not(err_expr), Not(sym_expr), decoding_formula),
    #                                    Or(And(err_expr, sym_expr), Not(decoding_formula))
    #                                        )))) 
    return formula_to_check
# @timebudget
def smtencoding(bit_width, precond, program, postcond, err_cond, err_gt, decoder_cond, sym_cond = None):

    variables = {}
    constraints = []
    # const_errors_to_z3(err_vals_tree.children[0], variables)
    cass_tree = VCgeneration(precond, program, postcond)
    # print(cass_tree)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)

    # print(cass_expr)    
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True)
    
    err_gt_tree, _, _ = precond_generator('skip', err_gt, err_cond)
    err_gt_expr = tree_to_z3(err_gt_tree.children[0], variables, bit_width, [], False)
    
    # print(err_expr)
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr) 
    # print(decoder_expr)
    # exit(0)
    
    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)

    substitution = And(*constraints)
    
    ##/* symmetrization */##
    ##/hqf 10.03 / ## 

    if sym_cond != None:
        sym_tree, _, _  = precond_generator('skip', sym_cond, 'true')
        sym_expr = tree_to_z3(sym_tree.children[0], variables, bit_width, [], False)
    
        formula = Or(Not(err_gt_expr), And(substitution, 
                Or(Not(err_expr), Not(sym_expr), decoding_formula)))
    
    else:
        formula = Or(Not(err_gt_expr), And(substitution, 
                Or(Not(err_expr), decoding_formula)))


    return formula, variables, constraints
  
# @timebudget 
def smtchecking(formula):
    #t = Tactic('solve-eqs')
    solver = SolverFor('QF_BV')
    solver.add(formula)
    # r = solver.check()

    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic BV)\n" + "\n".join(lines[1:])

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
    err = []
    if str(r) == 'sat':
        vars = sm.getDeclaredTerms()
        res_lines = (s2.getModel([], vars)).decode('utf-8').splitlines()[1:-1]
        # print(res_lines)

        for i, line in enumerate(res_lines):
            # print(line)
            if(line[-2] == '1'):
                elems = line.split(' ')
                # print(elems)
                err.append(elems[1])
        # print(err)
        return r, err
    # if r.isSat():
    #     model = s2.getModel([],[])
    # print(model)
    return r, []
def coord_to_index(x, y, distance):
    return x * distance + y
def sym_gen(dx, dz):
    groups = defaultdict(list)
    midx = dx // 2
    midz = dz // 2
    for i in range(midx):
        for j in range(dz):
            sind = coord_to_index(i, j, dz)
            groups[sind] = [sind, coord_to_index(dx - 1 - i, dz - 1 - j, dz)]
    for j in range(midz):
        sind = coord_to_index(midx, j, dz)
        groups[sind] = [sind, coord_to_index(midx, dz - 1 - j, dz)]
    sym_x, sym_z = [], []
    for value in groups.values():
        k, l = value[0], value[1]
        sym_x.append(f"ez_({k + 1}) <= ez_({l + 1})")
        sym_z.append(f"ex_({k + 1}) <= ex_({l + 1})")
    sym_x, sym_z = '&&'.join(sym_x), '&&'.join(sym_z)
    return sym_x, sym_z



def cond_generator(matrix, dx, dz, is_discrete, is_sym = False):
    num_qubits = matrix.shape[1] // 2
    # begin_x, length_x, _ = info_x
    # begin_z, length_z, _ = info_z
    slice_x = num_qubits // dx
    slice_z = num_qubits // dz

    ez_max = (dz - 1) // 2
    ex_max = (dx - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    k = matrix.shape[0] - num_qubits
    # surface_mat = surface_matrix_gen(distance)
    # precond_x, precond_z = stab_cond_gen(surface_mat, num_qubits, 1)
    precond_x, precond_z = stab_cond_gen(matrix, num_qubits, k)

    err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {ex_max}"
    err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {ez_max}"
    err_gt_z = f"sum i 1 {num_qubits} (ex_(i)) <= {2 * ex_max}"
    err_gt_x = f"sum i 1 {num_qubits} (ez_(i)) <= {2 * ez_max}"
    if is_discrete == True:
        for i in range(slice_z):
            start = i * dz + 1
            if start + dz - 1 <= num_qubits:
                err_gt_x += f" && sum i {start} {start + dz - 1} (ez_(i)) <= 1"
            else:
            # elif start <= num_qubits:
                err_gt_x += f" && sum i {start} {num_qubits} (ez_(i)) <= 1"

        for i in range(slice_x):
            start = i * dx + 1
            if start + dx - 1 <= num_qubits:
                err_gt_z += f" && sum i {start} {start + dx - 1} (ex_(i)) <= 1"
            else:
            # elif start <= num_qubits:
                err_gt_z += f" && sum i {start} {num_qubits} (ex_(i)) <= 1"
    # print(err_gt_x, err_gt_z)
    postcond_x, postcond_z = precond_x, precond_z

    # err_val_exprs_x = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    # err_val_exprs_str_x = ' && '.join(err_val_exprs_x)

    # err_val_exprs_z = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    # err_val_exprs_str_z = ' && '.join(err_val_exprs_z)
    
    # program_x, program_z = program_gen(surface_mat, num_qubits, 1)
    # decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance, 'verify')
    program_x, program_z = program_gen(matrix, num_qubits, k)
    
    decoder_cond_x, decoder_cond_z = decode_cond_gen(matrix, num_qubits, k, dx, dz, 'verify')

    sym_x, sym_z = None, None
    if is_sym:
        sym_x, sym_z = sym_gen(dx, dz)
    
    packed_x = smtencoding(bit_width, precond_x, program_x, postcond_x, 
                            err_cond_x, err_gt_x, 
                            decoder_cond_x, sym_x)
    packed_z = smtencoding(bit_width, precond_z, program_z, postcond_z, 
                            err_cond_z, err_gt_z, 
                            decoder_cond_z, sym_z)
    
    return packed_x, packed_z

## A sequnential checker for logical operations without measurement error
def seq_cond_checker_logical(packed_expr, err_vals, p_vals, opt):
    t2 = time.time()
    expr, variables, constraints = packed_expr
    if opt == 'x':
        err_val_exprs = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        err_val_exprs.extend([f'(pz_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    else:
        err_val_exprs = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        err_val_exprs.extend([f'(px_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    
    err_val_exprs_str = ' && '.join(err_val_exprs)
    # print(err_val_exprs_str)
    formula = smtencoding_constrep(expr, variables, constraints, err_val_exprs_str)
    t3 = time.time()
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result

### A sequential checker for general property verification 
def seq_cond_checker(packed_expr, err_vals, opt):
    t2 = time.time()
    expr, variables, constraints = packed_expr
    if opt == 'x':
        err_val_exprs = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        # err_val_exprs.extend([f'(pz_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    else:
        
        ### Normal form ### 
        err_val_exprs = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        # err_val_exprs.extend([f'(px_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    
    err_val_exprs_str = ' && '.join(err_val_exprs)
    # print(err_val_exprs_str)
    
    formula = smtencoding_constrep(expr, variables, constraints, err_val_exprs_str)
    t3 = time.time()
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result


def seq_cond_checker_user(packed_expr, err_vals, info, opt):
    t2 = time.time()
    expr, variables, constraints = packed_expr
    err_set, free_set = info
    if opt == 'x':
        err_val_exprs = [f'ez_({i + 1}) == 0' for i in free_set]
        err_val_exprs.extend([f'cz_({i + 1}) == 0' for i in free_set])
        err_val_exprs.extend([f'ez_({err_set[i] + 1}) == {err_vals[i]}' for i in range(len(err_vals))])
    else:
        err_val_exprs = [f'ex_({i + 1}) == 0' for i in free_set]
        err_val_exprs.extend([f'cx_({i + 1}) == 0' for i in free_set])
        err_val_exprs.extend([f'ex_({err_set[i] + 1}) == {err_vals[i]}' for i in range(len(err_vals))])

    # print(err_set, free_set)
    # print(err_val_exprs)
    # exit(0)
    # if opt == 'x':
    #     err_val_exprs = [f'ez_({i + 1}) == 0' for i in range(begin)]
    #     err_val_exprs = [f'cz_({i + 1}) == 0' for i in range(begin)]
    #     err_val_exprs.extend([f'(ez_({i + 1 + begin})) == {err_vals[i]}' for i in range(len(err_vals))])
    #     err_val_exprs.extend([f'ez_({i + 1 + begin + length}) == 0' for i in range(numq - length - begin)])
    #     err_val_exprs.extend([f'cz_({i + 1 + begin + length}) == 0' for i in range(numq - length - begin)])
    # else:
    #     err_val_exprs = [f'ex_({i + 1}) == 0' for i in range(begin)]
    #     err_val_exprs = [f'cx_({i + 1}) == 0' for i in range(begin)]
    #     err_val_exprs.extend([f'(ex_({i + 1 + begin})) == {err_vals[i]}' for i in range(len(err_vals))])
    #     err_val_exprs.extend([f'ex_({i + 1 + begin + length}) == 0' for i in range(numq - length - begin)])
    #     err_val_exprs.extend([f'cx_({i + 1 + begin + length}) == 0' for i in range(numq - length - begin)])

    err_val_exprs_str = ' && '.join(err_val_exprs)

    formula = smtencoding_constrep(expr, variables, constraints, err_val_exprs_str)
    t3 = time.time()
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result

# def seq_cond_checker(packed_x, packed_z, err_vals):
    
#     t2 = time.time()
    
#     err_val_exprs_x = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
#     err_val_exprs_str_x = ' && '.join(err_val_exprs_x)

#     err_val_exprs_z = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
#     err_val_exprs_str_z = ' && '.join(err_val_exprs_z)

#     expr_x, variables_x, constraints_x = packed_x

#     expr_z, variables_z, constraints_z = packed_z
#     formula_x = smtencoding_constrep(expr_x, variables_x, constraints_x,
#                                     err_val_exprs_str_x)
#     formula_z = smtencoding_constrep(expr_z, variables_z, constraints_z,                    
#                                     err_val_exprs_str_z)

#     t3 = time.time()
#     result_x = smtchecking(formula_x)
#     result_z = smtchecking(formula_z)
#     t4 = time.time()
#     # print(t4 - t3, t3 - t2)
#     return t4 - t3, result_x, result_z




if __name__ == '__main__':
   
    distance = 3
    err_vals = [0,1,1]
    matrix = surface_matrix_gen(distance)
    #print(err_vals)
    packed_x, packed_z = cond_generator(matrix, distance, distance, True)
    print(seq_cond_checker(packed_z, err_vals, 'z'))
    # print(seq_cond_checker_part(packed_x, err_vals, 'x'))
    # print(seq_cond_checker_part(packed_z, err_vals, 'z'))
