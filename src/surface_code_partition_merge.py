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
def smtencoding_constrep(exprs, variables, constraints, err_vals):
    cass_expr, decoder_expr, err_expr, err_gt_expr, sym_expr = exprs
    err_vals_tree, _, _ = precond_generator('skip', err_vals, 'true')
    consts = {}
    const_errors_to_z3(err_vals_tree.children[0], consts)
    replace = []
    for i, ki in enumerate(consts.keys()):
        replace.append((variables[ki], consts[ki]))
        
    cass_expr = simplify(substitute(cass_expr, replace))

    decoder_expr = simplify(substitute(decoder_expr, replace))
    err_expr = substitute(err_expr, replace)
    
    err_gt_expr = substitute(err_gt_expr, replace)
    #constraints = simplify(substitute(constraints ,replace))
    sym_expr = simplify(substitute(sym_expr, replace))
    substitution = And(*constraints)
    substitution = simplify(substitute(substitution, replace))
    decoding_formula = And(cass_expr, decoder_expr)
    # print(substitution)
    vaux_list, verr_list, vdata_list = [], [], []
    for name, var in variables.items():
        if var.size() == 1:
            sym, _ = name.split('_')
            if(sym[0] != 'e'):
                vdata_list.append(var)
            elif name not in consts.keys():
                verr_list.append(var)
        else:
            vaux_list.append(var)

    var_list = vaux_list + vdata_list
    # print(verr_list)
    # print(sym_expr)
    # print(var_list)
    ## SMT encoding
    ## SMT formula I: If #error <= max_err, then decoding formula is true
    formula_to_check = ForAll(verr_list, 
                           Exists(var_list, 
                                      Or(Not(err_gt_expr), 
                                         And(substitution, 
                                             Or(Not(err_expr), Not(sym_expr), decoding_formula)
                                             ))))
    
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
def smtencoding(precond, program, postcond, err_cond, err_gt, decoder_cond, sym_cond, bit_width):

    # err_vals_tree, _, sym_tree  = precond_generator('skip', err_vals, sym_cond)
    sym_tree, _, _  = precond_generator('skip', sym_cond, 'true')
    variables = {}
    constraints = []
    # const_errors_to_z3(err_vals_tree.children[0], variables)
    cass_tree = VCgeneration(precond, program, postcond)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)
    # print(f'err_cond: {err_cond}')
    # print(f'decoder_cond: {decoder_cond}')
    
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True)
    
    # err_expr = simplify(err_expr)

    err_gt_tree, _, _ = precond_generator('skip', err_gt, err_cond)
    err_gt_expr = tree_to_z3(err_gt_tree.children[0], variables, bit_width, [], False)
    # err_gt_expr = simplify(err_gt_expr)
    
    #err_expr = simplify(tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True))
    #decoder_variables = {}
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr)
    
    #decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True))

    #var_list = [var for var in list(decoder_variables.values()) if var not in list(err_variables.values())]

    # decoding_formula = And(cass_expr, decoder_expr)
    # decoding_formula = simplify(decoding_formula)

    # substitution = And(*constraints)
    #formula_to_check = ForAll(var_list,  Or(Not(substitution), And(err_expr, Not(decoding_formula))))
 
    #formula_to_check = ForAll(verr_list, Exists(var_list, Implies(err_gt_expr, And(substitution, Or(Not(err_expr), decoding_formula)))))


    ##/* symmetrization */##
    sym_expr = tree_to_z3(sym_tree.children[0], variables, bit_width, [], False)
    
    ##/hqf 9.24 / ## 
    exprs = [cass_expr, decoder_expr, err_expr, err_gt_expr, sym_expr]

    return exprs, variables, constraints
  


# @timebudget 
def smtchecking(formula):
    #t = Tactic('solve-eqs')
    solver = Solver()
    solver.add(formula)
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
    
    # if r.isSat():
    #     model = s2.getModel([],[])
    # print(model)
    return r
def coord_to_index(x, y, distance):
    return x * distance + y
def sym_gen(n):
    groups = defaultdict(list)
    mid = n // 2
    for i in range(mid):
        for j in range(n):
            sind = coord_to_index(i, j, n)
            groups[sind] = [sind, coord_to_index(n - 1 - i, n - 1 - j, n)]
    for j in range(mid):
        sind = coord_to_index(mid, j, n)
        groups[sind] = [sind, coord_to_index(mid, n - 1 - j, n)]
    sym_x, sym_z = [], []
    for value in groups.values():
        k, l = value[0], value[1]
        sym_x.append(f"ez_({k + 1}) <= ez_({l + 1})")
        sym_z.append(f"ex_({k + 1}) <= ex_({l + 1})")
    sym_x, sym_z = '&&'.join(sym_x), '&&'.join(sym_z)
    return sym_x, sym_z



def cond_generator(distance):
    num_qubits = distance**2
    max_errors = (distance - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    max_errors = (distance - 1) // 2 
    surface_mat = surface_matrix_gen(distance)
    precond_x, precond_z = stab_cond_gen(surface_mat, num_qubits, 1)
    #precond, cond2, x_inds, z_inds = surface(distance, 1)
    #err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {max_errors}"
    #err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {max_errors}"
    err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {max_errors}"
    err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {max_errors}"
    err_gt_z = f"sum i 1 {num_qubits} (ex_(i)) <= {distance - 1}"
    err_gt_x = f"sum i 1 {num_qubits} (ez_(i)) <= {distance - 1}"
    postcond_x, postcond_z = precond_x, precond_z

    # err_val_exprs_x = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    # err_val_exprs_str_x = ' && '.join(err_val_exprs_x)

    # err_val_exprs_z = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    # err_val_exprs_str_z = ' && '.join(err_val_exprs_z)
    
    program_x, program_z = program_gen(surface_mat, num_qubits, 1)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance)
    sym_x, sym_z = sym_gen(distance)
   

    # cond_x = [precond_x, program_x, postcond_x, 
    #                         err_cond_x, err_gt_x, decoder_cond_x, sym_x]
    # cond_z = [precond_z, program_z, postcond_z, 
    #                         err_cond_z, err_gt_z, decoder_cond_z, sym_z]
    packed_x = smtencoding(precond_x, program_x, postcond_x, 
                            err_cond_x, err_gt_x, 
                            decoder_cond_x, sym_x, bit_width)
    packed_z = smtencoding(precond_z, program_z, postcond_z, 
                            err_cond_z, err_gt_z, 
                            decoder_cond_z, sym_z, bit_width)
    
    return packed_x, packed_z


def seq_cond_checker(packed_x, packed_z, err_vals):
    # precond_x, program_x, postcond_x, err_cond_x, err_gt_x, decoder_cond_x, sym_x = cond_x
    # precond_z, program_z, postcond_z, err_cond_z, err_gt_z, decoder_cond_z, sym_z = cond_z
    t2 = time.time()
    err_val_exprs_x = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    err_val_exprs_str_x = ' && '.join(err_val_exprs_x)

    err_val_exprs_z = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    err_val_exprs_str_z = ' && '.join(err_val_exprs_z)
    # packed_x, packed_z = cond_generator(distance)
    exprs_x, variables_x, constraints_x = packed_x
    
    exprs_z, variables_z, constraints_z = packed_z
    formula_x = smtencoding_constrep(exprs_x, variables_x, constraints_x,
                                      err_val_exprs_str_x)
    formula_z = smtencoding_constrep(exprs_z, variables_z, constraints_z,                    
                                      err_val_exprs_str_z)
    # print(formula_x)
    # formula_x = smtencoding(precond_x, program_x, postcond_x, 
    #                         err_cond_x, err_gt_x, err_val_exprs_str_x,
    #                         decoder_cond_x, sym_x, bit_width)\
    # formula_z = smtencoding(precond_z, program_z, postcond_z, 
    #                         err_cond_z, err_gt_z, err_val_exprs_str_z, 
    #                         decoder_cond_z, sym_z, bit_width)
    t3 = time.time()
    result_x = smtchecking(formula_x)
    result_z = smtchecking(formula_z)
    t4 = time.time()
    # print(t4 - t3, t3 - t2)
    return t4 - t3, result_x, result_z




if __name__ == '__main__':
   
    distance = 7
    err_vals = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    #print(err_vals)
    packed_x, packed_z = cond_generator(distance)
    print(seq_cond_checker(packed_x, packed_z, err_vals))