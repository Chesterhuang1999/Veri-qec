from encoder import *
from verifier import precond_generator
from z3 import *
import cvc5
from timebudget import timebudget

### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections  

# @timebudget
def smtencoding_parti(code, triple, err, decoder_cond, sym_cond, bit_width):
    
    precond, program, postcond = triple
    err_cond, err_gt, err_vals = err
    # print(precond, program, postcond, err_cond, err_gt, err_vals)
    err_vals_tree, _, sym_tree  = precond_generator('skip', err_vals, sym_cond)
    variables = {}
    constraints = []
    const_errors_to_z3(err_vals_tree.children[0], variables)

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

    vaux_list, verr_list, vdata_list = [], [], []
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

    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)

    substitution = And(*constraints)
    #formula_to_check = ForAll(var_list,  Or(Not(substitution), And(err_expr, Not(decoding_formula))))
 
    #formula_to_check = ForAll(verr_list, Exists(var_list, Implies(err_gt_expr, And(substitution, Or(Not(err_expr), decoding_formula)))))


    ##/* symmetrization */##
   
    # print(sym_expr)


    ##/hqf 9.24 / ## 

    ## SMT formula I: If #error <= max_err, then decoding formula is true
    # formula_to_check = ForAll(verr_list, 
    #                           Exists(var_list, 
    #                                  Or(Not(err_gt_expr), 
    #                                     And(substitution, 
    #                                         Or(Not(err_expr), decoding_formula)
    #                                         ))))
    
    ## SMT formula II: If #error > max_err, then no satisfiable decoding formula
    # formula_to_check = ForAll(vdata_list,
    #                           Exists(vaux_list,
    #                           And(Not(err_expr), err_gt_expr, 
    #                               substitution, Not(decoding_formula))))
    # print(formula_to_check)
    ## SMT formula IV: Apply symmetry condition
    if code == 'surface': 
        sym_expr = tree_to_z3(sym_tree.children[0], variables, bit_width, [], False)
        formula_to_check = ForAll(verr_list, 
                            Exists(var_list, 
                                Or(Not(err_gt_expr), 
                                    And(substitution, sym_expr, 
                                        Or(Not(err_expr), decoding_formula),
                                        Or(err_expr, Not(decoding_formula))
                                            )))) 
    ## SMT formula III: Encode both directions together
    else:

        formula_to_check = ForAll(verr_list, 
                                Exists(var_list, 
                                    Or(Not(err_gt_expr), 
                                        And(substitution, 
                                            Or(Not(err_expr), decoding_formula),
                                            Or(err_expr, Not(decoding_formula))
                                                ))))

        
    
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
    return formula_to_check


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

def coord_to_index(x, y, dx):
    return x * dx + y
def sym_gen(dx, dz):
    groups = defaultdict(list)
    midz = dz // 2
    midx = dx // 2
    for i in range(midz):
        for j in range(dx):
            sind = coord_to_index(i, j, dx)
            groups[sind] = [sind, coord_to_index(dz - 1 - i, dx - 1 - j, dx)]
    for j in range(midx):
        sind = coord_to_index(midz, j, dx)
        groups[sind] = [sind, coord_to_index(midz, dx - 1 - j, dx)]
    return groups
    # sym_x, sym_z = [], []
    # for value in groups.values():
    #     k, l = value[0], value[1]
    #     sym_x.append(f"ex_({k + 1}) <= ex_({l + 1})")
    #     sym_z.append(f"ez_({k + 1}) <= ez_({l + 1})")
    # sym_x, sym_z = '&&'.join(sym_x), '&&'.join(sym_z)
    # return sym_x, sym_z

if __name__ == "__main__":

    print(sym_gen(5, 3))