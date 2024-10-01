import time
import math
from condition import stab_cond_gen, surface_matrix_gen, program_gen, decode_cond_gen
from verifier import precond_generator
from encoder import *
from z3 import *
from timebudget import timebudget
import cvc5

from itertools import combinations 
import math

def smtencoding_testing(kind, triple, err_vals, decoder_cond,decoder_opt, bit_width):
    precond, program, postcond = triple
    variables = {}
    for i in range(len(err_vals)):
        var_name = f"e{kind}_{i + 1}"
        variables[var_name] = BitVecVal(err_vals[i], 1)
   
    #print(variables)
    cass_tree = VCgeneration(precond,program, postcond)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)
    #print(cass_expr) 
    constraints = []
    opt_tree,_,decoder_tree = precond_generator('skip',decoder_opt,decoder_cond)
    decoder_expr = tree_to_z3(decoder_tree.children[0], variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr)
    opt_expr = tree_to_z3(opt_tree.children[0], variables, bit_width, [], False)
    #print(opt_expr)
    #print(decoder_expr)
    decoding_formula = And(cass_expr, decoder_expr)

    decoding_formula = simplify(decoding_formula)

    substitution = And(*constraints)

    formula_to_check = And(substitution, decoding_formula)
        
    return formula_to_check, opt_expr

def smtchecking_testing(formula, opt):
    #use z3 to convert formula to SMT2 format
    solver = z3.Optimize()
    solver.add(formula)
    solver.minimize(opt)
    r = solver.check()
    model = solver.model()
    print(model)
    #formula_smt2 = solver.to_smt2()
    #print(formula_smt2)
    #lines = formula_smt2.splitlines()
    #formula_smt2 = f"(set-logic QF_BV)\n" + "\n".join(lines[1:]) + f"\n(get-model)"

    #cvc5 solver
    #s2 = cvc5.Solver()
    #s2.setOption('produce-models','true')
    #cvc5_parser = cvc5.InputParser(s2)
    #cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

    #sm = cvc5_parser.getSymbolManager()
    #while True:
        #cmd = cvc5_parser.nextCommand()
        #if cmd.isNull():
            #break
        #cmd.invoke(s2, sm)
    
    #print(s2.getModel())
    #r = s2.checkSat()
    return r 

if __name__ == "__main__":
    D = 3
    numq = D**2
    mat = surface_matrix_gen(D)
    #print(mat)
    err_vals = np.array([0, 0, 1, 0, 1, 0, 0, 0, 0])
    program_x,program_z = program_gen(mat, numq, 1)
    postcond_x, postcond_z = stab_cond_gen(mat, numq, 1)
    precond_x = postcond_x
    precond_z = postcond_z
    triple_x = [precond_x, program_x, postcond_x]
    triple_z = [precond_z, program_z, postcond_z]
    decoder_cond_x, decoder_cond_z = decode_cond_gen(mat, numq, 1, D, D)
    print(decoder_cond_z)
    decoder_opt_x = f"sum i 1 {numq} (cz_(i))"
    decoder_opt_z = f"sum i 1 {numq} (cx_(i))"
    formula_x, opt_x = smtencoding_testing('z', triple_x, err_vals,decoder_cond_x,decoder_opt_x, 4)
    formula_z, opt_z = smtencoding_testing('x', triple_z, err_vals,decoder_cond_z,decoder_opt_z, 4)
    result_x = smtchecking_testing(formula_x, opt_x)
    result_z = smtchecking_testing(formula_z, opt_z)
    print(result_x, result_z)
