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
def smtencoding(precond, program, postcond, err_cond, err_gt, decoder_cond, bit_width):
    
    cass_expr = simplify(VCgeneration(precond, program, postcond))
    #print(cass_expr)
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    #err_variables = {}
    variables = {}
    constraints = []
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True)
    
    err_gt_tree, _, _ = precond_generator('skip', err_gt, err_cond)
    err_gt_expr = tree_to_z3(err_gt_tree.children[0], {}, bit_width,  [], False)
    
    #err_expr = simplify(tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True))
    #decoder_variables = {}
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    #decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True))

    #decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],decoder_variables, bit_width))
    #var_list = [var for var in list(decoder_variables.values()) if var not in list(err_variables.values())]
    #constraints.append(err_gt_expr)
    #print(err_gt_expr)
    vaux_list, verr_list, vdata_list = [], [], []
    
    for name, var in variables.items():
        if var.size() == 1:
            sym, ind = name.split('_')
            if(sym[0] != 'e'):
                vdata_list.append(var)
            else:
                verr_list.append(var)
        else:
            vaux_list.append(var)

    var_list = vaux_list + vdata_list
    #print(var_list)
    #print(vdata_list)
    decoding_formula = And(cass_expr, decoder_expr)
    #decoding_formula = simplify(And(cass_expr, decoder_expr))
    substitution = And(*constraints)

    #formula_to_check = ForAll(var_list,  Or(Not(substitution), And(err_expr, Not(decoding_formula))))
    #formula_to_check = ForAll(verr_list, Exists(var_list, And(substitution, Or(Not(err_expr), decoding_formula))))
    #formula_to_check = ForAll(verr_list, Exists(var_list, Implies(err_gt_expr, And(substitution, Or(Not(err_expr), decoding_formula)))))
    formula_to_check = ForAll(verr_list, Exists(var_list, Or(Not(err_gt_expr), And(substitution, Or(Not(err_expr), decoding_formula)))))
    #formula_to_check = ForAll(verr_list, And(substitution, Implies(err_expr, decoding_formula)))
    #print(formula_to_check)
    # 
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

@timebudget
def sur_cond_checker(distance, encode_time, check_time):
    t1 = time.time()
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

    #program = surface_program(distance,x_inds,z_inds)
    program_x, program_z = program_gen(surface_mat, num_qubits, 1)
    #decoder_cond = sur_decode_gen(x_inds, z_inds)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance)
    formula_x = smtencoding(precond_x, program_x, postcond_x, err_cond_x, err_gt_x, decoder_cond_x, bit_width)
    formula_z = smtencoding(precond_z, program_z, postcond_z, err_cond_z, err_gt_z, decoder_cond_z, bit_width)
    t2 = time.time()
    encode_time.append(t2 - t1)
    result_x = smtchecking(formula_x)
    result_z = smtchecking(formula_z)
    t3 = time.time()
    check_time.append(t3 - t2)
    
encode_time = []
check_time = []
sur_cond_checker(5, encode_time, check_time)
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