import dat
from dat import *
from encoder import *
from z3 import *
import matplotlib.pyplot as plt
from timebudget import timebudget 
import cvc5
@timebudget
def sur_cond_checker(distance, encode_time, check_time):
    t1 = time.time()
    num_qubits = distance**2
    max_errors = (distance - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    max_errors = (distance - 1) // 2 
    surface_mat = dat.surface_matrix_gen(distance)
    precond = dat.stab_cond_gen(surface_mat, num_qubits, 1) 
    #precond, cond2, x_inds, z_inds = surface(distance, 1)
    err_cond = f"sum i 1 {num_qubits} (ex_(i)) <= {max_errors} && sum i 1 {num_qubits} (ez_(i)) <= {max_errors}"
    postcond = precond

    program = dat.program_gen(surface_mat, num_qubits, 1)

    decoder_cond = dat.decode_cond_gen(surface_mat, num_qubits, 1, distance, distance)

    cass_expr = simplify(VCgeneration(precond, program, postcond))
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    variables = {}
    constraints = []
    err_expr = simplify(tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True))
    #decoder_variables = {}
    #print(err_expr)
    decoder_expr = simplify(tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True))
    #print(decoder_expr)
    vaux_list, vdata_list = [], []

    for name, var in variables.items():
        if var.size() == 1:
            sym, ind = name.split('_')
            if(sym[0] != 'e'):
                vdata_list.append(var)
        else:
            vaux_list.append(var)
    var_list = vaux_list + vdata_list


    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)
    replace_adder = And(*constraints)
    formula_to_check = ForAll(var_list, Or(Not(replace_adder), And(err_expr, Not(decoding_formula))))
    solver = z3.SolverFor("BV")
    #print(formula_to_check)
    solver.add(formula_to_check)
    t2 = time.time()
    encode_time.append(t2 - t1)
    print("Encoding Time: ", t2 - t1)

    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic BV)\n" + "\n".join(lines[1:])
    with open("surface.smt2", "w") as f:
        f.write(formula_smt2)
    
    s2 = cvc5.Solver()
    s2.setOption('produce-models', 'true')
    cvc5_parser = cvc5.InputParser(s2)

    cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

    sm = cvc5_parser.getSymbolManager()
    while True:

        cmd = cvc5_parser.nextCommand()
        if cmd.isNull():
            break
        #print(f"Executing command {cmd}:")
            # invoke the command on the solver and the symbol manager, print the result
        cmd.invoke(s2, sm)
        tf = time.time()

    
    r = s2.checkSat()
    print(r)
    t3 = time.time()
    check_time.append(t3 - t2)
    
encode_time = []

check_time = []
sur_cond_checker(3, encode_time, check_time)
print(encode_time, check_time)
# x = [2*i+1 for i in range(1, 8)]
# #x.append(25)
# for i in x:
#     sur_cond_checker(i, encode_time, check_time)

# plt.plot(x, encode_time, label = "Encoding Time")
# plt.plot(x, check_time, label = "Checking Time")
# plt.xlabel('Code Distance')
# plt.ylabel('Time (s)')
# plt.title('Surface Code Verification Time')
# plt.legend()
# plt.savefig('surface_41.png')
