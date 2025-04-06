import sys
from condition import stab_cond_gen, surface_matrix_gen
from verifier import precond_generator, qassertion2c
from transformer import recon_string
from encoder import tree_to_z3, const_errors_to_z3, VCgeneration
from z3 import *

import time
import cvc5
import bitwuzla as bzla

import numpy as np
import math
from collections import defaultdict
from Dataset import linalg_GF, special_codes, qldpc_codes
### A special subclass of codes which can detect but cannot correct errors
sys.setrecursionlimit(1000000)

### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   
def smtencoding_constrep(expr, variables, err_vals):
    
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
    # formula_to_check = ForAll(verr_list, Exists(var_list, expr))
    # formula_to_check = ForAll(var_list, expr)
    formula_to_check = expr
    return formula_to_check

  
# @timebudget 
class Terminator:
    def __init__(self, time_limit):
        self.start_time = time.time()
        self.time_limit = time_limit
    def __call__(self):
        return (time.time() - self.start_time) > self.time_limit

def smtchecking_bzla(formula):
    solver = Solver()
    solver.add(formula)
    # print(formula)
    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic QF_BV)\n" + "\n".join(lines[2:])
    # print(formula_smt2)
    # with open('test.smt2', 'w') as f:   
    #     f.write(formula_smt2)
    # print(formula_smt2)
    tm = bzla.TermManager()
    options = bzla.Options()
    # options.set("produce-models", "true")
    # bitwuzla = bzla.Bitwuzla(tm, options)
    # options.set(bzla.Option.SAT_SOLVER, 'cadical')
    ### Set the timeout for the solver
    parser = bzla.Parser(tm, options)
    # result = parser.parse('test.smt2') 
    parser.parse(formula_smt2, True, False)
    tt = Terminator(900)
    bzla_solver = parser.bitwuzla()
    bzla_solver.configure_terminator(tt)
    # result = parser.bitwuzla().check_sat()
    result = bzla_solver.check_sat()    
    # print(result)
    return result

def smtchecking(formula):
    #t = Tactic('solve-eqs')
    solver = Solver()
    solver.add(formula)
    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic QF_BV)\n" + "\n".join(lines[1:])

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
    err = []
    r = s2.checkSat()
    if str(r) == 'sat':
        vars = sm.getDeclaredTerms()
        res_lines = (s2.getModel([], vars)).decode('utf-8').splitlines()[1:-1]
        for i, line in enumerate(res_lines):
            
            if(line[-2] == '1'):
                elems = line.split(' ')
                # print(elems)
                err.append(elems[1])
        return r, err
        # print(res_lines)
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

def stab_cond_gen_detect(matrix, n, k):
    cond_parts_x = []
    cond_parts_z = []
    for i in range(n - k):
        hasx, hasz = False, False
        for j in range(n):
            if matrix[i][j] == 1:
                cond_parts_x.extend(f"(0,1,{j + 1})")
                hasx = True
            if matrix[i][j + n] == 1:
                cond_parts_z.extend(f"(1,0,{j + 1})")
                hasz = True
        if hasx == True:
            cond_parts_x.append("&&")
        if hasz == True:
            cond_parts_z.append("&&")
    
    return ''.join(cond_parts_x[:-1]), ''.join(cond_parts_z[:-1])

def meas_gen_detect(H, n, k): 
    prog_parts_x = []
    prog_parts_z = []

    for i in range(n - k):
        if (np.all(H[i,:n] == 0) == False):
            prog_parts_x.append(f"s_({i + 1}) := meas")
            for j in range(n):
                if H[i][j] == 1:
                    prog_parts_x.append(f"(0,1,{j + 1})")
            prog_parts_x.append("; ")
        if (np.all(H[i,n:] == 0) == False):
            prog_parts_z.append(f"s_({i + 1}) := meas")
            for j in range(n):
                if H[i][j + n] == 1:
                    prog_parts_z.append(f"(1,0,{j + 1})")
            prog_parts_z.append(";")

    return ''.join(prog_parts_x[:-1]), ''.join(prog_parts_z[:-1])
def cond_generator(matrix, dx, dz, is_Tanner, is_sym = False):
    num_qubits = matrix.shape[1] // 2
    # ez_max = (dz - 1) // 2
    # ex_max = (dx - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    k = matrix.shape[0] - num_qubits
   
    precond_x, precond_z = stab_cond_gen(matrix, num_qubits, k)

    if is_Tanner == True:
        err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) == {dx - 1}"
        err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) == {dz - 1}"
    else:
        err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {dx - 1} && sum i 1 {num_qubits} (ex_(i)) >= 1"
        err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {dz - 1} && sum i 1 {num_qubits} (ez_(i)) >= 1"
    err_prog_z = f"for i in 1 to {num_qubits} do q_(i) *= ex_(i) X end"
    err_prog_x = f"for i in 1 to {num_qubits} do q_(i) *= ez_(i) Z end"
    postcond_x, postcond_z =  precond_x , precond_z
    
    program_x, program_z = meas_gen_detect(matrix, num_qubits, k)

    packed_x = smtencoding_detect(bit_width, precond_x, program_x, postcond_x, 
                            err_cond_x, err_prog_x)
    packed_z = smtencoding_detect(bit_width, precond_z, program_z, postcond_z, 
                            err_cond_z, err_prog_z)

    return packed_x, packed_z

def smtencoding_detect(bit_width, precond, program, postcond, err_cond, err_prog):              
    post_tree, _, meas_tree = precond_generator(program, postcond, precond)
    variables = {}
 
    constraints = []
    meas_cond = recon_string(meas_tree)
    phase_tree = VCgeneration(precond, err_prog, meas_cond)
    phase_expr = simplify(tree_to_z3(phase_tree, variables, bit_width, [], False))
    logic_expr_list = []
    stabs_expr_list = []
    for i, child in enumerate(phase_expr.children()):
        name = child.children()[0].sexpr().split('_')[0]
        if name != 's':
            logic_expr_list.append(Not(child))
        else:
            stabs_expr_list.append(child)
    if len(logic_expr_list) == 1:
        logic_expr = logic_expr_list[0]
    else:
        logic_expr = Or(*logic_expr_list)
    phase_expr = And(*stabs_expr_list)
    # cass_tree = Qass2c(meas_tree, post_tree.children[0])
    meas_transformer = qassertion2c(meas_tree)
    cass_tree = meas_transformer.transform(post_tree.children[0])
    # cass_tree_x = simplifyeq().transform(cass_tree_x)
    cass_expr = simplify(tree_to_z3(cass_tree, {}, bit_width, [], False))
    # print(cass_expr)
    err_tree = precond_generator('skip', err_cond, 'true')[0]
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, False)

    # substitution = And(*constraints)
    # detect_formula = simplify(Or(Not(phase_expr), And(cass_expr, logic_expr)))
    detect_formula = simplify(And(logic_expr, phase_expr, cass_expr))
    # print(logic_expr, phase_expr, cass_expr)
    # print(err_expr)
    # expr = And(substitution, Or(Not(err_expr), detect_formula))
    # expr = simplify(And(substitution, err_expr, detect_formula))
    expr = simplify(And(err_expr, detect_formula))
    return expr, variables

def seq_cond_checker_detect(packed_expr, err_vals, opt):
    t2 = time.time()
    expr, variables = packed_expr
    if opt == 'x':
        err_val_exprs = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    else:
        err_val_exprs = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    
    err_val_exprs_str = ' && '.join(err_val_exprs)
    
    formula = smtencoding_constrep(expr, variables, err_val_exprs_str)
    # print(formula)
    t3 = time.time()
    # result = smtchecking_bzla(formula)
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result


if __name__ == '__main__':
   
    dx = 4
    dz = 2
    err_vals = [0]
    Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                   [1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
    Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])
    Rep51 = np.array([[1, 1, 0, 0, 0],
                  [1, 0, 1, 0, 0],
                  [1, 0, 0, 1, 0],
                  [1, 0, 0, 0, 1]])
    Par54 = np.array([[1, 1, 1, 1, 1]])

    # min_x = np.argmin(row_sum_x)
    # min_z = np.argmin(row_sum_z)
    # err_inds_x = np.array(np.nonzero(matrix[min_x + n -k ,:]))[0]
    # err_inds_z = np.array(np.nonzero(matrix[min_z + n, :]))[0] - 343
    
    # err_vals_x = np.zeros(n - 5, dtype = int)
    # err_vals_z = np.zeros(n - 5, dtype = int)
    # for i in np.random.choice(err_inds_x, dx_max - 2, replace = False):
    #     if i <= len(err_vals_x) - 1:
    #         err_vals_x[i] = 1
    # for i in np.random.choice(err_inds_z, dz_max - 2, replace = False):
    #     if i <= len(err_vals_z) - 1:
    #         err_vals_z[i] = 1
    

    matrix = surface_matrix_gen(3)
    dz = 3
    dx = 3
    start = time.time()
    packed_x, packed_z = cond_generator(matrix, dx, dz, False)
    
    err_vals_z = [0]
    err_vals_x = [1]
    end = time.time()
    print(end - start)
    time1, res_x = seq_cond_checker_detect(packed_x, err_vals_z, 'x')
    
    time2, res_z = seq_cond_checker_detect(packed_z, err_vals_x, 'z')

    print(time1, res_x)
    print(time2, res_z)