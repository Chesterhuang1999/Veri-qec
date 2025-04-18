#----------#
# Developer: Chester Huang
# Date: 2024/11/01
# Description: SMT formula generation, SMT solver invokation
# for verifying accurate correction of errors
#----------#

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


sys.setrecursionlimit(1000000)

### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   

### Replace the error variables in formula using enumerated values ### 
def smtencoding_constrep(expr, variables, constraints, err_vals):
    
    consts = {}
    if err_vals != "":
        err_vals_tree, _, _ = precond_generator('skip', err_vals, 'true')
        
        const_errors_to_z3(err_vals_tree.children[0], consts)
        replace = []
        for i, ki in enumerate(consts.keys()):
            replace.append((variables[ki], consts[ki]))
        
        expr = simplify(substitute(expr, replace))
        
    vaux_list, verr_list, vdata_list = [], [], []
    # Collect all variables and select the 
    # syndromes as bounded variables, errors as existential variables
    for name, var in variables.items():
        if var.size() == 1:
            sym, _ = name.split('_')
            
            if(sym[0] not in ('e','p')):
                vdata_list.append(var)
            elif name not in consts.keys():
                verr_list.append(var)
        else:
            vaux_list.append(var)
   
    var_list = vaux_list + vdata_list
    ## Include quantifiers to the expression
    formula_to_check = ForAll(var_list, Not(expr))
    
    return formula_to_check

### Integrating the formulas together to obtain the verification condition to check###
def smtencoding(bit_width, precond, program, postcond, err_cond, err_gt, decoder_cond, sym_cond = None):

    variables = {}
    constraints = []
    ## generated from phases of stabilizers
    cass_tree = VCgeneration(precond, program, postcond)
    cass_expr = tree_to_z3(cass_tree, variables, bit_width, [], False)
    cass_expr = simplify(cass_expr)
    
    ## The assumed condition for correctable errors
    err_tree, _, decoder_tree = precond_generator('skip', err_cond, decoder_cond)
    err_expr = tree_to_z3(err_tree.children[0], variables, bit_width, constraints, True)
    ## Err_gt: assumes error should be detected.
    err_gt_tree, _, _ = precond_generator('skip', err_gt, err_cond)
    err_gt_expr = tree_to_z3(err_gt_tree.children[0], variables, bit_width, [], False)
    
    ### Generate decoder's condition
    decoder_expr = tree_to_z3(decoder_tree.children[0],variables, bit_width, constraints, True)
    decoder_expr = simplify(decoder_expr) 
   
    decoding_formula = And(cass_expr, decoder_expr)
    decoding_formula = simplify(decoding_formula)

    substitution = And(*constraints)

    if sym_cond != None:
        sym_tree, _, _  = precond_generator('skip', sym_cond, 'true')
        sym_expr = tree_to_z3(sym_tree.children[0], variables, bit_width, [], False)
    
        formula = Or(Not(err_gt_expr), And(substitution, 
                Or(Not(err_expr), Not(sym_expr), decoding_formula)))
    ### Not( err_gt_expr => And(substitution, err_expr => decoding_formula))
    ## Substitution is auxiliary, introduced to simplify summation
    else:
        formula = Or(Not(err_gt_expr), And(substitution, 
                Or(Not(err_expr), decoding_formula)))
    
    return formula, variables, constraints
  
### Invokes CVC5 to check the SMT formula ### 
def smtchecking(formula):

    solver = SolverFor('QF_BV')
    solver.add(formula)

    formula_smt2 = solver.to_smt2()
    lines = formula_smt2.splitlines()
    formula_smt2 = f"(set-logic BV)\n" + "\n".join(lines[1:])

    s2 = cvc5.Solver()
    s2.setOption('produce-models', 'true')  
    # Parse the input SMT2 formula
    cvc5_parser = cvc5.InputParser(s2)

    cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

    sm = cvc5_parser.getSymbolManager()
    while True:
        cmd = cvc5_parser.nextCommand()
        if cmd.isNull():
            break
        cmd.invoke(s2, sm)
    ## You can use this to produce the counterexample information
    r = s2.checkSat()
    err = []
    if str(r) == 'sat':
        vars = sm.getDeclaredTerms()
        res_lines = (s2.getModel([], vars)).decode('utf-8').splitlines()[1:-1]
    
        for i, line in enumerate(res_lines):
            if(line[-2] == '1'):
                elems = line.split(' ')
                err.append(elems[1])
        
        return r, err
    
    return r, []

### Generate the symmetry condition for the surface code ###    
## Surface code is central symmetric, so we leverage this property to simplify the code ##
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


### Generate the SMT formula to check ### 
def cond_generator(matrix, dx, dz, is_discrete, is_sym = False):
    num_qubits = matrix.shape[1] // 2
  
    slice_x = num_qubits // dx ## Divide the whole tasks into slices
    slice_z = num_qubits // dz

    ez_max = (dz - 1) // 2
    ex_max = (dx - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    k = matrix.shape[0] - num_qubits
   
    precond_x, precond_z = stab_cond_gen(matrix, num_qubits, k)
    ## The correctable threshold determined by the supposed code distance.
    err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {ex_max}"
    err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {ez_max}"
    ### Assume that all of the errors can be detected.
    err_gt_z = f"sum i 1 {num_qubits} (ex_(i)) <= {2 * ex_max}"
    err_gt_x = f"sum i 1 {num_qubits} (ez_(i)) <= {2 * ez_max}" 
    ## If the discreteness constraint is imposed, then we need to add extra constraints over errors.
    if is_discrete == True:
        for i in range(slice_z):
            start = i * dz + 1
            if start + dz - 1 <= num_qubits:
                err_gt_x += f" && sum i {start} {start + dz - 1} (ez_(i)) <= 1"
            else:
                err_gt_x += f" && sum i {start} {num_qubits} (ez_(i)) <= 1"

        for i in range(slice_x):
            start = i * dx + 1
            if start + dx - 1 <= num_qubits:
                err_gt_z += f" && sum i {start} {start + dx - 1} (ex_(i)) <= 1"
            else:
                err_gt_z += f" && sum i {start} {num_qubits} (ex_(i)) <= 1"
    
    ## Generate initial hoare triple without error condition 
    postcond_x, postcond_z = precond_x, precond_z
    program_x, program_z = program_gen(matrix, num_qubits, k)

    ## Generate Decoder condition
    decoder_cond_x, decoder_cond_z = decode_cond_gen(matrix, num_qubits, k, dx, dz, 'verify')

    ## Include symmetry condition for surface code 
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

### A sequnential checker for logical operations without measurement error ### 
def seq_cond_checker_logical(packed_expr, err_vals, p_vals, opt):
    t2 = time.time()
    expr, variables, constraints = packed_expr
    ## Generate assertions for enumerated values
    if opt == 'x':
        err_val_exprs = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        err_val_exprs.extend([f'(pz_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    else:
        err_val_exprs = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        err_val_exprs.extend([f'(px_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    
    err_val_exprs_str = ' && '.join(err_val_exprs)
    
    formula = smtencoding_constrep(expr, variables, constraints, err_val_exprs_str)
    t3 = time.time()
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result

### A SMT checker with some enumerated values ### 
def seq_cond_checker(packed_expr, err_vals, opt):
    t2 = time.time()
    expr, variables, constraints = packed_expr
    ## Generate assertions for enumerated values
    if opt == 'x':
        err_val_exprs = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    else:
        err_val_exprs = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        
    err_val_exprs_str = ' && '.join(err_val_exprs)
    
    formula = smtencoding_constrep(expr, variables, constraints, err_val_exprs_str)

    t3 = time.time()
    
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result


### A SMT checker with enumerated values and the constraints provided by the user ###
def seq_cond_checker_user(packed_expr, err_vals, info, opt):
    t2 = time.time()
    expr, variables, constraints = packed_expr
    err_set, free_set = info
    ## Generate assertions for enumerated values
    ## Pay attention to the err-free set, we assume no corrections are made there.
    if opt == 'x':
        err_val_exprs = [f'ez_({i + 1}) == 0' for i in free_set]
        err_val_exprs.extend([f'cz_({i + 1}) == 0' for i in free_set])
        err_val_exprs.extend([f'ez_({err_set[i] + 1}) == {err_vals[i]}' for i in range(len(err_vals))])
    else:
        err_val_exprs = [f'ex_({i + 1}) == 0' for i in free_set]
        err_val_exprs.extend([f'cx_({i + 1}) == 0' for i in free_set])
        err_val_exprs.extend([f'ex_({err_set[i] + 1}) == {err_vals[i]}' for i in range(len(err_vals))])

    err_val_exprs_str = ' && '.join(err_val_exprs)

    formula = smtencoding_constrep(expr, variables, constraints, err_val_exprs_str)
    t3 = time.time()
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result

