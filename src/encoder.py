from z3 import *
from verifier import *
from lark import Token
import math
# import matplotlib.pyplot as plt
from transformer import Loops

## For testing ## 
import re
from lark.reconstruct import Reconstructor
from parser_qec import get_parser
def recon_string(tree):
    assertion_reconstruct = Reconstructor(parser = get_parser()).reconstruct(tree)
    cleaned_assertion = re.sub(r'\s*_\s*','_', assertion_reconstruct)

    return cleaned_assertion
def auto_complement(a, b):
    if a.size() > b.size():
        return a, ZeroExt(a.size() - b.size(), b)
    elif a.size() < b.size():
        return ZeroExt(b.size() - a.size(), a), b
    else:
        return a, b


#def tree_to_z3(tree, variables, bit_width, aux):
#     if isinstance(tree, Token) and tree.type == 'NUMBER':
#         bit_width = 1 if tree.value == '0' else int(math.log2(int(tree.value))) + 1
#         return BitVecVal(tree.value, bit_width)
#     elif tree.data == 'and':
#         return And(*[tree_to_z3(child, variables, bit_width, aux) for child in tree.children])
#     elif tree.data == 'or':
#         return Or(*[tree_to_z3(child, variables, bit_width, aux) for child in tree.children])
#     elif tree.data == 'eq':
#         z3_child0, z3_child1 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width, aux), tree_to_z3(tree.children[1], variables, bit_width, aux))
#         return z3_child0 == z3_child1
#     elif tree.data == 'leq':
#         z3_child0 = tree_to_z3(tree.children[0], variables, bit_width) 
#         if isinstance(tree.children[1], Tree):
#             if(tree.children[1].data == 'min'):
#                 min_tree = tree.children[1]
#                 z3_child10, z3_child11 = tree_to_z3(min_tree, variables, bit_width)
#                 z3_child0, z3_child10 = auto_complement(z3_child0, z3_child10)
#                 z3_child1, z3_child11 = auto_complement(z3_child0, z3_child11)
#                 return And(ULE(z3_child0, z3_child10), ULE(z3_child0, z3_child11))
        
#         z3_child0, z3_child1 = auto_complement(z3_child0, tree_to_z3(tree.children[1], variables, bit_width, aux)) 
#         return ULE(z3_child0, z3_child1)
#     elif tree.data == 'geq':   
#         z3_child0, z3_child1 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width, aux), tree_to_z3(tree.children[1], variables, bit_width, aux))
#         return UGE(z3_child0, z3_child1) 
#     elif tree.data == 'xor':
#         return tree_to_z3(tree.children[0], variables, bit_width, aux) ^ tree_to_z3(tree.children[1], variables, bit_width, aux)
#     elif tree.data == 'add':
#         ssum = BitVecVal(0, bit_width)
#         for child in tree.children:
#             z3_child = tree_to_z3(child, variables, bit_width, aux)
#             ext_width = bit_width - z3_child.size()
#             ssum += ZeroExt(ext_width, z3_child)
#         aux.cnt += 1
#         var_name = f"aux_{aux.cnt}"
#         variables[var_name] = BitVec(var_name, bit_width)
#         aux.con.append(ssum == variables[var_name])
#         return ssum
#     elif tree.data == 'sum':
#         name = tree.children[0].value
#         start = int(tree.children[1].value)
#         end = int(tree.children[2].value)
#         body = tree.children[3]
#         ssum = BitVecVal(0, bit_width)
#         for j in range(start, end+1):
#             loops_transformer = Loops(name, j)
#             body_trans = loops_transformer.transform(body)
#             z3_body_trans = tree_to_z3(body_trans, variables, bit_width, aux)
#             ext_width = bit_width - z3_body_trans.size()
#             ssum = ssum + ZeroExt(ext_width, tree_to_z3(body_trans, variables, bit_width, aux))
#         if 
#         aux.cnt += 1
#         var_name = f"aux_{aux.cnt}"
#         variables[var_name] = BitVec(var_name, bit_width)
#         aux.con.append(ssum == variables[var_name])
#         return ssum
#     # elif tree.data == 'bool_and':
#     #     return tree_to_z3(tree.children[0], variables, bit_width, aux) & tree_to_z3(tree.children[1], variables, bit_width, aux)
#     # elif tree.data == 'bool_or':
#     #     return tree_to_z3(tree.children[0], variables, bit_width, aux) | tree_to_z3(tree.children[1], variables, bit_width, aux)
#     elif tree.data == 'neg':
#         return Not(tree_to_z3(tree.children[0], variables, bit_width, aux))
#     elif tree.data == 'min':
#         res1,res2 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width, aux), tree_to_z3(tree.children[1], variables, bit_width, aux))
#         return res1, res2
#     elif tree.data == 'var':
#         name = tree.children[0].value
#         index = int(tree.children[1].value)
#         var_name = f"{name}_{index}"
#         if var_name not in variables:
#             variables[var_name] = BitVec(var_name, 1)
#             # if bit_width > 1:
#             #     constraints.append(Or(variables[var_name] == BitVecVal(0, bit_width), variables[var_name] == BitVecVal(1, bit_width)))  # Add domain constraint for this variable
#         return variables[var_name]
#     else:
#         raise ValueError(f"Unknown tree node: {tree}")


def const_errors_to_z3(tree, variables):
    if isinstance(tree, Token) and tree.type == 'NUMBER':
        return BitVecVal(tree.value, 1)
    elif tree.data == 'cap':
        for child in tree.children:
            const_errors_to_z3(child, variables)
        return None
    elif tree.data == 'eq':
        var_name = const_errors_to_z3(tree.children[0], variables)
        const_val = const_errors_to_z3(tree.children[1], variables)
        variables[var_name] = const_val
        return None
    elif tree.data == 'var':
        name = tree.children[0].value
        index = int(tree.children[1].value)
        var_name = f"{name}_{index}"
        return var_name
    else:
        raise ValueError(f"Unknown tree node: {tree}")


def tree_to_z3(tree, variables, bit_width, constraints, ifaux = False):
    if isinstance(tree, Token) and tree.type == 'NUMBER':
        bit_width = 1 if tree.value == '0' else int(math.log2(int(tree.value))) + 1
        return BitVecVal(tree.value, bit_width)
    elif tree.data == 'cap':
        return And(*[tree_to_z3(child, variables, bit_width, constraints, ifaux) for child in tree.children])
        # return simplify(
        #     And(*[tree_to_z3(child, variables, bit_width, constraints, ifaux) for child in tree.children])
        # )
    elif tree.data == 'or':
        return Or(*[tree_to_z3(child, variables, bit_width,constraints, ifaux) for child in tree.children])
    elif tree.data == 'eq':
        z3_child0, z3_child1 = auto_complement(
                                    tree_to_z3(tree.children[0], variables, bit_width,constraints, ifaux), 
                                    tree_to_z3(tree.children[1], variables, bit_width,constraints, ifaux))
        return z3_child0 == z3_child1
    elif tree.data == 'leq':
        z3_child0 = tree_to_z3(tree.children[0], variables, bit_width, constraints, ifaux) 
        # if isinstance(tree.children[1], Tree):
        #     if(tree.children[1].data == 'min'):
        #         min_tree = tree.children[1]
        #         z3_child10, z3_child11 = tree_to_z3(min_tree, variables, bit_width, constraints, ifaux)
        #         z3_child0, z3_child10 = auto_complement(z3_child0, z3_child10)
        #         z3_child0, z3_child11 = auto_complement(z3_child0, z3_child11)
        #         return And(ULE(z3_child0, z3_child10), ULE(z3_child0, z3_child11))    
        z3_child0, z3_child1 = auto_complement(z3_child0, tree_to_z3(tree.children[1], variables, bit_width, constraints, ifaux)) 
        return ULE(z3_child0, z3_child1)
    
    elif tree.data == 'geq':   
        z3_child0, z3_child1 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width,constraints, ifaux), tree_to_z3(tree.children[1], variables, bit_width,constraints, ifaux))
        return UGE(z3_child0, z3_child1) 
    elif tree.data == 'xor':
        return tree_to_z3(tree.children[0], variables, bit_width,constraints, ifaux) + tree_to_z3(tree.children[1], variables, bit_width,constraints, ifaux)
    elif tree.data == 'add':
        ssum = BitVecVal(0, bit_width)
        for child in tree.children:
            z3_child = tree_to_z3(child, variables, bit_width,constraints, ifaux)
            ext_width = bit_width - z3_child.size()
            ssum += ZeroExt(ext_width, z3_child)
        return ssum
    elif tree.data == 'sum':
        name = tree.children[0].value
        start = int(tree.children[1].value)
        end = int(tree.children[2].value)
        body = tree.children[3]
        ssum = BitVecVal(0, bit_width)
        for j in range(start, end+1):
            loops_transformer = Loops(name, j)
            body_trans = loops_transformer.transform(body)
            z3_body_trans = tree_to_z3(body_trans, variables, bit_width,constraints, ifaux)
            ext_width = bit_width - z3_body_trans.size()
            ssum = ssum + ZeroExt(ext_width, tree_to_z3(body_trans, variables, bit_width, constraints, ifaux))
        if ifaux == True:
            body_name = str(body.children[0].value)
            var_name = f"{body_name}aux_{start}_{end}"
            var_aux = BitVec(var_name, bit_width)
            if var_aux not in variables:
                variables[var_name] = var_aux
                constraints.append((ssum == var_aux))
            return var_aux
        else:
            return ssum
    elif tree.data == 'neg':
        return Not(tree_to_z3(tree.children[0], variables, bit_width,constraints, ifaux))
    elif tree.data == 'min':
        res1,res2 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width,constraints, ifaux), tree_to_z3(tree.children[1], variables, bit_width,constraints, ifaux))
        # return res1, res2
        return If(ULE(res1, res2), res1, res2)
    elif tree.data == 'var':
        name = tree.children[0].value
        index = int(tree.children[1].value)
        var_name = f"{name}_{index}"
        if var_name not in variables:
            variables[var_name] = BitVec(var_name, 1)
        return variables[var_name]
    else:
        raise ValueError(f"Unknown tree node: {tree}")


def VCgeneration_meas(precond, prog_qec, postcond, prog_log = None):
    # print(prog_qec)
    result_meas = precond_generator(prog_qec, postcond, postcond)
    
    pre_tree, prog_tree, post_tree, auxes = result_meas
    # print(recon_string(pre_tree))   
    aux_trees = []
    for i, aux in enumerate(auxes):
        
        # aux = Qass2c(pre_tree, aux)
        cass_transformer = qassertion2c(pre_tree)
        aux = cass_transformer.transform(aux)
    
        aux = simplifyeq().transform(aux)
        
        aux_trees.append(aux)
    
    if prog_log != None: 
        program = f"{prog_log}; {prog_qec}"
        result_log = precond_generator(program, precond, postcond)
        pre_tree_log, prog_tree_log, post_tree_log, _ = result_log
        # print(recon_string(pre_tree_log))
        # cass_tree = Qass2c(pre_tree, post_tree.children[0].children[-1])  ## Save if test corrects
        cass_transformer = qassertion2c(pre_tree_log)
        cass_tree = cass_transformer.transform(post_tree_log.children[0].children[-1])
    else:
        # cass_tree = Qass2c(pre_tree, post_tree.children[0].children[-1])
        cass_transformer = qassertion2c(pre_tree)
        cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
    
    # print(recon_string(cass_tree))
    # exit(0)
    return cass_tree, aux_trees
def VCgeneration(precond, program, postcond):
    # pre_tree, prog_tree, post_tree, auxes = precond_generator(program, precond, postcond)
    
    result = precond_generator(program, precond, postcond)
    
    if len(result) == 4:
        pre_tree, _, post_tree, auxes = result
        # cass_tree = Qass2c(pre_tree, post_tree.children[0].children[-1])  ## Save if test corrects   
        cass_transformer = qassertion2c(pre_tree)
        cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
        cass_tree = simplifyeq().transform(cass_tree)
        # print(recon_string(cass_tree))
        # exit(0)
        
        aux_trees = []
        for i, aux in enumerate(auxes):
            # print(recon_string(aux))
            # aux = Qass2c(pre_tree, aux)
            cass_transformer = qassertion2c(pre_tree)
            aux = cass_transformer.transform(aux)
        
            aux = simplifyeq().transform(aux)
            # print(recon_string(aux))
            aux_trees.append(aux)
        
        return cass_tree, aux_trees
    
    else:
        pre_tree, _, post_tree = result
        # cass_tree = Qass2c(pre_tree, post_tree.children[0].children[-1])  ## Save if test corrects
        cass_transformer = qassertion2c(pre_tree)
        cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
        # print(recon_string(post_tree.children[0].children[-1]))
        cass_tree = simplifyeq().transform(cass_tree)
        # print(recon_string(cass_tree))
        return cass_tree
    # # print(recon_string(pre_tree))
    # cass_transformer = qassertion2c(pre_tree)
    # cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
    # cass_tree = simplifyeq().transform(cass_tree)
    # aux_trees = []
    # for i, aux in enumerate(auxes):
    #     cass_transformer = qassertion2c(pre_tree)
    #     aux = cass_transformer.transform(aux)
        
    #     aux = simplifyeq().transform(aux)
    #     aux_trees.append(aux)
        
    # cass_expr = tree_to_z3(cass_tree, {}, 1, [], False)

    # return cass_tree, aux_trees

##Test 
if __name__ == "__main__":
# start = time.time()
    precond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3)&& (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) """
    program = """for i in 1 to 7 do q_(i) *= ex_(i) X end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); for i in 1 to 7 do q_(i) *= cx_(i) X end"""
    postcond =  """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3)&& (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) """


# precond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

# program = """ for i in 1 to 7 do q_(i) *= ex_(i) X end; for i in 1 to 7 do q_(i) *= ez_(i) Z end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
# sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
# sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end; for i in 1 to 7 do q_(i) *= cz_(i) Z end"""

# postcond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

    cass_tree = VCgeneration(precond, program, postcond)
    variables = {}
    cass_expr = simplify(tree_to_z3(cass_tree.children[1], variables, 3, [], False))
    logic_expr = simplify(tree_to_z3(cass_tree.children[0], {}, 3, [], False))
    # print(cass_expr)
    decoder_cond = """ sz_(1) == cx_(1) @^ cx_(3) @^ cx_(5)@^ cx_(7) && sz_(2) == cx_(2) @^ cx_(3) @^ cx_(6) @^ cx_(7) && 
    sz_(3) == cx_(4) @^ cx_(5) @^ cx_(6) @^ cx_(7)"""
    sum_min = """sum i 1 7 (cx_(i))"""
    # variables_dec = {}
    decoder_tree,_, sum_tree = precond_generator('skip', decoder_cond, sum_min)
    decoder_expr = simplify(tree_to_z3(decoder_tree.children[0], {}, 3, [], False))
    var_corr = {}
    sum_expr = simplify(tree_to_z3(sum_tree.children[0], var_corr, 3, [], False))                      
    # var_corr = list(var_corr.values())
    
    decoding_formula = And(cass_expr, decoder_expr)
    
    consts_x = {}
    replace = []
    s1 = z3.Optimize()
    err_vals = [0,1,0,0,0,0,1]
    for i, ei in enumerate(err_vals):
        consts_x[f'ex_{i+1}'] = BitVecVal(ei, 1)
    for i in consts_x.keys():
        replace.append((variables[i], consts_x[i]))

    decoding_formula = simplify(substitute(decoding_formula, replace))
    logic_expr = simplify(substitute(logic_expr, replace))
    print(logic_expr)
    # print(decoding_formula)
    s1.add(decoding_formula)
    s1.minimize(sum_expr)
    if s1.check() == sat:
        model = s1.model()
       
    else: 
        print("unsat")
    replace = []
    for i in var_corr.keys():
        replace.append((var_corr[i], model[var_corr[i]]))
    print(replace)
    logic_expr = substitute(logic_expr, replace)
    s2 = z3.Solver()
    
    


# ## error condition and decoder condition generation 
# err_cond = """ sum i 1 7 (ex_(i)) <= 1 && sum i 1 7 (ez_(i)) <= 1 """
# # ## Decoding condition of a minimum-weight perfect matching (should be read from file)
# decoder_cond_bool = """ sz_(1) == cx_(1) @^ cx_(3) @^ cx_(5)@^ cx_(7) && sz_(2) == cx_(2) @^ cx_(3) @^ cx_(6) @^ cx_(7) && sz_(3) == cx_(4) @^ cx_(5) @^ cx_(6) @^ cx_(7) &&
# sx_(1) == cz_(1) @^ cz_(3) @^ cz_(5) @^ cz_(7)  && sx_(2) == cz_(2) @^ cz_(3) @^ cz_(6) @^ cz_(7) && sx_(3) == cz_(4) @^ cz_(5) @^ cz_(6) @^ cz_(7)"""

# decoder_cond_int = """ sum i 1 7 (cx_(i)) <= Min( sum i 1 7 (ex_(i)), 1) && sum i 1 7 (cz_(i)) <= Min( sum i 1 7 (ez_(i)), 1) """

# err_tree, _, decoder_tree_int = precond_generator('skip', err_cond, decoder_cond_int)
# _, _, decoder_tree_bool = precond_generator('skip', err_cond, decoder_cond_bool)

# err_expr = tree_to_z3(err_tree.children[0], {}, 3)
# decoder_expr_int = tree_to_z3(decoder_tree_int.children[0],{}, 3)

# variables = {}

# decoder_expr_bool = simplify(tree_to_z3(decoder_tree_bool.children[0], variables, 3))
# decoding_formula = And(cass_expr, decoder_expr_int, decoder_expr_bool)

# s = z3.SolverFor("BV")

# var_list = list(variables.values())
# correctness_formula = ForAll(var_list, And(err_expr, Not(decoding_formula)))

# #print(correctness_formula.sexpr())
# s.add(correctness_formula)
# formula_smt2 = s.to_smt2()
# print(formula_smt2)
# tm = cvc5.TermManager()
# s2 = cvc5.Solver()
# s2.setOption('produce-models', 'true')  
# cvc5_parser = cvc5.InputParser(s2)

# cvc5_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, formula_smt2, "MyInput")

# sm = cvc5_parser.getSymbolManager()
# while True:
#     cmd = cvc5_parser.nextCommand()
#     if cmd.isNull():
#         break
#     print(f"Executing command {cmd}:")
#         # invoke the command on the solver and the symbol manager, print the result
#     print(cmd.invoke(s2, sm), end="")

# r = s2.checkSat()


# # F = err_expr