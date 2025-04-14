#----------#
# Developer: Chester Huang
# Date: 2024/9/20
# Description: Encode classical logical formula in AST format to SMT2
#----------#

from z3 import *
from verifier import *
from lark import Token
import math

from transformer import Loops

## For testing ## 
import re
from lark.reconstruct import Reconstructor
from parser_qec import get_parser

### Reconstruct strings from the abstract syntax tree ###
def recon_string(tree):
    assertion_reconstruct = Reconstructor(parser = get_parser()).reconstruct(tree)
    cleaned_assertion = re.sub(r'\s*_\s*','_', assertion_reconstruct)

    return cleaned_assertion

 
### automatically align the bit-width of two variables ###
def auto_complement(a, b):
    if a.size() > b.size():
        return a, ZeroExt(a.size() - b.size(), b)
    elif a.size() < b.size():
        return ZeroExt(b.size() - a.size(), a), b
    else:
        return a, b



### Encode the values of enumerated variables to formula in format of SMT2 ###
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

### Encode the classical logical formula from abstract syntax tree to SMT2 ###
def tree_to_z3(tree, variables, bit_width, constraints, ifaux = False):
    if isinstance(tree, Token) and tree.type == 'NUMBER':
        bit_width = 1 if tree.value == '0' else int(math.log2(int(tree.value))) + 1
        return BitVecVal(tree.value, bit_width)
    elif tree.data == 'cap':
        return And(*[tree_to_z3(child, variables, bit_width, constraints, ifaux) for child in tree.children])
        
    elif tree.data == 'or':
        return Or(*[tree_to_z3(child, variables, bit_width,constraints, ifaux) for child in tree.children])
    elif tree.data == 'eq':
        z3_child0, z3_child1 = auto_complement(
                                    tree_to_z3(tree.children[0], variables, bit_width,constraints, ifaux), 
                                    tree_to_z3(tree.children[1], variables, bit_width,constraints, ifaux))
        return z3_child0 == z3_child1
    elif tree.data == 'leq':
        z3_child0 = tree_to_z3(tree.children[0], variables, bit_width, constraints, ifaux) 
        
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


### Generate the Verification condition in case of multi-round measurements ###
def VCgeneration_meas(precond, prog_qec, postcond, prog_log = None):
    
    result_meas = precond_generator(prog_qec, postcond, postcond)
    
    pre_tree, prog_tree, post_tree, auxes = result_meas
      
    aux_trees = []
    for i, aux in enumerate(auxes):
        
        
        cass_transformer = qassertion2c(pre_tree)
        aux = cass_transformer.transform(aux)
    
        aux = simplifyeq().transform(aux)
        
        aux_trees.append(aux)
    
    if prog_log != None: 
        program = f"{prog_log}; {prog_qec}"
        result_log = precond_generator(program, precond, postcond)
        pre_tree_log, prog_tree_log, post_tree_log, _ = result_log
        
        cass_transformer = qassertion2c(pre_tree_log)
        cass_tree = cass_transformer.transform(post_tree_log.children[0].children[-1])
    else:
        
        cass_transformer = qassertion2c(pre_tree)
        cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
    

    return cass_tree, aux_trees

### Generate Verification Condition in case of measurement errors ###
def VCgeneration(precond, program, postcond):
    
    result = precond_generator(program, precond, postcond)
    ## Multiple rounds of measurement, auxes stores the mediated assertion trees ## 
    if len(result) == 4:
        pre_tree, _, post_tree, auxes = result
           
        cass_transformer = qassertion2c(pre_tree)
        cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
        cass_tree = simplifyeq().transform(cass_tree)
        
        aux_trees = []
        for i, aux in enumerate(auxes):
            
            cass_transformer = qassertion2c(pre_tree)
            aux = cass_transformer.transform(aux)
        
            aux = simplifyeq().transform(aux)
            
            aux_trees.append(aux)
        
        return cass_tree, aux_trees
    ## Single round (default, no auxes) ##
    else:
        pre_tree, _, post_tree = result
        
        cass_transformer = qassertion2c(pre_tree)
        cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
        
        cass_tree = simplifyeq().transform(cass_tree)
        
        return cass_tree
    