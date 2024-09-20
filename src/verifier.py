
#------------
# author: Chester Huang
# date: 2024.7.10
# version: 1.0.0
#------------


#Introduction: This file use heuristic rules to transform VCs generated into classical assertions
#and encode them into Z3 formulas

from lark import Lark, Transformer, v_args, Tree, Token
from lark.reconstruct import Reconstructor
from parser_bexp2 import get_parser
from transformer_bexp2 import precond_generator, Loops
from transformer_bexp2 import eq_pauliop, eq_pexpr
import re
import time
from collections import defaultdict
import queue
from z3 import *
from data import *
import cvc5
from cvc5 import Kind, Solver
## Overload
def __xor__(a: Token, b: Token):
    assert a.type == 'NUMBER' and a.type == 'NUMBER'
    return Token('NUMBER', int(a.value) ^ int(b.value))
## Heuristic rule I: judge whether stabilizers in two assertions belong to the same group (or same)
def stab_set_gen(u: Tree):
    stab_set = sorted(list(u.find_data('pexpr')), key = lambda x: int(x.children[0].children[-1].value))
    stab_dict = defaultdict(set) 
    stab_list = []
    for s in stab_set:
        stab_dict[len(s.children)].add(s)
        stab_list.append(s)
        a = all(commute(s,t) for t in stab_set)
        if(a != True):
            raise Exception("Non-commute stabilizers!")
    return stab_dict, stab_list

def find_stab_rep(stab_dict, stab_list, s):
    l = len(s.children)
    phase = Token('NUMBER','0')
    is_matched = 0
    while is_matched == 0:
        for s_c in stab_dict[l]:
            if eq_pexpr(s, s_c):
                if len(s_c.children[0].children) == 4:
                    phase = s_c.children[0].children[0]
                #phase_set.append((s,phase))
                is_matched = 1
                stab_dict[l].remove(s_c) 
                break
        if is_matched == 1:
            break
        stab_list_cpy = stab_list.copy()
        length = len(stab_list_cpy)
        for i in range(length):
            for j in range(1 + i, length):
                temp_mul = stab_mul(stab_list_cpy[i],stab_list_cpy[j])
                if len(temp_mul.children) > 0:
                    stab_dict[len(temp_mul.children)].add(temp_mul)
                    stab_list.append(temp_mul)
                    #print(temp_mul)
#         raise Exception
    return phase
     
        
## Check if two pauli strings are commute
def commute(u: Tree, v: Tree):
    u_dict = {}
    for child in u.children:
        index = child.children[-1]
        #operator = child.children[-2]
        u_dict[index] = child
    mul = 1
    for child in v.children:
        index = child.children[-1]
        #operator = child.children[-2]
        if index in u_dict and u_dict[index] != child:
            mul = -mul   
    return mul

### Multiplication of stabilizers
def stab_mul(u: Tree, v: Tree):
    phase1 = None
    phase2 = None
    if(len(u.children[0].children) == 4):
        phase1 = u.children[0].children[0]
    if(len(v.children[0].children) == 4):
        phase2 = v.children[0].children[0]
    if phase1 != None and phase2 != None:
        phase = Tree('add', [phase1, phase2])
    else:
        phase = phase1 if phase1 != None else phase2
    stabs = u.children + v.children
    stab_dict = defaultdict(list)
    for stab in stabs:
        stab_dict[int(stab.children[-1])].append(stab)
    minval = min(stab_dict)
    maxval = max(stab_dict)
    stab_new = []
    isphase = 0
    for i in range(minval, maxval + 1):
        temp = stab_dict[i]
        if len(temp) == 1:
            if isphase == 0:
                if len(temp[0].children) == 4:
                    stab_new.append(temp[0])
                    isphase = 1
                else:
                    new = Tree('pauli',[phase] + temp[0].children)
                    isphase = 1
                    stab_new.append(new)
            else:
                if len(temp[0].children) == 4:
                    new = Tree('pauli',temp[0].children[1:])
                    stab_new.append(new)
                else:
                    stab_new.append(temp[0])
        else:
            child0 = temp[0].children
            child1 = temp[1].children
            z = __xor__(child0[-3], child1[-3])
            x = __xor__(child0[-2], child1[-2])
            if z.value != 0 or x.value != 0:
                if phase != None and isphase == 0:
                    new = Tree('pauli', [phase, z, x, Token('NUMBER', i)])
                    isphase = 1
                else:
                    new = Tree('pauli', [z, x, Token('NUMBER', i)])
                
                stab_new.append(new)
    return Tree('pexpr', stab_new)

## Transformation I: assertion with phase assembled implies the original assertion
class qassertion2c(Transformer):
    def __init__(self, base):
        self.base = base
        self.dict, self.list = stab_set_gen(base)
    def pexpr(self, args):  
        phase_desired = find_stab_rep(self.dict, self.list, Tree('pexpr', args))
        # extract the phase
        phase = Token('NUMBER','0')
        if len(args[0].children) == 4:
            phase = args[0].children[0]
            #print(args[0].children[0])
        ## generate the condition
        return Tree('eq', [phase_desired, phase])

### Simplification for classical assertion
def is_num(t):
    return isinstance(t, Token) and t.type == 'NUMBER'

def is_var(t):
    return isinstance(t, Tree) and t.data == 'var'
class calc_sym(Transformer):
    @v_args(inline=True)
    def add(self, l, r):
        if is_num(l) and is_num(r):
            return Token('NUMBER', int(l.value) + int(r.value))
        elif is_num(r):
                return Tree('add', [r, l])
        elif is_num(l):
            if(isinstance(r, Tree) and r.data == 'add') and is_num(r.children[0]):
               new_left = Token('NUMBER', int(l.value) + int(r.children[0].value))
               return Tree('add', [new_left, r.children[1]])         
            return Tree('add', [l, r])
        else:
            return Tree('add', [l, r])
    @v_args(inline=True)    
    def mul(self, l, r):
        if is_num(l) and is_num(r):
            return Token('NUMBER', int(l.value) * int(r.value))
        elif is_num(r):
                return Tree('mul', [r, l])
        return Tree('mul', [l, r])
    @v_args(inline=True)
    def sub(self, l, r): 
        if is_num(l) and is_num(r):
            return Token('NUMBER', int(l.value) - int(r.value)) 
        else: return Tree('sub', [l, r])

# Eliminate same terms in both sides of eq/leq
class simplifyeq(Transformer):
    @v_args(inline=True)
    def eq(self, l, r):
        left_terms = self.flatten_terms(l)
        right_terms = self.flatten_terms(r)
        common_terms = self.find_common_terms(left_terms, right_terms)
        lterms = [term for term in left_terms if term not in common_terms]
        rterms = [term for term in right_terms if term not in common_terms] 
        if(Token('NUMBER','0') in left_terms):
            lterms.remove(Token('NUMBER','0'))
        if(Token('NUMBER','0') in right_terms):
            rterms.remove(Token('NUMBER','0'))
        lterms, rterms = self.swap_terms(lterms, rterms) 
        treedata = l.data if len(left_terms) > 1 else r.data
         
        ltree = self.build_tree(lterms, data = treedata)
        rtree = self.build_tree(rterms, data = treedata)
        return Tree('eq', [ltree, rtree])
    def flatten_terms(self, expr):
        if isinstance(expr, Tree) and expr.data in ('xor', 'add') :
            terms = []
            for child in expr.children:
                terms.extend(self.flatten_terms(child))
            return terms
        else:
            return [expr]
        
    def find_common_terms(self, left_terms, right_terms):
        common_terms = []
        for term in left_terms:
            if term in right_terms:
                common_terms.append(term)
                #right_terms.remove(term)
        return common_terms
    def swap_terms(self, left_terms, right_terms):
        sterms = []
        total_terms = left_terms + right_terms
        for term in total_terms:
                name = term.children[0]
                if(name.value[0] == 's'):
                    sterms.append(term)
        other_terms = [term for term in total_terms if term not in sterms]
        return sterms, other_terms

    def build_tree(self, terms, data):
        if not terms:
            return Token('NUMBER', '0')
        elif len(terms) == 1:
            return terms[0]
        elif len(terms) == 2:
            return Tree(data, terms)
        else:
            return Tree(data, [terms[0],self.build_tree(terms[1:], data)])
        

### SMT encoding
    
def auto_complement(a, b):
    if a.size() > b.size():
        return a, ZeroExt(a.size() - b.size(), b)
    elif a.size() < b.size():
        return ZeroExt(b.size() - a.size(), a), b
    else:
        return a, b
def tree_to_z3(tree, variables, bit_width):
    if isinstance(tree, Token) and tree.type == 'NUMBER':
        bit_width = 1 if tree.value == '0' else int(math.log2(int(tree.value)))+1
        return BitVecVal(tree.value, bit_width)
    elif tree.data == 'and':
        return And(*[tree_to_z3(child, variables,bit_width) for child in tree.children])
    elif tree.data == 'or':
        return Or(*[tree_to_z3(child, variables, bit_width) for child in tree.children])
    elif tree.data == 'eq':
        z3_child0, z3_child1 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width), tree_to_z3(tree.children[1], variables, bit_width))
        return z3_child0 == z3_child1
    elif tree.data == 'leq':
        z3_child0, z3_child1 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width), tree_to_z3(tree.children[1], variables, bit_width)) 
        return ULE(z3_child0, z3_child1)
    elif tree.data == 'geq':   
        z3_child0, z3_child1 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width), tree_to_z3(tree.children[1], variables, bit_width))
        return UGE(z3_child0, z3_child1) 
    elif tree.data == 'xor':
        return tree_to_z3(tree.children[0], variables, bit_width) + tree_to_z3(tree.children[1], variables, bit_width)
    elif tree.data == 'add':
        ssum = BitVecVal(0, bit_width)
        for child in tree.children:
            z3_child = tree_to_z3(child, variables, bit_width)
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
            z3_body_trans = tree_to_z3(body_trans, variables, bit_width)
            ext_width = bit_width - z3_body_trans.size()
            ssum = ssum + ZeroExt(ext_width, tree_to_z3(body_trans, variables, bit_width))      
        return ssum
    elif tree.data == 'bool_and':
        return tree_to_z3(tree.children[0], variables, bit_width) & tree_to_z3(tree.children[1], variables, bit_width)
    elif tree.data == 'bool_or':
        return tree_to_z3(tree.children[0], variables, bit_width) | tree_to_z3(tree.children[1], variables, bit_width)
    elif tree.data == 'neg':
        return Not(tree_to_z3(tree.children[0], variables, bit_width))
    elif tree.data == 'min':
        res1,res2 = auto_complement(tree_to_z3(tree.children[0], variables, bit_width), tree_to_z3(tree.children[1], variables, bit_width))
        return If(ULE(res1, res2), res1, res2)
    elif tree.data == 'var':
        name = tree.children[0].value
        index = int(tree.children[1].value)
        var_name = f"{name}_{index}"
        if var_name not in variables:
            variables[var_name] = BitVec(var_name, 1)
            # if bit_width > 1:
            #     constraints.append(Or(variables[var_name] == BitVecVal(0, bit_width), variables[var_name] == BitVecVal(1, bit_width)))  # Add domain constraint for this variable
        return variables[var_name]
    else:
        raise ValueError(f"Unknown tree node: {tree}")
    
def auto_complement_cvc5(a, b, solver):
    a_size = a.getSort().getBitVectorSize()
    b_size = b.getSort().getBitVectorSize()

    if a_size > b_size:
        zero_ext = solver.mkTerm(Kind.BITVECTOR_ZERO_EXTEND, a_size - b_size, b)
        return a, zero_ext
    elif a_size < b_size:
        zero_ext = solver.mkTerm(Kind.BITVECTOR_ZERO_EXTEND, b_size - a_size, a)
        return zero_ext, b
    else:
        return a, b

def tree_to_cvc5(tree, variables, solver, bit_width):
    if isinstance(tree,Token) and tree.type == 'NUMBER':
        bit_width = 1 if tree.value == '0' else int(math.log2(int(tree.value)))
        return solver.mkBitVector(bit_width, int(tree.value))
    elif tree.data == 'and':
        return solver.mkterm(Kind.BITVECTOR_AND, *[tree_to_cvc5(child, variables, solver, bit_width) for child in tree.children])
    elif tree.data == 'or':
        return solver.mkTerm(Kind.BITVECTOR_OR, *[tree_to_cvc5(child, variables, solver, bit_width) for child in tree.children])
    elif tree.data == 'eq':
        child0, child1 = auto_complement(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                         tree_to_cvc5(tree.children[1], variables, solver, bit_width), solver)
        return solver.mkTerm(Kind.EQUAL, child0, child1)
    elif tree.data == 'leq':
        child0, child1 = auto_complement_cvc5(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                         tree_to_cvc5(tree.children[1], variables, solver, bit_width), solver)
        return solver.mkTerm(Kind.BITVECTOR_ULE, child0, child1)
    elif tree.data == 'geq':
        cvc5_child0, cvc5_child1 = auto_complement_cvc5(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                                   tree_to_cvc5(tree.children[1], variables, solver, bit_width), solver)
        return solver.mkTerm(Kind.BITVECTOR_UGE, cvc5_child0, cvc5_child1)
    elif tree.data == 'xor':
        return solver.mkTerm(Kind.BITVECTOR_XOR, tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                             tree_to_cvc5(tree.children[1], variables, solver, bit_width))
    elif tree.data == 'add':
        ssum = solver.mkBitVector(bit_width, 0)
        for child in tree.children:
            cvc5_child = tree_to_cvc5(child, variables, solver, bit_width)
            ext_width = bit_width - cvc5_child.getBitVectorSize()
            ssum = solver.mkTerm(Kind.BITVECTOR_ADD, ssum, solver.mkTerm(Kind.BITVECTOR_ZERO_EXTEND, ext_width, cvc5_child))
        return ssum
    elif tree.data == 'sum':
        name = tree.children[0].value
        start = int(tree.children[1].value)
        end = int(tree.children[2].value)
        body = tree.children[3]
        ssum = solver.mkBitVector(bit_width, 0)
        for j in range(start, end + 1):
            loops_transformer = Loops(name, j)
            body_trans = loops_transformer.transform(body)
            cvc5_body_trans = tree_to_cvc5(body_trans, variables, solver, bit_width)
            ext_width = bit_width - cvc5_body_trans.getBitVectorSize()
            ssum = solver.mkTerm(Kind.BITVECTOR_ADD, ssum,
                                 solver.mkTerm(Kind.BITVECTOR_ZERO_EXTEND, ext_width, cvc5_body_trans))
        return ssum
    elif tree.data == 'bool_and':
        return solver.mkTerm(Kind.AND, tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                             tree_to_cvc5(tree.children[1], variables, solver, bit_width))
    elif tree.data == 'bool_or':
        return solver.mkTerm(Kind.OR, tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                             tree_to_cvc5(tree.children[1], variables, solver, bit_width))
    elif tree.data == 'neg':
        return solver.mkTerm(Kind.NOT, tree_to_cvc5(tree.children[0], variables, solver, bit_width))
    elif tree.data == 'min':
        res1, res2 = auto_complement(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                     tree_to_cvc5(tree.children[1], variables, solver, bit_width))
        return solver.mkTerm(Kind.ITE, solver.mkTerm(Kind.BITVECTOR_ULE, res1, res2), res1, res2)
    elif tree.data == 'var':
        name = tree.children[0].value
        index = int(tree.children[1].value)
        var_name = f"{name}_{index}"
        if var_name not in variables:
            variables[var_name] = solver.mkConst(solver.mkBitVectorSort(1), var_name)
        return variables[var_name]
    else:
        raise ValueError(f"Unknown tree node: {tree}")
            

def VCgeneration(precond, program, postcond):
    pre_tree, prog_tree, post_tree = precond_generator(program, precond, postcond)
    #stab_dict, stab_list = stab_set_gen(pre_tree.children[0])
    cass_transformer = qassertion2c(pre_tree)
    cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
    cass_tree = simplifyeq().transform(cass_tree)
    cass_expr = tree_to_z3(cass_tree, {}, 1)

    return cass_expr

# Test: Surface code

# start = time.time()
# distance = 5
# num_logical = 1
# precond1, precond2, program = triple_gen('surface', distance, num_logical)
# postcond1 = precond1
# postcond2 = precond2

# cass_expr1 = VCgeneration(precond1, program, postcond1)
# cass_expr2 = VCgeneration(precond2, program, postcond2)

# num_qubits = distance**2
# bit_width = int(math.log2(num_qubits)) + 1 
# max_errors = (distance - 1) // 2
# err_cond = f"sum i 1 {num_qubits} (ex_(i)) <= 1 && sum i 1 {num_qubits} (ez_(i)) <= 1"
# decoder_cond = decode_cond_gen(surface_matrix_gen(distance))
# ## Test: Steane code 
# ### Precondition generation
# start = time.time()
# precond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

# program = """ for i in 1 to 7 do q_(i) *= ex_(i) X end; for i in 1 to 7 do q_(i) *= ez_(i) Z end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
# sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
# sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end; for i in 1 to 7 do q_(i) *= cz_(i) Z end"""

# postcond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """
# pre_tree, prog_tree, post_tree = precond_generator(program, precond, postcond)

# ### Reshape the generated precondition, extract classical part


# cass_transformer = qassertion2c(pre_tree)
# cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])

# cass_tree = simplifyeq().transform(cass_tree)
# solver = cvc5.Solver()
# cass_expr = tree_to_cvc5(cass_tree, {}, solver, 1)


# print(clean_cass)


# # ### SMT encoding

# # ## Error condition for successful decoding (Can be read from file)
# err_cond = """ sum i 1 7 (ex_(i)) <= 1 && sum i 1 7 (ez_(i)) <= 1 """
# # ## Decoding condition of a minimum-weight perfect matching (should be read from file)
# decoder_cond_bool = """ sz_(1) == cx_(1) @^ cx_(3) @^ cx_(5)@^ cx_(7) && sz_(2) == cx_(2) @^ cx_(3) @^ cx_(6) @^ cx_(7) && sz_(3) == cx_(4) @^ cx_(5) @^ cx_(6) @^ cx_(7) &&
# sx_(1) == cz_(1) @^ cz_(3) @^ cz_(5) @^ cz_(7)  && sx_(2) == cz_(2) @^ cz_(3) @^ cz_(6) @^ cz_(7) && sx_(3) == cz_(4) @^ cz_(5) @^ cz_(6) @^ cz_(7)"""

# decoder_cond_int = """ sum i 1 7 (cx_(i)) <= Min( sum i 1 7 (ex_(i)), 1) && sum i 1 7 (cz_(i)) <= Min( sum i 1 7 (ez_(i)), 1) """

# err_tree, _, decoder_tree_int = precond_generator('skip', err_cond, decoder_cond_int)
# _, _, decoder_tree_bool = precond_generator('skip', err_cond, decoder_cond_bool)


# # #### P_c: error condition
# variables_e = {} 
# err_expr = simplify(tree_to_cvc5(err_tree.children[0], variables_e,  3))

# # #### P_f decoding condition (divided into integer and boolean part to support different interpretation for addition)


# decoder_expr_int = tree_to_cvc5(decoder_tree_int.children[0],{}, 5)

# variables = {}

# decoder_expr_bool = simplify(tree_to_cvc5(decoder_tree_bool.children[0], variables, 5))
# decoding_formula = And(cass_expr, decoder_expr_int, decoder_expr_bool)

# print(cass_expr)
# print(decoder_expr_bool)
# print(err_expr)

# print(decoder_expr_bool)


# # F = err_expr
# G = decoding_formula1


# equivalence = ForAll(forall_var_list, Not(Implies(F, G)))

# solver = Solver()

# solver.add(equivalence)


# # Check satisfiability
# if solver.check() == sat:
#     print("Satisfiable")
#     model = solver.model()
#     print(model)
#     #print(model.eval(sum_c))
# else:
#     print("Unsatisfiable")
# end = time.time()
# print(end - start)