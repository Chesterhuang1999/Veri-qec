
#------------
# author: Chester Huang
# date: 2024.7.20
# version: 1.2.0
#------------


#Introduction: This file use heuristic rules to transform VCs generated into classical assertions
#and encode them into Z3 formulas

from lark import Transformer, v_args, Tree, Token
#from lark.reconstruct import Reconstructor
#from parser_bexp2 import get_parser
from transformer import precond_generator, eq_pauliop, eq_pexpr, recon_string

from collections import defaultdict
from z3 import *
from condition import *

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
    stab_dict_cpy = stab_dict.copy()
    while is_matched == 0:
        for s_c in stab_dict_cpy[l]:
            if eq_pexpr(s, s_c):
                if len(s_c.children[0].children) == 4:
                    phase = s_c.children[0].children[0]
                #phase_set.append((s,phase))
                is_matched = 1
                stab_dict_cpy[l].remove(s_c) 
                break
        if is_matched == 1:
            break
        stab_list_cpy = stab_list.copy()
        length = len(stab_list_cpy)
        for i in range(length):
            for j in range(1 + i, length):
                temp_mul = stab_mul(stab_list_cpy[i],stab_list_cpy[j])
                if len(temp_mul.children) > 0:
                    stab_dict_cpy[len(temp_mul.children)].add(temp_mul)
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
        # print(self.dict, self.list)
        dict_temp = self.dict
        list_temp = self.list
        phase_desired = find_stab_rep(dict_temp, list_temp, Tree('pexpr', args))
        
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
        



# # ## Test: Steane code 
# # ### Precondition generation
# # start = time.time()
# # precond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# # &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

# # program = """ for i in 1 to 7 do q_(i) *= ex_(i) X end; for i in 1 to 7 do q_(i) *= ez_(i) Z end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
# # sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
# # sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end; for i in 1 to 7 do q_(i) *= cz_(i) Z end"""

# # postcond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# # &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """
# # pre_tree, prog_tree, post_tree = precond_generator(program, precond, postcond)


if __name__ == '__main__':
    precond = """ (-1)^(b_(1))(0,1,1) && (0,1,1)(0,1,2) && (0,1,2)(0,1,3)"""

    program = """for i in 1 to 3 do q_(i) *= ez_(i) Z end; s_(1) := meas (0,1,1)(0,1,2); s_(2) := meas (0,1,2)(0,1,3); for i in 1 to 3 do q_(i) *= cz_(i) Z end;
    for i in 1 to 3 do q_(i) *= ez_(i + 3) Z end; s_(3) := meas (0,1,1)(0,1,2); s_(4) := meas (0,1,2)(0,1,3); for i in 1 to 3 do q_(i) *= cz_(i+3) Z end"""

    postcond = """(-1)^(b_(1))(0,1,1) && (0,1,1)(0,1,2) && (0,1,2)(0,1,3)"""
    start = time.time()
    pre_tree, program_tree, assertion_tree, auxes = precond_generator(program, precond, postcond)
    # print(recon_string(assertion_tree))
    cass_transformer = qassertion2c(pre_tree)
    cass_tree = cass_transformer.transform(assertion_tree.children[0].children[-1])
    cass_tree = simplifyeq().transform(cass_tree)
    
    # print(recon_string(cass_tree))
    for i, aux in enumerate(auxes):
        cass_transformer = qassertion2c(pre_tree)
        aux = cass_transformer.transform(aux)
        aux = simplifyeq().transform(aux)
        print(recon_string(aux))    



