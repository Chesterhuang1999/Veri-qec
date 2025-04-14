#------------#
# Developer: Chester Huang
# date: 2024.7.20
# Description: Use heuristic rules to transform VCs generated into classical assertions
#------------#


from lark import Transformer, v_args, Tree, Token

from copy import deepcopy
from transformer import precond_generator, eq_pauliop, eq_pexpr, recon_string
from Dataset import linalg_GF
from collections import defaultdict
from z3 import *
from condition import *

## Overload operators ##
def __xor__(a: Token, b: Token):
    assert a.type == 'NUMBER' and a.type == 'NUMBER'
    return Token('NUMBER', int(a.value) ^ int(b.value))
### Heuristic rule I: judge whether stabilizers in two assertions belong to the same group (or same) 
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

### Using greedy to find the representation of another set of stabilizers ###
def find_stab_rep(stab_dict, stab_list, s):
    l = len(s.children)
    phase = Token('NUMBER','0')
    is_matched = 0
    # stab_dict_cpy = stab_dict.deepcopy()
    stab_dict_cpy = copy.deepcopy(stab_dict)
    while is_matched == 0: ## Find if the stabilizer is in current list
        for s_c in stab_dict_cpy[l]:
            if eq_pexpr(s, s_c):
                if len(s_c.children[0].children) == 4:
                    phase = s_c.children[0].children[0]
                
                is_matched = 1
                
                break
        if is_matched == 1:
            break
        ## Not found, extend the list by multiplying stabilizers, and continue
        stab_list_cpy = copy.deepcopy(stab_list)
        length = len(stab_list_cpy)
        for i in range(length):
            for j in range(1 + i, length):
                temp_mul = stab_mul(stab_list_cpy[i],stab_list_cpy[j])
                if len(temp_mul.children) > 0:
                    stab_dict_cpy[len(temp_mul.children)].add(temp_mul)
                    stab_list.append(temp_mul)
            
    return phase
     

### Canonical form of stabilizers,
#  designed to find the linear transformation between two sets of generators ###
### The generators can be viewed as two binary matrices, 
# and the transformation is the linear transformation between two binary matrices. ###
def canonical_form(stab_list):
    stab_list = sorted(stab_list, key = lambda x: int(x.children[0].children[-1].value)) 
    max_ind = 1
    for stab in stab_list:
        max_temp = max([int(child.children[-1].value) for child in stab.children])
        if max_temp > max_ind:
            max_ind = max_temp
    stabs_mat_rep = np.zeros([len(stab_list), 2 * max_ind], dtype = int)
    phase_rep = []
    for i, stab in enumerate(stab_list):
        paulis = stab.children
        phase = stab.children[0].children[0] if len(stab.children[0].children) == 4 else Token('NUMBER','0')
        phase_rep.append(phase)
        for p in paulis:
            index = int(p.children[-1].value)
            x = int(p.children[-2].value)
            z = int(p.children[-3].value)
            stabs_mat_rep[i][index -1] = x
            stabs_mat_rep[i][index + max_ind - 1] = z
        
    return stabs_mat_rep, phase_rep

### Linear transformation between two set of generators. P = LQ, so Q is precondition, so is stab_mat1 ###
def linear_transform(stab_mat1, stab_mat2, phase1, phase2):
    Qt = stab_mat1.T
    Pt = stab_mat2.T 
    n, k = Qt.shape ## n: 2*N, N is the number of qubits, k is the number of generators
    L = np.zeros((k, k), dtype = int)
    for i in range(k):
        rhs = Pt[:,i].reshape(-1,1)
        aug = np.concatenate((Qt, rhs), axis = 1)
        aug, sol = linalg_GF.aug_Gaussian(aug, k)
        L[:,i] = sol.reshape(-1)
    Lt = L.T
    eq_tree = 0    
    for i in range(k):
        cur_sum = Token('NUMBER','0')
        for j in range(k):
            if Lt[i][j] == 1 and phase1[j] != Token('NUMBER','0'):
                if cur_sum == Token('NUMBER','0'):
                    cur_sum = phase1[j]
                else:
                    cur_sum = Tree('add', [phase1[j], cur_sum])
        if eq_tree == 0:
            eq_tree = Tree('eq', [phase2[i], cur_sum])
        else:
            eq_tree = Tree('cap', [Tree('eq', [phase2[i], cur_sum]), eq_tree])
    return L.T, eq_tree

### Check if two pauli strings commute ###
def commute(u: Tree, v: Tree):

    u_dict = {}
    for child in u.children:
        index = child.children[-1]
        
        u_dict[index] = child
    mul = 1
    for child in v.children:
        index = child.children[-1]
       
        if index in u_dict and u_dict[index] != child:
            mul = -mul   
    return mul

### Multiplication of stabilizers ###
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
    
    ## Multiply in turns and pay attention to phases
    stab_new = []
    isphase = 0
    for i in stab_dict.keys():
        temp = stab_dict[i]
        if len(temp) == 1:
            if isphase == 0:
                if len(temp[0].children) == 4:
                    stab_new.append(temp[0])
                    isphase = 1
                else:
                    if phase != None:
                        new = Tree('pauli',[phase] + temp[0].children)
                        isphase = 1
                    else:
                        new = temp[0]
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
    stab_new = sorted(stab_new, key = lambda x: int(x.children[-1].value))
    
    return Tree('pexpr', stab_new)

### Transformation I: assertion with phase assembled implies the original assertion ###
class qassertion2c(Transformer):
    def __init__(self, base):
        self.base = base
        self.dict, self.list = stab_set_gen(base)
    def pexpr(self, args):  
        
        dict_temp = self.dict
        list_temp = self.list
        phase_desired = find_stab_rep(dict_temp, list_temp, Tree('pexpr', args))
        
        # extract the phase
        phase = Token('NUMBER','0')
        if len(args[0].children) == 4:
            phase = args[0].children[0]
            
        ## generate the condition
        return Tree('eq', [phase_desired, phase])

### A modified version of the classical VC generation ###

def Qass2c(pre_tree, post_tree):
    stab_mat_rep1, phase_rep1 = canonical_form(pre_tree)
    stab_mat_rep2, phase_rep2 = canonical_form(post_tree)
    L, eq_tree = linear_transform(stab_mat_rep1, stab_mat_rep2, phase_rep1, phase_rep2)

    return simplifyeq().transform(eq_tree)


### Simplification for classical assertion ###
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

### Eliminate same terms and redundant 0s in both sides of eq/leq ###
class simplifyeq(Transformer):
    @v_args(inline=True)
    def eq(self, l, r):
        left_terms = self.flatten_terms(l)
        right_terms = self.flatten_terms(r)
        common_terms = self.find_common_terms(left_terms, right_terms)
        lterms = [term for term in left_terms if term not in common_terms]
        rterms = [term for term in right_terms if term not in common_terms] 
        if(Token('NUMBER','0') in lterms):
            lterms.remove(Token('NUMBER','0'))
        if(Token('NUMBER','0') in rterms):
            rterms.remove(Token('NUMBER','0'))
        lterms, rterms = self.swap_terms(lterms, rterms) 
        if len(lterms) == 0 and len(rterms) == 0:
            return Tree('true', [])
        else:
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
        



