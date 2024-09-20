#------------
# author: Chester Huang
# date: 2024.7.16
# version: 1.1.0
#------------

### Transformers of the parse tree for assertions based on the inference rules. 


## Temporarily, it is used as a test file for bitstring representation of stabilizers


from lark import Transformer, Tree, Token
#from lark.visitors import merge_transformers
from lark.reconstruct import Reconstructor
from parser_bexp2 import get_parser
#from concurrent.futures import ThreadPoolExecutor
#import re
import time
#import cProfile
parser = get_parser()


## Customized function for operator overloading and useful gadgets
def tree_sorted_key(tree):
    return int(tree.children[-1]) if tree.data == 'pauli' else None

def find_pos(list, index):
    l = 0 
    m = len(list) - 1
    while l <= m:
        mid = (l + m) // 2
        if int(list[mid].children[-1]) == index:
            return mid
        elif int(list[mid].children[-1]) < index:
            l = mid + 1
        else:
            m = mid - 1
    return l
### Substitution/Transformation rules
# A transformer class to perform substitution on the tree
class Assign(Transformer):
    def __init__(self, var_name, new_expr):
        self.var_name = var_name
        self.new_expr = new_expr
    # Assign rule substitution
    def var(self, children):
        name = self.var_name.children[0]
        index = self.var_name.children[1]
        if children[0] == name and children[1] == index: 
            return self.new_expr
        return Tree('var', children)



# Substitution rule for unitary gates, currently support conditional pauli gate and clifford gate without condition
class Unitary(Transformer):
    def __init__(self, var, bexp, unit):
        self.var_obj = var
        self.bexp = bexp
        self.unit = unit
    def pexpr(self, args):
        op = self.unit
        if op == 'CNOT':
            [q1, q2] = self.var_obj
            v_ind1 = int(q1.children[1])
            v_ind2 = int(q2.children[1])
            z1, x1, z2, x2 = 0, 0, 0, 0
            pos1 = -1
            pos2 = -1
            for i in range(len(args)):
                if int(args[i].children[-1])== v_ind1:
                    z1 = int(args[i].children[-3])
                    x1 = int(args[i].children[-2])
                    pos1 = i ## position of pauli on q1
                elif int(args[i].children[-1]) == v_ind2:
                    z2 = int(args[i].children[-3])
                    x2 = int(args[i].children[-2])
                    pos2 = i ## position of pauli on q2
            if (z1, x1, z2, x2) == (0, 0, 0, 0):
                return Tree('pexpr', args)
            else:
                z1 = z1 ^ z2
                x2 = x1 ^ x2 
                phase = args[0].children[0] if len(args[0].children) == 4 else Token('NUMBER',0)
                if pos1 == -1: ## the stabilizer doesn't act on q1
                    if (z1,x1) != (0,0):
                        args.insert(find_pos(args, v_ind1), Tree('pauli',[Token('NUMBER', z1), Token('NUMBER', x1), Token('NUMBER', v_ind1)])) 
                else:
                    if (z1, x1) == (0,0):
                        args.pop(pos1)
                    else:
                        args[pos1] = Tree('pauli', [Token('NUMBER', z1), Token('NUMBER', x1), Token('NUMBER', v_ind1)])
                
                if pos2 == -1:
                    if (z2, x2) != (0,0):
                        args.insert(find_pos(args, v_ind2), Tree('pauli',[Token('NUMBER', z2), Token('NUMBER', x2), Token('NUMBER', v_ind2)]))
                else:
                    if (z2, x2) == (0,0):
                        args.pop(pos2)
                    else:
                        args[pos2] = Tree('pauli', [Token('NUMBER', z2), Token('NUMBER', x2), Token('NUMBER', v_ind2)])
                if x1 == 1 and z2 == 1 and x2 == z1:
                    phase = Tree('add', [phase, Token('NUMBER',1)])
                if phase != 0:
                    if len(args[0].children[0]) == 4:
                        args[0].children[0] = phase
                    else:
                        args[0].children.insert(0, phase)
                return Tree('pexpr', args)
        else:
            return Tree('pexpr', args)         
    def pauli(self, args):
        #var_name = self.var.children[0]
        op = self.unit
        if op == "CNOT": # 2-qubit CNOT gate
            return Tree('pauli', args)
        else: # 1-qubit gates
            v_ind = int(self.var_obj.children[1])
            p_ind = int(args[-1])
            stab_z, stab_x = int(args[-3]), int(args[-2])
            if p_ind != v_ind:
                return Tree('pauli', args)
            if op in ("X","Y","Z"):
                x_dict = {"X": 1, "Y": 1, "Z": 0}
                z_dict = {"X": 0, "Y": 1, "Z": 1}
                xflip = z_dict[op] and stab_x
                zflip = x_dict[op] and stab_z
                if (xflip, zflip) in ((1,0), (0,1)):
                    if(len(args) == 3):
                        return Tree('pauli', [self.bexp] + args)
                    bexpr = Tree('xor', [self.bexp, args[0]])
                    # bexpr = args[0] 
                    # if bexpr.data == 'add':
                    #     bexpr = Tree('add', [self.bexp, bexpr])
                    #     #bexpr.children = [self.bexp] + args[0].children 
                    # else:
                    #     bexpr = Tree('add', [self.bexp, args[0]])

                    return Tree('pauli',[bexpr] + args[1:])
                else:
                    return Tree('pauli', args)
            elif op == "H": # Hadamard gate(conditional)
                if stab_z == 1 and stab_x == 1: # Y stabilizer
                    if(len(args) == 3):
                        return Tree('pauli', [self.bexp] + args)
                    #else:
                        # if args[0].data == 'add':
                        #     bexpr = Tree('add', [self.bexp, args[0]])
                        #     #args[0].children = [self.bexp] + args[0].children 
                        #     #bexpr = args[0]
                        # else:
                    bexpr = Tree('xor', [self.bexp, args[0]])
                    return Tree('pauli',[bexpr] + args[1:])
                elif stab_z == 1: # Z stabilizer
                    if self.bexp == 1:
                        args[-3] = Token('NUMBER','0')
                        args[-2] = Token('NUMBER','1')
                    else: 
                        args[-3] = Tree('neg', [self.bexp])
                        args[-2] = self.bexp
                    return Tree('pauli', args)
                else: 
                    if self.bexp == 1:
                        args[-3] = Token('NUMBER','1')
                        args[-2] = Token('NUMBER','0')
                    args[-3] = self.bexp
                    args[-2] = Tree('neg', [self.bexp])
                    return Tree('pauli', args)
                
            else: # S gate(conditional)
                if stab_x == 0:
                    return Tree('pauli', args)
                elif stab_z == 0: #X
                    args[-2] = self.bexp
                    return Tree('pauli', args)
                else:
                    args[-2] = self.bexp
                    if(len(args) == 3):
                        return Tree('pauli', [self.bexp] + args)
                    else:
                        if args[0].data == 'xor':
                            bexpr = Tree('xor', [self.bexp] + args[0])  
                            #args[0].children = [self.bexp] + args[0].children 
                            #bexpr = args[0]
                        else:
                            bexpr = Tree('xor', [self.bexp, args[0]])
                        return Tree('pauli',[bexpr] + args[1:])
        


# Measure rule substitution (need to deal with big operator)
class Measure(Transformer):
    def __init__(self, var, pexpr):
        self.var_obj = var
        self.pexpr_obj = pexpr
        self.ismeasure = 0  # record if the measurement op already exists in assertion
    def pexpr(self, args):
        child = self.pexpr_obj.children
        if len(args) == len(child) and all(eq_pauliop(arg,ch) for arg,ch in zip(args, child)):
                if len(args[0].children) == 4:
                    args[0].children[0] = self.var_obj
                else:
                    args[0].children.insert(0, self.var_obj)
                self.ismeasure = 1
        return Tree('pexpr', args)
    def condition(self, args):
        if args[0].data == "bigor":
            length = len(args[0].children)
            children = [None] * (length + 1)
            # add new variable in subscripts of bigor
            for i in range(length - 1):
                children[i + 1] = args[0].children[i]
            children[0] = self.var_obj
            temp1 = args[0].children[length -  1]
            children[length] = temp1 
            if self.ismeasure == 0:
                # create the new pauli operator
                pexpr = self.pexpr_obj
                temp2 = [self.var_obj] + pexpr.children[0].children
                pexpr.children[0] = Tree('pauli',temp2)
                children[length] = Tree('and',[pexpr, temp1])
            else:
                children[length] = temp1
            return Tree('condition',[Tree('bigor', children)])
        else: 
            if self.ismeasure == 0:
                pexpr = self.pexpr_obj
                temp = Tree('pauli', [self.var_obj]+ pexpr.children[0].children)
                pexpr.children[0] = temp
                temp1 = Tree('and',[pexpr,args[0]])
                return Tree('condition', [Tree('bigor', [self.var_obj,temp1])])
            else:
                return Tree('condition', [Tree('bigor', [self.var_obj, args[0]])]) 
        

#ToDo: Substitution of pauli operator indexes
class Loops(Transformer):
    def __init__(self, var, value):
        self.var_obj = var
        self.value = value
    def var(self, args):
        if args[1] == self.var_obj: 
            args[1] = Token('NUMBER', self.value)
        return Tree('var', args)



## Additional transformers to reformulate the assertion to a compact form
### Combine the phases in the same stabilizer
class Combinephase(Transformer):
    def pexpr(self, children):
        if(children[0].data != 'pauli'):
            return Tree('pexpr', children)
        else: 
            length = len(children)
            temp = None
            for i in reversed(range(length)):
                op = children[i]
                if len(op.children) > 3:
                    phase = op.children.pop(0)
                    temp = phase if temp == None else Tree('xor', [phase, temp])
                    # if phase.data == 'add':
                    #     temp.extend(phase.children)
                    #     # for j in range(len(phase.children)):
                    #     #     temp.append(phase.children[j])
                    # else:
                    #     temp.append(phase)
                    if i == 0:
                        op.children.insert(0, temp)
                    # and temp == phase:
                    #     op.children.insert(0, temp)
                    # elif i == 0 and len(temp) == 1:
                    #     op.children.insert(0, temp[0])
            return Tree('pexpr', children)

### Simplify the phase of each pauli, eliminate even terms                    
# class Simphase(Transformer):
#     def pexpr(self, children):
#         if(children[0].data != 'pauli' or len(children[0].children) == 3):
#             return Tree('pexpr', children)
#         else:
#             phase = children[0].children[0]
#             cache_number = 0
#             for i in range
#             return Tree('pexpr', children)

# def calc(t):
#     num_cache = []
#     sym_cache = []
#     if(isinstance(t, Token)):
#         return t
#     elif t.data == 'var':
#         return t
#     else: 
#         for c in t.children: 
#             if isinstance(calc(c), Token):
#                 num_cache.append(calc(c))
#             elif c.data == 'var':
#                 sym_cache.append(calc(c))
#             else: 
#             return 
            
                
## Perform transformations 
def assign(t, assertion_tree):
    var = t.children[0]
    new_expr = t.children[1]
    assign_transformer = Assign(var, new_expr)
    return assign_transformer.transform(assertion_tree)

def unitary(t, assertion_tree):
    #length = len(t.children)
    unit = t.children[-1]
    if unit.value == 'CNOT':
        bexp = t.children[-2] if len(t.children) == 4 else 1
        var = t.children[:2]
    else:
        bexp = t.children[-2] if len(t.children) == 3 else 1
        var = t.children[0]

    unitary_transformer = Unitary(var, bexp, unit)
    unit = unitary_transformer.__mul__(Combinephase())
    return Combinephase().transform(unitary_transformer.transform(assertion_tree))

def meas(t, assertion_tree):
    var = t.children[0]
    pexpr = t.children[1]
    meas_transformer = Measure(var, pexpr)
    return Combinephase().transform(meas_transformer.transform(assertion_tree))


# Processing the postcondition via Hoare rules 

def process(program_tree, assertion_tree):
    command_list =  program_tree.children
    length = len(command_list)
    for i in reversed(range(length)):
        t = command_list[i]
        if t.data == 'assign':
            assertion_tree = assign(t, assertion_tree)
            # assertion_reconstruct = Reconstructor(parser = get_parser()).reconstruct(assertion_tree)
            # cleaned_assertion = re.sub(r'\s*_\s*','_', assertion_reconstruct)
            # print(cleaned_assertion)
        elif t.data == 'unitary':
            assertion_tree = unitary(t,assertion_tree)
        elif t.data == 'meas':
            assertion_tree = meas(t,assertion_tree)
        elif t.data == 'if':
            b, prog1, prog2 = t.children
        elif t.data == 'for':
            var, start, end, child_prog = t.children
            for j in range(int(start), int(end) + 1):
                loop_transformer = Loops(var, j)
                child_prog_mod = loop_transformer.transform(child_prog)
                assertion_tree = process(child_prog_mod, assertion_tree)
    return assertion_tree



# Check the equality of two pauli expressions, without considering the phase            
def eq_pauliop(u: Tree,v: Tree):
   return all(u.children[-i] == v.children[-i] for i in range(1, 4))
    
def eq_pexpr(u: Tree, v: Tree):
    if len(u.children) != len(v.children): 
        return False
    return all(eq_pauliop(u.children[i],v.children[i]) for i in range(len(u.children)))



# Generate the precondition from the program and the postcondition

def precond_generator(program: str, precond: str, postcond: str):
    t1 = time.time()
    triple = "{" + precond + "}" + program + "{" + postcond + "}"
    tree = parser.parse(triple)
    pre_tree, program_tree, post_tree = tree.children
    t2 = time.time()
    ### Record the time for processing the AST
    post_tree = process(program_tree, post_tree)
    t3 = time.time()
    #print(end - start)
    return pre_tree, program_tree, post_tree



#####################################################        
#Test example: Steane code
# precond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

# program = """ for i in 1 to 7 do q_(i) *= ex_(i) X end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
# sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
# sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end"""

# postcond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """



# Test example: Repetition code
# precond = """ (-1)^(b_(1))(1,0,3) && (1,0,1)(1,0,2) && (1,0,2)(1,0,3)"""

# program = """for i in 1 to 3 do q_(i) *= ez_(i) Z end; sx_(1) := meas (0,1,1)(0,1,2); sx_(2) := meas (0,1,2)(0,1,3); for i in 1 to 3 do q_(i) *= cz_(i) Z end"""

# postcond = """(-1)^(b_(1))(0,1,1)(0,1,2)(0,1,3) && (0,1,1)(0,1,2) && (0,1,2)(0,1,3)"""
# start = time.time()
# t1, t2, _, program_tree, assertion_tree = precond_generator(program, precond, postcond)
# print(t1, t2)
# end = time.time()
# print(program_tree)
# print(assertion_tree)
# print(end - start)
# ## A reconstructor for visualizing the generated precondition.
# ## VC transformation will still be performed on the AST. 
# assertion_reconstruct = Reconstructor(parser = get_parser()).reconstruct(assertion_tree)
# cleaned_assertion = re.sub(r'\s*_\s*','_', assertion_reconstruct)

# print(cleaned_assertion)


