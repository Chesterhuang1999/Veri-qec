#------------
# author: Chester Huang
# date: 2024.5.31
# version: 1.0.1
#------------

from lark import Lark, Transformer, v_args, Tree, Token
from lark.reconstruct import Reconstructor
from parser_lark import get_parser
import re

import time

parser = get_parser()
# Basic transformer to perform calculation
# @v_args(inline = True)
# class Calc(Transformer):
#     from operator import add, sub, mul, truediv as div, neg
#     number = int
#     def var(self, token):

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
    # def add(self, args):
    #     if isinstance(args[0], Token) or isinstance(args[1], Token):
    #         return Token('NUMBER', eval(args[0]) + eval(args[1]))
    #     return Tree('add', args)
    # def sub(self, args):
    #     if isinstance(args[0], Token) or isinstance(args[1], Token):
    #         return Token('NUMBER', eval(args[0]) - eval(args[1]))
    #     return Tree('sub', args)

# Substitution rule for unitary gates, currently support conditional pauli gate and clifford gate without condition
class Unitary(Transformer):
    def __init__(self, var, bexp, unit):
        self.var_obj = var
        self.bexp = bexp
        self.pauliop = unit
    def pauli(self, args):
        #var_name = self.var.children[0]
        var_ind = self.var_obj.children[1]
        pauliop = self.pauliop.children[0]
        #Substitution
        if pauliop in ("X","Y","Z"):
            if len(args) == 2: # no phase before the stabilizer
                if(args[0] == pauliop or args[1] != var_ind):
                    return Tree('pauli', args)
                else:
                    return Tree('pauli', [self.bexp, args[0], args[1]])
            elif len(args) == 3: # phase before the stabilizer
                if(args[1] == pauliop or args[2] != var_ind):
                    return Tree('pauli', args)
                else:
                    if args[0].data == 'add':
                        args[0].children = [self.bexp] + args[0].children 
                        bexpr = args[0]
                    else:
                        bexpr = Tree('add', [self.bexp, args[0]])
                    return Tree('pauli', [bexpr,args[1],args[2]])
            return Tree('pauli', args)
        # Version I, don't support conditional clifford
        elif pauliop == "H":
            dict = {"X": "Z", "Y": "Y", "Z" :"Z"}
            if(len(args) == 2):
                op = dict[args[0]]
                if(args[0] == "Y"):
                    return Tree('pauli', [1, op, args[1]])
                else:
                    return Tree('pauli', [op, args[1]])
                
            elif(len(args) == 3):
                op = dict[args[1]]
                if(args[0] == "Y"):
                    bexp = Tree('add', [1, args[0]])
                    return Tree('pauli', [bexp, op, args[1]])
                else:
                    return Tree('pauli', [bexp, op, args[1]])
        elif pauliop == "S":
            dict = {"X": "Y", "Y": "X", "Z": "Z"}
            if(len(args) == 2):
                op = dict[args[0]]
                if(args[0] == "Y"):
                    return Tree('pauli', [1, op, args[1]])
                else:
                    return Tree('pauli', [op, args[1]])
            elif(len(args) == 3):
                op = dict[args[1]]
                if(args[0] == "Y"):
                    bexp = Tree('add', [1, args[0]])
                    return Tree('pauli', [bexp, op, args[1]])
                else:
                    return Tree('pauli', [bexp, op, args[1]])  
            else: 
                raise ValueError("Invalid number of arguments")
        else: 
            return Tree('pauli', args)    
# Measure rule substitution (need to deal with big operator)
class Measure(Transformer):
    def __init__(self, var, pexpr):
        self.var_obj = var
        self.pexpr_obj = pexpr
    def condition(self, args):
        if args[0].data == "bigor":
            length = len(args[0].children)
            children = [None] * (length + 1)
            for i in range(length - 1):
                children[i + 1] = args[0].children[i]
            children[0] = self.var_obj
            temp1 = args[0].children[length -  1]
            pexpr = self.pexpr_obj
            temp2 = [self.var_obj] + pexpr.children[0].children
            pexpr.children[0] = Tree('pauli',temp2)
            children[length] = Tree('and',[pexpr, temp1])
            return Tree('condition',[Tree('bigor', children)])
        else: 
            pexpr = self.pexpr_obj
            temp = Tree('pauli', [self.var_obj]+ pexpr.children[0].children)
            pexpr.children[0] = temp
            temp1 = Tree('and',[pexpr,args[0]])
            return Tree('condition', [Tree('bigor', [self.var_obj, temp1])]) 
        

#ToDo: Substitution of pauli operator indexes
class Loops(Transformer):
    def __init__(self, var, value):
        self.var_obj = var
        self.value = value
    def var(self, args):
        if args[1] == self.var_obj.children[0]: 
            args[1] = Token('NUMBER', self.value)
        return Tree('var', args)

### Additional transformers to reformulate the assertion to a compact form
class Combinephase(Transformer):
    def pexpr(self, children):
        if(children[0].data != 'pauli'):
            return Tree('pexpr', children)
        else: 
            length = len(children)
            temp = []
            for i in reversed(range(length)):
                op = children[i]
                if len(op.children) > 2:
                    phase = op.children[0]
                    if(phase.data == 'add'):
                        for j in range(len(phase.children)):
                            temp.append(phase.children[j])
                    else:
                        temp.append(phase)
                    if( i > 0):
                        op.children.pop(0)
                    else:
                        op.children[0] = Tree('add', temp)
            return Tree('pexpr', children)
                    


## Perform transformations 
def assign(t, assertion_tree):
    var = t.children[0]
    new_expr = t.children[1]
    assign_transformer = Assign(var, new_expr)
    #print(assertion_tree)
    return assign_transformer.transform(assertion_tree)
def unitary(t, assertion_tree):
    length = len(t.children)
    if(length == 3):
        var = t.children[0]
        bexp = t.children[1]
        unit = t.children[2]
    else: 
        var = t.children[0]
        bexp = 1
        unit = t.children[1]
    unitary_transformer = Unitary(var, bexp, unit)
    return unitary_transformer.transform(assertion_tree)

def meas(t, assertion_tree):
    var = t.children[0]
    pexpr = t.children[1]
    meas_transformer = Measure(var, pexpr)
    return meas_transformer.transform(assertion_tree)


# Processing the postcondition via Hoare rules 
def process(program_tree, assertion_tree):
    command_list =  program_tree.children
    length = len(command_list)
    for i in reversed(range(length)):
        t = command_list[i]
        #assertion_tree = inference(t, assertion_tree)
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
        #print(prog)
            for j in range(int(start), int(end) + 1):
                loop_transformer = Loops(var, j)
                child_prog_mod = loop_transformer.transform(child_prog)
                assertion_tree = process(child_prog_mod, assertion_tree)
    return assertion_tree
            # switch_dict = {
            # 'assign': assign,
            # 'unitary': unitary,
            # 'meas': meas
            # }
            # var, start, end, prog = t.children
            # fun = switch_dict.get(prog.data)
            # print(fun)
            


# Generate the precondition from the program and the postcondition
def precond_generator(program: str, precond: str, postcond: str):
    triple = "{" + precond + "}" + program + "{" + postcond + "}"
    tree = parser.parse(triple)
    _, program_tree, assertion_tree = tree.children
    ### Record the time for processing the AST
    start = time.time()
    assertion_tree = process(program_tree, assertion_tree)
    phase_transformer = Combinephase()
    assertion_tree = phase_transformer.transform(assertion_tree)
    end = time.time()
    print(end - start)
    return program_tree, assertion_tree


# Test examples
start = time.time()
precond = ''''''
program = """ for i in 1 to 3 do q_i *= e_i X end; for i in 1 to 3 do q_i *= c_i X end"""
### ''' c_1 := (e_1 & !e_2); q_1 *= c_1 Z; q_2 *= c_2 Z; q_3 *= c_3 Z'''
postcond = '''  (-1)^(b_1) Z_1 && Z_1Z_2 && Z_2Z_3 '''
program_tree, assertion_tree = precond_generator(program, precond, postcond)
end = time.time()
print(end - start)
## A reconstructor for visualizing the generated precondition.
## VC transformation will still be performed on the AST. 
#assertion_reconstruct = Reconstructor(parser = get_parser()).reconstruct(assertion_tree)
#cleaned_assertion = re.sub(r'\s*_\s*','_', assertion_reconstruct)

#print(cleaned_assertion)
#print(end - start)

## Archive for test examples
# for i in 1 to 3 do e_i := 0 end; e_1 := 1; for i in 1 to 3 do q_i *= e_i X end; 
# s_1 := meas Z_1Z_2; s_2 := meas Z_2Z_3;