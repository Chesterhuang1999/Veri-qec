## A test file for Lark transformers 
from lark import Lark, Transformer, v_args, Tree, Token
from lark.reconstruct import Reconstructor
from parser_lark import get_parser
import re

parser = get_parser()

class Loops_transformer(Transformer):
    def __init__(self, var, value):
        self.var_obj = var
        self.value = value
    def var(self, args):
        print(args)
        if args[1] == self.var_obj.children[0]: 
            args[1] = Token('NUMBER', self.value)
        return Tree('var', args)

precond = """"""
program = """ for i in 1 to 3 do e_i := 0"""
postcond = """"""

triple = "{" + precond + "}" + program + "{" + postcond + "}"
tree = parser.parse(triple)
_, program_tree, _ = tree.children

for t in program_tree.children:
    if t.data == 'for':
        var, start, end, prog = t.children
        print(var, prog)
        #print(prog)
        for j in range(int(start), int(end) + 1):
            loop = Loops_transformer(var, j)

            prog1 = loop.transform(prog)
            print(prog1)
            str_prog1 = Reconstructor(parser = get_parser()).reconstruct(prog1)
            print(str_prog1)
    else: 
        pass 

# program_reconstruct = Reconstructor(parser = get_parser()).reconstruct(program)
# cleaned_program = re.sub(r'\s*_\s*','_', program_reconstruct)