from lark import Lark, Tree, Token, Transformer
from transformer import 
#### The highest level of class object, the Hoare triple as the verification target
class HoareTriple:
    def __init__(self, pre, prog, post):
        self.pre = pre ## Initial expected precondition
        self.prog = prog ## Programs to be verified 
        self.post = post ## Initial postcondition

    def __str__(self):
        return "{" + str(self.pre) + "} " + str(self.prog) + " {" + str(self.post) + "}"