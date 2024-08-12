import re
from typing import List, Tuple, Union 

# Define token types

Token = Tuple[str, str]

reserved_words = {
    'if': 'IF',
    'else': 'ELSE',
    'while': 'WHILE',
    'for': 'FOR',
    'true': 'TRUE',
    'false': 'FALSE',
    '(-1)^': 'PHASE'
}
# Define Lexer 
def lexer(expression: str) -> List[Token]:
    token_specification = [
        ('NUM', r'\d+(\.\d*)?'), 
        ('NAME', r'[a-z][_0-9]*'),
        ('PAULI',r'[I|X|Y|Z]_[0-9]+'),
        ('OP', r'[+|\-|*|/|^|<|>|==|!=|&&|\|\||]'),
        # ('PLUS', r'\+'),('MINUS',r'\-'),('MULT', r'\*'),('DIV', r'/'),
        # ('LE',r'\<='), ('GE', r'\>='),('EQ', r'=='),('NE', r'!='),
        # ('AND',r'\&\&'), ('OR', r'\|\|'), ('EXP', r'\^'),
        ('LP', r'\('),
        ('RP', r'\)'),
        ('SKIP', r'[ \t\n]'),
        ('MISMATCH', r'.'),
    ]
    token_regex = '|'.join('(?P<%s>%s)' % pair for pair in token_specification)
    get_token = re.compile(token_regex).finditer
    tokens = []
    for match in get_token(expression):
        kind = match.lastgroup
        value = match.group()
        if kind == 'NAME':
            kind = reserved_words.get(value, 'NAME')
        elif kind == 'NUM':
            value = float(value) if '.' in value else int(value)
        elif kind == 'SKIP':
            continue
        elif kind == 'MISMATCH':
            raise RuntimeError(f'{value!r} unexpected')
        tokens.append((kind, value))
    return tokens 

# Define AST Node
class ASTNode: 
    pass
class BinOp(ASTNode):
    def __init__ (self, left: ASTNode, op: str, right: ASTNode):
        self.left = left
        self.op = op
        self.right = right
class UnaryOp(ASTNode):
    def __init__(self, op: str, expr: ASTNode):
        self.op = op
        self.expr = expr

# Leaf node classes 
class BoolLiteral(ASTNode):
    def __init__(self, value: bool):
        self.value = value
class Number(ASTNode):
    def __init__(self, value: Union[int, float]):
        self.value = value

class Name(ASTNode):
    def __init__(self, name: str):
        self.name = name
class Pauli(ASTNode):
    def __init__(self, name: str):
        self.name = name

#Parser
class Parser: 
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0

    def parse(self) -> ASTNode: 
        return self.bexpr()
    #bexpr = bterm &&/|| bterm
    #Parse the expressions
    def bexpr(self) -> ASTNode:
        node = self.bterm()
        while self.current_token_value in ('&&', '||'):
            op = self.current_token_value()
            self.eat('OP')
            node = BinOp(node, op = op, right = self.bterm())
        return node
    # bterm = !bterm | (bexpr) | true | false | aexpr <= aexpr | aexpr >= aexpr | aexpr == aexpr | aexpr != aexpr | pexpr
    def bterm(self) -> ASTNode:
        if self.current_token_value() == '!':
            op = self.current_token_value()
            self.eat('OP')
            node = UnaryOp(op = op, expr = self.bterm())
            return node
        elif self.current_token_value() == '(':
            self.eat('LP')
            node = self.bexpr()
            self.eat('RP')
            return node
        elif self.current_token_value() == 'true':
            node = BoolLiteral(True)
            self.eat('TRUE')
            return node
        elif self.current_token_value() == 'false':
            node = BoolLiteral(False)
            self.eat('FALSE')
            return node
        else: 
            node = self.aexpr()
            if self.current_token_value() in ('<','>','==','!='):
                op = self.current_token_value()
                self.eat('OP')
                node = BinOp(node, op, self.aexpr())
            return node
    #aexpr = aterm + aexpr | aterm - aexpr | aterm
    def aexpr(self) -> ASTNode:
        node = self.term()
        while self.current_token_value() in ('+','-','*','/'):
            op = self.current_token_value()
            self.eat('OP')
            node = BinOp(node, op, self.term())
        return node
    #Deal with Leaf nodes  
    def term(self) -> ASTNode:
        token_type = self.current_token_type()
        if token_type == 'NUM':
            node = Number(self.current_token_value())
            self.eat('NUM')
            return node 
        elif token_type == 'NAME':
            node = Name(self.current_token_value())
            self.eat('NAME')
            return node
        elif self.current_token_type == '-':
            self.eat('OP')
            node = UnaryOp('-', self.term())
            return node
        
        raise RuntimeError(f'Unexpected token {token_type}')
    
    #Token information
    def current_token(self) -> Token:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        else:
            return ('EOF', None)
    def current_token_type(self) -> str:
        return self.current_token()[0]
    def current_token_value(self) -> Union[str,int, float]:
        return self.current_token()[1]
    
    #Type check
    def eat(self, token_type: str):
        if self.current_token_type() == token_type:
            self.pos += 1
        else:
            raise RuntimeError(f'Expected {token_type} but got {self.current_token_type()}')
#Test 
if __name__ == '__main__':
    expression = 'x_1 + x_2 + x_3 < 1'
    tokens = lexer(expression)
    print(tokens)
    parser = Parser(tokens)
    AST = parser.parse()
    print(AST)