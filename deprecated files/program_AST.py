import re
from typing import List, Tuple, Union 
import ply.lex as lex
# Define token types

Token = Tuple[str, Union[str,int, float]]

reserved_words = {
    'if': 'IF',
    'then': 'THEN',
    'else': 'ELSE',
    'while': 'WHILE',
    'do': 'DO',
    'for': 'FOR',
    'true': 'TRUE',
    'false': 'FALSE',
    'ph': 'PHASE',
    'meas': 'MEASURE'
}
# Define Lexer 
def lexer(expression: str) -> List[Token]:
    token_specification = [
        ('NUM', r'\d+(\.\d*)?'), 
        ('NAME', r'[a-zA-Z](_)?[0-9]*'),
        ('PAULI',r'[I|X|Y|Z](_)?[0-9]*'),
        ('UNITARY', r'[H|S|CNOT|T]'),
        ('ASSIGN', r'\:\='),
        ('UOP', r'\*\='),
        ('OP', r'<=|>=|==|!=|\&\&|\|\||[!|-|+|*|/|^|<|>|=|&||]'),
        ('SEMI',  r';'),
        # ('PLUS', r'\+'),('MINUS',r'\-'),('MULT', r'\*'),('DIV', r'/'),
        # ('LE',r'\<='), ('GE', r'\>='),('EQ', r'=='),('NE', r'!='),
        # ('AND',r'\&\&'), ('OR', r'\|\|'), ('EXP', r'\^'),
        ('LP', r'\('),
        ('RP', r'\)'),
        ('SKIP', r'[ \t\n]'),
        ('MISMATCH', r'.'),
    ]
    reserved_regex = '|'.join(f'(?P<{pair[1]}>{pair[0]})' for pair in reserved_words.items())
    token_regex = '|'.join(f'(?P<{pair[0]}>{pair[1]})' for pair in token_specification)
    combined_regex = f'{reserved_regex}|{token_regex}'
    get_token = re.compile(combined_regex).finditer
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
# Assertion & Pauli syntax 
class BinOp(ASTNode):
    def __init__ (self, left: ASTNode, op: str, right: ASTNode):
        self.left = left
        self.op = op
        self.right = right
class UnaryOp(ASTNode):
    def __init__(self, op: str, expr: ASTNode):
        self.op = op
        self.expr = expr
class Pauliexp(ASTNode):
    def __init__(self, phase: ASTNode, expr: ASTNode):
        self.phase = phase
        self.expr = expr
class Pauliproduct(ASTNode):
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right
#Program syntax
class Unitary(ASTNode):
    def __init__(self, var: ASTNode, cond: ASTNode, expr: ASTNode):
        self.var = var
        self.cond = cond
        self.expr = expr
class Measure(ASTNode):
    def __init__(self, var: ASTNode, expr: ASTNode):
        self.var = var
        self.expr = expr
class Assign(ASTNode):
    def __init__(self, var: ASTNode, expr: ASTNode):
        self.var = var 
        self.expr = expr
class Var(ASTNode):
    def __init__(self, token):
       self.token = token
       self.value = token[1]
# tprog: IF-T then prog1 fprog: IF-F then prog2
class IF(ASTNode):
    def __init__(self, cond: ASTNode, prog1, prog2):
        self.cond = cond
        self.tprog = prog1
        self.fprog = prog2
class WHILE(ASTNode):
    def __init(self, cond: ASTNode, prog):
        self.cond = cond
        self.prog = prog
#Leaf node classes
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
class UNITARY(ASTNode):
    def __init__(self, name: str):
        self.name = name
#Parser
class Program_Parser: 
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0

    def parse(self): 
        node = self.program()
        if self.current_token_type() != 'EOF':
            raise RuntimeError(f'Unexpected token {self.current_token_type()}')
        return node
    # program = statement | statement ; program
    def program(self):
        node = self.statement()
        results = [node]
        while self.current_token_value() == ';':
            self.eat('SEMI')
            results.append(self.statement())
        return results
    # statement = unitary | measure | assign | If | While
    def statement(self) -> ASTNode:
        left = self.var()
        if self.current_token_value() == ':=':
            self.eat('ASSIGN')
            if self.current_token_value() == 'meas':
                self.eat('MEASURE')
                right = self.pauli()
                return Measure(left, right)
            else:
                right = self.atom()
                return Assign(left, right)
        elif self.current_token_value() == '*=':
            self.eat('UOP')
            cond = self.bexpr()
            right = self.pauli()
            return Unitary(left, cond, right)
        elif self.current_token_type() == 'IF':
            self.eat('IF')
            control = self.bexpr()
            self.eat('THEN')
            prog1 = self.program()
            self.eat('ELSE')
            prog2 = self.program()
            return IF(control, prog1, prog2)
        elif self.current_token_type() == 'WHILE':
            self.eat('WHILE')
            control = self.bexpr()
            self.eat('DO')
            prog = self.program()
            return WHILE(control, prog)
    # variable: NAME
    def var(self) -> ASTNode:
        token = self.current_token()
        self.eat('NAME')
        return Var(token)
    #atom =  PAULI atom | PAULI | bexpr
    def atom(self) -> ASTNode: 
        # if self.current_token_value() == '(':
        #     self.eat('LP')
        #     node = self.assertion()
        #     self.eat('RP')
        #     return node
        node = self.pauli()
        if self.current_token_type() in('PAULI','PHASE'):
            node = self.pauli()
            if self.current_token_type() in ('PAULI','PHASE'):
                node = Pauliproduct(node, self.atom())
                return node
            else:
                node = self.pauli()
                return node
        else: 
            node = self.bexpr()
            return node
    # pauli: p_n | ph b p_n | NAME
    def pauli(self) -> ASTNode:
        if self.current_token_type() == 'PAULI':
            node = Pauli(self.current_token_value())
            self.eat('PAULI')
            return node
        elif self.current_token_type() == 'PHASE':
            self.eat('PHASE')
            node = Pauliexp(self.bexpr(), self.pauli())
            return node
        elif self.current_token_type() == 'NAME':
            node = Name(self.current_token_value())
            self.eat('NAME')
            return node
        else:
            raise RuntimeError(f'Unexpected token {self.current_token_type()}')
    # Below defs are already correct. 
    # bexpr = bterm &/| bterm 
    def bexpr(self) -> ASTNode:
        node = self.bterm()
        while self.current_token_value() in ('&', '|'):
            op = self.current_token_value()
            self.eat('OP')
            node = BinOp(node, op = op, right = self.bterm())
        return node
    # bterm = !bterm | (bexpr) | true | false | aexpr <= aexpr | aexpr >= aexpr | aexpr == aexpr | aexpr != aexpr | aexpr
    def bterm(self) -> ASTNode:
        if self.current_token_value() == '!':
            op = self.current_token_value()
            self.eat('OP')
            node = UnaryOp(op, self.bterm())
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
            if self.current_token_value() in ('<=','>=','==','!='):
                op = self.current_token_value()
                self.eat('OP')
                node = BinOp(node, op, self.aexpr())
            return node
    #aexpr = term +/-/*// aexpr | term
    def aexpr(self) -> ASTNode:
        node = self.term()
        while self.current_token_type() in ('OP') and self.current_token_value() in ('+','-','*','/'):
            self.eat('OP')
            op = self.current_token_value()
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
    def next_token(self) -> Token:
        if self.pos + 1 < len(self.tokens):
            return self.tokens[self.pos + 1]
        else:
            return ('EOF', None)
    def current_token_type(self) -> str:
        return self.current_token()[0]
    def current_token_value(self) -> Union[str,int, float]:
        return self.current_token()[1]
    def next_token_type(self) -> str:
        return self.next_token()[0]
    def next_token_value(self) -> Union[str, int, float]:
        return self.next_token()[1]
    
    #Type check
    def eat(self, token_type: str):
        if(self.current_token_type() == token_type):
            self.pos += 1
        else:
            raise RuntimeError(f'Expected {token_type} but got {self.current_token_type()}')

#Node visitor for program logic

#Test 
if __name__ == '__main__':
    expression = ' g_1 := Z_1Z_2; g_2 := Z_2Z_3; s_1 := meas g_1; s_2 := meas g_2; q_1 *= (s_1 & !s_2) X'
    tokens = lexer(expression)
    print(tokens)

    parser = Program_Parser(tokens)
    AST = parser.parse()
    print(AST)