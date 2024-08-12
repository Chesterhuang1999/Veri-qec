import ply 
import ply.lex as lex
from ply.lex import TOKEN
    
reserved = { 
    'if':'IF',
    'else': 'ELSE',
    'while':'WHILE',
    'for':'FOR',
    'true': 'TRUE',
    'false': 'FALSE',
    '(-1)^': 'PHASE',
}
print(reserved.values())
tokens = list(reserved.values()) +[
    'NAME', 'NUM', 'OP','LP','RP','PAULI','CLIFF']
t_ignore = r'[ \t\n]|\#.*'
def t_NAME(t):
    r'[a-z](_[0-9]+)*'
    if t.value in reserved: 
        t.type = t.value 
        return t
    
def t_NUM(t):
    r'\d+(\.\d*)?'
    t.value = float(t.value) if '.' in t.value else int(t.value)
    return t

def t_OP(t):
    r'<=|>=|==|!=|\&\&|\|\||[-|+|*|/|^|<|>|=]'
    return t

def t_LP(t):
    r'\('
    return t
def t_RP(t):
    r'\)'
    return t

def t_PAULI(t):
    r'[I|X|Y|Z]_[0-9]+'
    return t
def t_CLIFF(t):
    r'[H|S|CNOT]_[0-9]+'
    return t


lexer = lex.lex(debug = 0)

data = '''true && (-1)^b Z_1Z_2Z_3 || (2.2 * e_1) < e_2'''

lexer.input(data)
for token in lexer:
    print(token)