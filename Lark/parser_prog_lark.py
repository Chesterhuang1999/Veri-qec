# This file is designed for archiving purposes. 

from lark import Lark, Transformer, v_args

from lark import Lark, Transformer, v_args
def get_assertion_parser():
    assertion_grammar = """
    ?assertion: pexp 
        | "!" assertion -> not
        | assertion "&&" assertion -> and
        | assertion "||" assertion -> or
        | assertion "=>" assertion -> implies
    ?pexp: "(" assertion ")"
        | pauli*
        | bexpr
    ?pauli: PAULIOP -> elem
        | "ph" bexpr PAULIOP -> phase
    ?bexpr: bterm 
        | bexpr "&" bterm
        | bexpr "|" bterm -> bit_or
        | bexpr "->" bterm 
    ?bterm: "!" bterm
        | "(" bexpr ")"
        | "true" -> true
        | "false"  -> false
        | aexpr "<=" aexpr
        | aexpr ">=" aexpr
        | aexpr "==" aexpr
        | aexpr "!=" aexpr
        | aexpr "<"  aexpr
        | aexpr ">"  aexpr
        | aexpr
    ?aexpr: aterm
        | aexpr " + " aterm
        | aexpr " - " aterm
        | aexpr " * " aterm
        | aexpr " / " aterm
    ?aterm: NUMBER
        | NAME
        | "-" aterm
        | "(" aexpr ")"
        
    %import common.NUMBER -> NUMBER
    %import common.WS
    %ignore WS

    PAULIOP: /[IXYZ](_)?[0-9]*/
    NAME: /[a-zA-Z](_)?[0-9]*/
    OR: "||"
    BIT_OR: "|"

    """
    return Lark(assertion_grammar, start='assertion', parser='earley')

def get_program_parser(): 
    program_grammar = """
    ?program: (statement ";")* statement ->seq 
       
    ?statement: var ":=" "meas" pauli -> meas
        | var ":=" expr -> assign
        | var "*=" bexpr pauli -> unitary
        | "if" bexpr "then" program "else" program -> if
        | "while" bexpr "do" program -> while
        | "skip" -> skip
    
    ?var: NAME
    ?expr: pauli*
        | bexpr
    
    ?pauli: PAULIOP 
        | "ph" bexpr PAULIOP 
        | NAME

    ?bexpr: bterm 
        | bexpr "&" bterm
        | bexpr "|" bterm -> bit_or
    ?bterm: "!" bterm
        | "(" bexpr ")"
        | "true" -> true
        | "false"  -> false
        | aexpr "<=" aexpr
        | aexpr ">=" aexpr
        | aexpr "==" aexpr
        | aexpr "!=" aexpr
        | aexpr "<"  aexpr
        | aexpr ">"  aexpr
        | aexpr
    ?aexpr: aterm
        | aexpr " + " aterm
        | aexpr " - " aterm
        | aexpr " * " aterm
        | aexpr " / " aterm
    ?aterm: NUMBER
        | NAME
        | "-" aterm
        | "(" aexpr ")"
        
    %import common.NUMBER -> NUMBER
    %import common.WS
    %ignore WS

   
    PAULIOP: /[IXYZ](_)?[0-9]*/
    NAME: /[a-zA-Z]+(_)?[0-9]*/
    OR: "||"
    BIT_OR: "|"   
    IF: "if"
    THEN: "then"
    ELSE: "else"
    WHILE: "while"
    DO: "do"
    SKIP: "skip"
    MEASURE: "meas" 
    """
    return Lark(program_grammar, start='program', parser='earley')


program = '''g_1 := Z_1Z_2; g_2 := Z_2Z_3; q_1 *= e_1 X; q_2 *= e_2 X; q_3 *= e_3 X; s_1 := meas g_1; s_2 := meas g_2; q_1 *= (s_1 & !s_2) X'''
program_parser = get_program_parser()

tree = program_parser.parse(program)


    