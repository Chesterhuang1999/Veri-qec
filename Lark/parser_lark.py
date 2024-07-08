#------------
# author: Chester Huang
# date: 2024.7.8
# version: 1.1.0
#------------

from lark import Lark, Transformer, v_args
# def get_assertion_parser():
#     assertion_grammar = """
#     ?assertion: pexp 
#         | "!" assertion -> not
#         | assertion "&&" assertion -> and
#         | assertion "||" assertion -> or
#         | assertion "=>" assertion -> implies
#     ?pexp: "(" assertion ")"
#         | pauli*
#         | bexpr
#     ?pauli: PAULIOP -> elem
#         | "ph" bexpr PAULIOP -> phase
#     ?bexpr: bterm 
#         | bexpr "&" bterm
#         | bexpr "|" bterm -> bit_or
#         | bexpr "->" bterm 
#     ?bterm: "!" bterm
#         | "(" bexpr ")"
#         | "true" -> true
#         | "false"  -> false
#         | aexpr "<=" aexpr
#         | aexpr ">=" aexpr
#         | aexpr "==" aexpr
#         | aexpr "!=" aexpr
#         | aexpr "<"  aexpr
#         | aexpr ">"  aexpr
#         | aexpr
#     ?aexpr: aterm
#         | aexpr " + " aterm
#         | aexpr " - " aterm
#         | aexpr " * " aterm
#         | aexpr " / " aterm
#     ?aterm: NUMBER
#         | NAME
#         | "-" aterm
#         | "(" aexpr ")"
        
#     %import common.NUMBER -> NUMBER
#     %import common.WS
#     %ignore WS

#     PAULIOP: /[IXYZ](_)?[0-9]*/
#     NAME: /[a-zA-Z](_)?[0-9]*/
#     OR: "||"
#     BIT_OR: "|"

#     """
#     return Lark(assertion_grammar, start='assertion', parser='earley')


##### parser for the program and assertions in the hoare triple #####
def get_parser(): 
    hoare_triple_grammar = """
    ?triple: "{" condition "}" program "{" condition "}" 
    condition: assertion

    ?program: statement ( ";" statement)*  -> seq 
    var: NAME("_" (NAME | NUMBER))?  

    ?statement: var ":=" "meas" pexpr -> meas
        | var ":=" pexpr -> assign
        | var "*=" (bexpr)? pauli -> unitary
        | "if" bexpr "then" program "else" program -> if
        | "while" bexpr "do" program -> while
        | "skip" -> skip
        | "for" var "in" NUMBER "to" NUMBER "do" program "end" -> for

    ?assertion: pexpr
        | "!" assertion -> not
        | pexpr "&&" assertion -> and
        | pexpr "||" assertion -> or
        | pexpr "=>" assertion -> implies
        | "Or" var* NUMBER* NUMBER* "(" assertion ")" -> bigor
        | "And" var* NUMBER* NUMBER* "(" assertion ")" -> bigand

        
        
    ?pexpr: "(" assertion ")"
        | pauli*
        | bexpr
    
    pauli: "(-1)^("bexpr ")"PAULIOP("_"NUMBER)?
        | PAULIOP("_"NUMBER)? 

    ?bexpr: bterm 
        | bexpr "&" bterm -> bool_and
        | bexpr "|" bterm -> bool_or
    ?bterm: "!" bterm -> neg
        | "(" bexpr ")"
        | "true" -> true
        | "false"  -> false
        | aexpr "<=" aexpr -> leq
        | aexpr ">=" aexpr -> geq
        | aexpr "==" aexpr -> eq
        | aexpr "!=" aexpr -> neq
        | aexpr "<"  aexpr -> lt
        | aexpr ">"  aexpr -> gt
        | aexpr
    ?aexpr: aterm
        | aterm "+" aexpr  -> add
        | aterm "-" aexpr  -> sub 
        | aterm "*" aexpr  -> mul 
        | aterm "/" aexpr  -> div
    ?aterm: NUMBER
        | var
        | "-"aterm -> unary_minus
        | "("aexpr")"
        
    %import common.NUMBER -> NUMBER
    %import common.WS
    %ignore WS

   
    PAULIOP: /[IXYZHS|CNOT]/
    NAME: /[a-zA-Z]+/
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
    return Lark(hoare_triple_grammar, start='triple', parser='earley')


##### tests ##### 


# text = ''' {Z_1Z_2 && Z_2Z_3} q_1 *= e_1 X; q_2 *= e_2 X; q_3 *= e_3 X {( e_1 + e_2 + e_3 <= 1 ) && !!( (-1)^1 Z_1 Z_2 || ((-1)^0 Z_2Z_3 => Z_1Z_2Z_3))}  '''
# hoare_triple_parser = get_parser()
# tree = hoare_triple_parser.parse(text)
# print(tree.pretty())
# print(tree.data)
# print(tree.children[2])

# program = '''g_1 := Z_1Z_2; g_2 := Z_2Z_3; q_1 *= e_1 X; q_2 *= e_2 X; q_3 *= e_3 X; s_1 := meas g_1; s_2 := meas g_2; q_1 *= (s_1 & !s_2) X'''
# program_parser = get_program_parser()

# tree = program_parser.parse(program)

#q_1 *= e_1 X; q_2 *= e_2 X; q_3 *= e_3 X; s_1 := meas Z_1Z_2; s_2 := meas Z_2Z_3; q_1 *= (s_1 & !s_2) X 
    