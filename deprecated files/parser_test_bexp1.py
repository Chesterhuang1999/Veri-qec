from lark import Lark, Transformer, v_args

##### parser for the program and assertions in the hoare triple #####
def get_parser(): 
    hoare_triple_grammar = """
    ?triple: "{" condition "}" program "{" condition "}" 
    condition: assertion

    ?program: statement ( ";" statement)*  -> seq 
    var: NAME "_" aexpr

    ?statement: var ":=" "meas" pexpr -> meas
        | var ":=" pexpr -> assign
        | var "*=" (bexpr)? pauli -> unitary
        | "if" bexpr "then" program "else" program -> if
        | "while" bexpr "do" program -> while
        | "skip" -> skip
        | "for" NAME "in" NUMBER "to" NUMBER "do" program "end" -> for

    
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
    
    pauli: "(-1)^("bexpr ")" PAULIOP("_" aexpr)?
        | PAULIOP("_"aexpr)? 

    ?bexpr: bterm 
        | bterm ("&" bterm)+ -> bool_and
        | bterm ("|" bterm)+ -> bool_or
    ?bterm:  "!" bterm -> neg
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
    ?aexpr: aterm ("," aterm)* 
        | aterm ("+" aexpr)+  -> add
        | aterm ("-" aexpr)+  -> sub 
        | aterm ("*" aexpr)+  -> mul 
        | aterm ("/" aexpr)+  -> div  
    ?aterm: NUMBER
        | var
        | NAME
        | "-"aterm -> unary_minus
        | "("aexpr ")"
        | var "(" aterm ("," aterm)* ")" -> func
        
    %import common.NUMBER -> NUMBER
    %import common.WS
    %ignore WS

   
    PAULIOP: "I"| "X" |"Y" | "Z" | "H" | "S" | "CNOT"
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
    return Lark(hoare_triple_grammar, start='triple', parser = 'earley')