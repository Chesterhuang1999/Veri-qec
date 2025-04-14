from lark import Lark

##### parser for the program and assertions in the hoare triple #####

### The text should start with a Hoare triple consists of two assertions and a program ###
### The assertion is constructed following AExp ###
### The AST of program is constructed following the program syntax ###
### Lalr1 is used to avoid ambiguity ### 
def get_parser(): 
    hoare_triple_grammar = """
    ?triple: ("{" condition "}" program "{")? condition ("}")? 
    condition: assertion

    ?program: statement ( ";" statement)*  -> seq 

    ?statement: var ":=" "meas" pexpr -> meas
        | var ":=" assatom -> assign
        | var ("," var)* "*=" (bexpr)? UNIT -> unitary
        | "if" bexpr "then" program "else" program "end" -> if
        | "while" bexpr "do" program "end" -> while
        | "skip" -> skip
        | "for" NAME "in" NUMBER "to" NUMBER "do" program "end" -> for


    ?assertion: "Neg" assertion -> neg
        | assatom
        | assatom "&&" assertion -> cap
        | assatom "||" assertion -> or
        | assatom "=>" assertion -> implies
        | "Or" (var (NUMBER"," NUMBER)?)+ "(" assertion ")" -> bigor
        | "And" (var (NUMBER "," NUMBER)?)+ "(" assertion ")" -> bigand

        
    ?assatom: pterm | bexpr
    
    ?sexpr: "QR2" "[" aexpr "," aexpr "," aexpr "]"
    
    ?pterm: pexpr | sexpr pexpr ("+" sexpr pexpr)*

    pexpr: pauli+ | 

    pauli: ("(-1)^(" bexpr ")" )? "(" bexpr "," bexpr "," aexpr ")"

    var: NAME "_"  "(" aexpr ")"    

    ?bexpr: bterm
        | bterm "&" bexpr -> bool_and
        | bterm "|" bexpr -> bool_or

    
    ?bterm:  "!" bexpr -> not
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
        | aterm "@^" aexpr -> xor
        | "Max(" aexpr "," aexpr ")" -> max
        | "Min(" aexpr "," aexpr ")" -> min
        

    ?aterm: afactor
        | afactor ("*" afactor)+ -> mul
        | afactor ("/" afactor)+ -> div

    ?afactor: NUMBER
        | NAME
        | var
        | "-" aterm -> unary_minus
        | "(" aexpr ")"
        | "sum" NAME NUMBER NUMBER "(" aexpr ")" -> sum 
        | var "(" aterm ("," aterm)* ")" -> func
        
   
    %import common.NUMBER -> NUMBER
    %import common.WS
    %ignore WS

   
    UNIT:  "I" | "X" | "Y" | "Z" | "H" | "S" | "T" | "CNOT" | "T+"  
    NAME: /[a-z]+/
    OR: "||"
    BIT_OR: "|"   
    IF: "if"
    THEN: "then"
    ELSE: "else"
    WHILE: "while"
    QR2: "QR2"
    DO: "do"
    SKIP: "skip"
    MEASURE: "meas" 
  
    """
    return Lark(hoare_triple_grammar, start='triple', parser = 'lalr', maybe_placeholders = False)



