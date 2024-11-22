from lark import Lark


##### parser for the program and assertions in the hoare triple #####
def get_parser(): 
    hoare_triple_grammar = """
    ?triple: "{" condition "}" program "{" condition "}" 
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
        | assatom "&&" assertion -> and
        | assatom "||" assertion -> or
        | assatom "=>" assertion -> implies
        | "Or" (var (NUMBER"," NUMBER)?)+ "(" assertion ")" -> bigor
        | "And" (var (NUMBER "," NUMBER)?)+ "(" assertion ")" -> bigand

    ?assatom: pexpr | bexpr
    
    pexpr:  pauli+ 
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

   
    UNIT:  "I" | "X" | "Y" | "Z" | "H" | "S"  | "CNOT" 
    NAME: /[a-z]+/
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
    return Lark(hoare_triple_grammar, start='triple', parser = 'lalr', maybe_placeholders = False)


# def test_parser(cond):
#     tree = parser.parse(cond)

#     return tree.pretty()

# start = time.time()
# precond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

# program = """for i in 1 to 7 do q_(i) *= ex_(i) X end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
# sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
# sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end"""

# postcond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

# parser = get_parser()
# triple = "{" + precond + "}" + program + "{" + postcond + "}"
# tree = parser.parse(triple)
# pre_tree, program_tree, post_tree = tree.children

# end = time.time()
# print(end - start)

### archive 

# && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# for i in 1 to 7 do q_(i) *= ex_(i) X end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
# sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
# sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end

# (-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
# &&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7)
# for i in 1 to 7 do q_(i) *= ex_(i) X end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
# sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
# sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end