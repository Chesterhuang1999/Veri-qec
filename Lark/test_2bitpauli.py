from lark import Lark, Transformer, v_args

grammar = """

    ?start: assertion
    ?assertion: pexpr
    | "!" assertion
    | assertion "&&" assertion
    | assertion "||" assertion

    ?pexpr: "("assertion")"
    | pauli*
    | bexpr
    
    ?pauli: "(-1)^(" bexpr ")" PE "_" NUMBER
    | PE "_" NUMBER 
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
        | aexpr"+"aterm  -> add
        | aexpr"-"aterm  -> sub 
        | aexpr"*"aterm  -> mul 
        | aexpr"/"aterm  -> div
    ?aterm: NUMBER
        | NAME("_" NUMBER)? -> var
        | "-"aterm -> unary_minus
        | "("aexpr")"


    PE: "01" | "10" | "11" | "00"
    %import common.NUMBER -> NUMBER 
    %import common.WS 
    %ignore WS

    NAME: /[a-zA-Z]+/
    
"""

parser = Lark(grammar, parser = 'earley',start = 'start')

text = """(-1)^(b_1)01_1 11_2 """
print(parser.parse(text).pretty())

# # Define the grammar for the calculator
# grammar = """
#     ?start: expr

#     ?expr: expr "+" term  -> add
#          | expr "-" term  -> sub
#          | term

#     ?term: term "*" factor  -> mul
#          | term "/" factor  -> div
#          | factor

#     ?factor: NUMBER        -> number
#            | SYMBOL        -> variable
#            | "(" expr ")"

#     %import common.CNAME -> SYMBOL
#     %import common.NUMBER
#     %import common.WS_INLINE

#     %ignore WS_INLINE
# """

# class SimplifyTransformer(Transformer):
#     def __init__(self):
#         pass

#     def add(self, args):
#         return self.combine(args[0], args[1], '+')

#     def sub(self, args):
#         return self.combine(args[0], args[1], '-')

#     def mul(self, args):
#         left, right = args
#         if isinstance(left, dict):
#             return {k: v * right for k, v in left.items()}
#         if isinstance(right, dict):
#             return {k: v * left for k, v in right.items()}
#         return left * right

#     def div(self, args):
#         left, right = args
#         if isinstance(left, (int, float)) and isinstance(right, (int, float)):
#             return left / right
#         else:
#             raise ValueError("Division involving variables is not supported in this simple form")

#     def number(self, n):
#         return int(n[0])

#     def variable(self, name):
#         return {str(name[0]): 1}

#     def combine(self, left, right, operator):
#         result = {}
#         all_keys = set(left.keys()).union(right.keys())
#         for k in all_keys:
#             left_value = left.get(k, 0)
#             right_value = right.get(k, 0)
#             if operator == '+':
#                 result[k] = left_value + right_value
#             elif operator == '-':
#                 result[k] = left_value - right_value
#         return result

# # Function to evaluate expressions
# def evaluate_expression(expression):
#     parser = Lark(grammar, parser='lalr', transformer=SimplifyTransformer())
#     return parser.parse(expression)

# # Function to format the result
# def format_result(result):
#     terms = []
#     for var, coef in sorted(result.items()):
#         if coef == 0:
#             continue
#         if var == '':
#             terms.append(str(coef))
#         else:
#             if coef == 1:
#                 terms.append(var)
#             elif coef == -1:
#                 terms.append(f"-{var}")
#             else:
#                 terms.append(f"{coef}*{var}")
#     if not terms:
#         return "0"
#     return " + ".join(terms).replace('+ -', '- ')

# # Example usage
# if __name__ == '__main__':
#     expressions = [
#         "y + 3 + y + 3 + 1",
#         "2*x + 3*x + 4",
#         "a - 2*a + 3",
#         "5 + b - b + 2",
#         "c * 3 + 4 * c - 5"
#     ]

#     for expr in expressions:
#         result = evaluate_expression(expr)
#         formatted_result = format_result(result)
#         print(f"{expr} = {formatted_result}")
