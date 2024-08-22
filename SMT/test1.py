
from lark import Tree, Token
from z3 import *

def tree_to_z3(tree, variables, constraints, bit_width):
    if isinstance(tree, Token) and tree.type == 'NUMBER':
        return BitVecVal(tree.value, bit_width)
    elif tree.data == 'and':
        return And(*[tree_to_z3(child, variables, constraints,bit_width) for child in tree.children])
    elif tree.data == 'or':
        return Or(*[tree_to_z3(child, variables, constraints, bit_width) for child in tree.children])
    elif tree.data == 'eq':
        return tree_to_z3(tree.children[0], variables, constraints, bit_width) == tree_to_z3(tree.children[1], variables, constraints, bit_width)
    elif tree.data == 'add':
        return sum((tree_to_z3(child, variables, constraints, bit_width) for child in tree.children), BitVecVal(0, bit_width))
    elif tree.data == 'var':
        name = tree.children[0].value
        index = int(tree.children[1].value)
        var_name = f"{name}_{index}"
        if var_name not in variables:
            variables[var_name] = BitVec(var_name, bit_width)
            constraints.append(Or(variables[var_name] == 0, variables[var_name] == 1))  # Add domain constraint for this variable
        return variables[var_name]
    elif tree.data == 'func':
        func_name = tree.children[0].children[0].value
        args = [tree_to_z3(child, variables, constraints,bit_width) for child in tree.children[1:]]
        # Assuming the function is defined separately; replace this with actual function definition
        return Function(func_name, *args)
    else:
        raise ValueError(f"Unknown tree node: {tree}")


# Example tree
# tree = Tree('and', [
#     Tree('eq', [
#         Tree('var', [Token('NAME', 'b'), Token('NUMBER', '1')]),
#         Tree('add', [
#             Tree('var', [Token('NAME', 'e'), Token('NUMBER', '3')]),
#             Tree('var', [Token('NAME', 'c'), Token('NUMBER', '3')]),
#             Tree('var', [Token('NAME', 'b'), Token('NUMBER', '1')])
#         ])
#     ]),
#     Tree('and', [
#         Tree('eq', [
#             Token('NUMBER', '0'),
#             Tree('add', [
#                 Tree('var', [Token('NAME', 'e'), Token('NUMBER', '2')]),
#                 Tree('var', [Token('NAME', 'e'), Token('NUMBER', '1')]),
#                 Tree('var', [Token('NAME', 's'), Token('NUMBER', '1')])
#             ])
#         ]),
#         Tree('eq', [
#             Token('NUMBER', '0'),
#             Tree('add', [
#                 Tree('var', [Token('NAME', 'e'), Token('NUMBER', '3')]),
#                 Tree('var', [Token('NAME', 'e'), Token('NUMBER', '2')]),
#                 Tree('var', [Token('NAME', 's'), Token('NUMBER', '2')])
#             ])
#         ])
#     ])
# ])

tree = Tree('eq', [Token('NUMBER', '0'), Tree('add', [Tree('var', [Token('NAME', 'e'), Token('NUMBER', 3)]), 
                                                                   Tree('var',[Token('NAME','c'),Token('NUMBER','3')])])])
variables = {}
constraints = []
z3_expr = tree_to_z3(tree, variables, constraints, bit_width = 1)

existential_formula = Exists(list(variables.values()), And(*constraints, z3_expr))
print(simplify(existential_formula))

# Create a solver and add the existential formula
solver = Solver()
solver.add(existential_formula)

# Check satisfiability
if solver.check() == sat:
    print("Satisfiable")
    print(solver.model())
else:
    print("Unsatisfiable")

variables = {}
variables[f"e_3"] = BitVec(f"e_3", 1)
variables[f"e_2"] = BitVec(f"e_2", 1)  

z3_expr = variables[f"e_3"] + variables [f"e_2"] == BitVecVal(2, 2)
solver = Solver()
solver.add(z3_expr) 
if solver.check() == sat:
    print("Satisfiable")
    print(solver.model())
else:
    print("Unsatisfiable") 