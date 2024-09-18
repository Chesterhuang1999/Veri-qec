import cvc5
from cvc5 import Kind
from verifier import * 
from data import *

    
def auto_complement_cvc5(a, b, solver):
    a_size = a.getSort().getBitVectorSize()
    b_size = b.getSort().getBitVectorSize()

    if a_size > b_size:
        zero_ext = solver.mkTerm(solver.mkOp(Kind.BITVECTOR_ZERO_EXTEND, a_size - b_size), b)
        return a, zero_ext
    elif a_size < b_size:
        zero_ext = solver.mkTerm(solver.mkOp(Kind.BITVECTOR_ZERO_EXTEND, b_size - a_size), a)
        return zero_ext, b
    else:
        return a, b

def tree_to_cvc5(tree, variables, solver, bit_width):
    if isinstance(tree,Token) and tree.type == 'NUMBER':
        bit_width = 1 if tree.value == '0' else int(math.log2(int(tree.value))) + 1
        return solver.mkBitVector(bit_width, int(tree.value))
    elif tree.data == 'and':
        return solver.mkTerm(Kind.AND, *[tree_to_cvc5(child, variables, solver, bit_width) for child in tree.children])
    elif tree.data == 'or':
        return solver.mkTerm(Kind.OR, *[tree_to_cvc5(child, variables, solver, bit_width) for child in tree.children])
    elif tree.data == 'eq':
        child0, child1 = auto_complement_cvc5(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                         tree_to_cvc5(tree.children[1], variables, solver, bit_width), solver)
        return solver.mkTerm(Kind.EQUAL, child0, child1)
    elif tree.data == 'leq':
        child0, child1 = auto_complement_cvc5(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                         tree_to_cvc5(tree.children[1], variables, solver, bit_width), solver)
        return solver.mkTerm(Kind.BITVECTOR_ULE, child0, child1)
    elif tree.data == 'geq':
        cvc5_child0, cvc5_child1 = auto_complement_cvc5(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                                   tree_to_cvc5(tree.children[1], variables, solver, bit_width), solver)
        return solver.mkTerm(Kind.BITVECTOR_UGE, cvc5_child0, cvc5_child1)
    elif tree.data == 'xor':
        return solver.mkTerm(Kind.BITVECTOR_XOR, tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                             tree_to_cvc5(tree.children[1], variables, solver, bit_width))
    elif tree.data == 'add':
        ssum = solver.mkBitVector(bit_width, 0)
        for child in tree.children:
            cvc5_child = tree_to_cvc5(child, variables, solver, bit_width)
            ext_width = bit_width - cvc5_child.getBitVectorSize()
            ssum = solver.mkTerm(Kind.BITVECTOR_ADD, ssum, solver.mkTerm(Kind.BITVECTOR_ZERO_EXTEND, ext_width, cvc5_child))
        return ssum
    elif tree.data == 'sum':
        name = tree.children[0].value
        start = int(tree.children[1].value)
        end = int(tree.children[2].value)
        body = tree.children[3]
        ssum = solver.mkBitVector(bit_width, 0)
        for j in range(start, end + 1):
            loops_transformer = Loops(name, j)
            body_trans = loops_transformer.transform(body)
            cvc5_body_trans = tree_to_cvc5(body_trans, variables, solver, bit_width)
            ext_width = bit_width - cvc5_body_trans.getSort().getBitVectorSize()
            ssum = solver.mkTerm(Kind.BITVECTOR_ADD, ssum,
                                 solver.mkTerm(solver.mkOp(Kind.BITVECTOR_ZERO_EXTEND, ext_width), cvc5_body_trans))
        return ssum
    elif tree.data == 'bool_and':
        return solver.mkTerm(Kind.AND, tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                             tree_to_cvc5(tree.children[1], variables, solver, bit_width))
    elif tree.data == 'bool_or':
        return solver.mkTerm(Kind.OR, tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                             tree_to_cvc5(tree.children[1], variables, solver, bit_width))
    elif tree.data == 'neg':
        return solver.mkTerm(Kind.NOT, tree_to_cvc5(tree.children[0], variables, solver, bit_width))
    elif tree.data == 'min':
        res1, res2 = auto_complement_cvc5(tree_to_cvc5(tree.children[0], variables, solver, bit_width),
                                     tree_to_cvc5(tree.children[1], variables, solver, bit_width), solver)
        return solver.mkTerm(Kind.ITE, solver.mkTerm(Kind.BITVECTOR_ULE, res1, res2), res1, res2)
    elif tree.data == 'var':
        name = tree.children[0].value
        index = int(tree.children[1].value)
        var_name = f"{name}_{index}"
        if var_name not in variables:
            variables[var_name] = solver.mkConst(solver.mkBitVectorSort(1), var_name)
        return variables[var_name]
    else:
        raise ValueError(f"Unknown tree node: {tree}")
            

def VCgeneration(precond, program, postcond, solver):
    pre_tree, prog_tree, post_tree = precond_generator(program, precond, postcond)
    #stab_dict, stab_list = stab_set_gen(pre_tree.children[0])
    cass_transformer = qassertion2c(pre_tree)
    cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
    cass_tree = simplifyeq().transform(cass_tree)
    cass_expr = solver.simplify(tree_to_cvc5(cass_tree, {}, solver, 1))

    return cass_expr

### Test: surface code 
### Precondition generation
start = time.time()
precond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
&&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

program = """ for i in 1 to 7 do q_(i) *= ex_(i) X end; for i in 1 to 7 do q_(i) *= ez_(i) Z end; sz_(1) := meas (1,0,1)(1,0,3)(1,0,5)(1,0,7); sz_(2) := meas (1,0,2)(1,0,3)(1,0,6)(1,0,7); 
sz_(3) := meas (1,0,4)(1,0,5)(1,0,6)(1,0,7); sx_(1) := meas (0,1,1)(0,1,3)(0,1,5)(0,1,7); 
sx_(2) := meas (0,1,2)(0,1,3)(0,1,6)(0,1,7); sx_(3) := meas (0,1,4)(0,1,5)(0,1,6)(0,1,7); for i in 1 to 7 do q_(i) *= cx_(i) X end; for i in 1 to 7 do q_(i) *= cz_(i) Z end"""

postcond = """(-1)^(b_(1))(1,0,1)(1,0,2)(1,0,3) && (1,0,1)(1,0,3)(1,0,5)(1,0,7) && (1,0,2)(1,0,3)(1,0,6)(1,0,7) && (1,0,4)(1,0,5)(1,0,6)(1,0,7) 
&&(0,1,1)(0,1,3)(0,1,5)(0,1,7) && (0,1,2)(0,1,3)(0,1,6)(0,1,7) && (0,1,4)(0,1,5)(0,1,6)(0,1,7) """

tm = cvc5.TermManager()
solver = cvc5.Solver(tm)
solver.setLogic("BV")
solver.setOption("produce-models", "true")


cass_expr = VCgeneration(precond, program, postcond, solver)

err_cond = """ sum i 1 7 (ex_(i)) <= 1  """
# # ## Decoding condition of a minimum-weight perfect matching (should be read from file)
decoder_cond_bool = """ sz_(1) == cx_(1) @^ cx_(3) @^ cx_(5)@^ cx_(7) && sz_(2) == cx_(2) @^ cx_(3) @^ cx_(6) @^ cx_(7) && sz_(3) == cx_(4) @^ cx_(5) @^ cx_(6) @^ cx_(7) 
&&sx_(1) == cz_(1) @^cz_(3) @^ cz_(5) @^ cz_(7)  && sx_(2) == cz_(2) @^ cz_(3) @^ cz_(6) @^ cz_(7) && sx_(3) == cz_(4) @^ cz_(5) @^ cz_(6) @^ cz_(7)"""

decoder_cond_int = """ sum i 1 7 (cx_(i)) <= Min( sum i 1 7 (ex_(i)), 1) && sum i 1 7 (cz_(i)) <= Min( sum i 1 7 (ez_(i)), 1) """

err_tree, _, decoder_tree_int = precond_generator('skip', err_cond, decoder_cond_int)
_, _, decoder_tree_bool = precond_generator('skip', err_cond, decoder_cond_bool)

err_expr = solver.simplify(tree_to_cvc5(err_tree.children[0], {}, solver, 3))

decoder_expr_int = solver.simplify(tree_to_cvc5(decoder_tree_int.children[0],{}, solver, 3))

variables = {}

decoder_expr_bool = solver.simplify(tree_to_cvc5(decoder_tree_bool.children[0], variables, solver, 3))

decoding_formula = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.AND, cass_expr, decoder_expr_int, decoder_expr_bool))
print(decoding_formula)
#var_list = list(variables.values())
name_list = list(variables.keys())
var_list = [solver.mkVar(solver.mkBitVectorSort(1), name) for name in name_list]
var_list = solver.mkTerm(Kind.VARIABLE_LIST,*[var for var in var_list])
correctness_assertion = solver.mkTerm(Kind.FORALL, var_list, 
                                      solver.mkTerm(Kind.AND, err_expr, decoding_formula))
solver.assertFormula(correctness_assertion)
with open("cvc5_assertion.smt2", "w") as f:
    f.write(correctness_assertion)

# if solver.checkSat() == 'sat':
#     print("Counterexample:")
#     print(solver.getModel())
# else: 
#     print("The assertion is correct!")



# F = err_expr