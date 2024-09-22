import sys
from condition_gen import *
from encoder import *
from z3 import *
import matplotlib.pyplot as plt
from timebudget import timebudget 
from scipy.sparse import csc_matrix, block_diag, kron, eye
import cvc5

sys.setrecursionlimit(10**6)
### Verification steps: I. Generate the program and assertion from the check matrix and the required logical operations
###                     II. Generate the decoding conditions and error conditions
###                    III. Transform those conditions into a z3 SMT expression
###                    IV. Check the satisfiability of the SMT expression


### Scenario I: 
@timebudget
def code_checker_basic(matrix, numq, k, dx, dz):
    t1 = time.time()
    ex_max = (dx - 1) // 2
    ez_max = (dz - 1) // 2
    bit_width = int(math.log2(numq)) + 1
    precond = stab_cond_gen(matrix, numq, k)
    postcond = precond 
    program = program_gen(matrix, numq, k)
    decoder_cond = decode_cond_gen(matrix, numq, k)
    
    
### Scenario II: Logical operations on encoded qubits
@timebudget
def code_checker_logical(matrix, numq, k, dx, dz):
    precond = stab_cond_gen(matrix, numq, k)


### Scenario III: Errors during decoding

@timebudget
def code_checker_error(matrix, numq, k, dx, dz):
    pass