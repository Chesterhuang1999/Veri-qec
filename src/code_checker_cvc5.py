import sys
from condition_multiq import *
from encoder import *
from parser_qec import get_parser
from lark.reconstruct import Reconstructor
from z3 import *
import matplotlib.pyplot as plt
from timebudget import timebudget 
from collections import defaultdict
from surface_code_partition import smtencoding, smtchecking
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
def code_checker_logical(matrix, numq, k, N, dx, dz, circuit):
    precond = stab_cond_gen(matrix, numq, k)
    ex_max = (dx - 1) // 2
    ez_max = (dz - 1) // 2
    bit_width = int(math.log2(numq)) + 1
    postcond_x, postcond_z = stab_cond_gen(matrix, numq, k)
    code = 'surface'
    for ind, gateinfo in circuit.items():
        program_log = program_gen_logical(matrix, numq, N, gateinfo, code)
        program_qec_x, program_qec_z = program_gen_qec(matrix, numq, k,  N)
        program_x = ';'.join([program_log, program_qec_x])
        program_z = ';'.join([program_log, program_qec_z])
        decoder_cond_x, decoder_cond_z = decode_cond_gen(matrix, numq, k, N, dx, dz)
        err_cond_z = f"sum i 1 {numq} (ex_(i)) <= {ex_max}"
        err_cond_x = f"sum i 1 {numq} (ez_(i)) <= {ez_max}"
        err_gt_z = f"sum i 1 {numq} (ex_(i)) <= {dx - 1}"
        err_gt_x = f"sum i 1 {numq} (ez_(i)) <= {dz - 1}"
        _, _, precond_x_tree = precond_generator(program_log, postcond_x, postcond_x)
        _, _, precond_z_tree = precond_generator(program_log, postcond_z, postcond_z)
        precond_x = Reconstructor(parser = get_parser()).reconstruct(precond_x_tree)
    # program = program_gen_logical(matrix, numq, N)
    # program_gen()

### Scenario III: Errors during decoding

@timebudget
def code_checker_error(matrix, numq, k, dx, dz):
    pass


### Scenario IV: Errors during both

if __name__ == "__main__" : 
    matrix = surface_matrix_gen(3)
    DJ = defaultdict(list)
    DJ[1] = [['H', [1]], ['H',[2]], ['H', [3]]]
    DJ[2] = [['CNOT', [1,2]], ['CNOT', [1,3]]]
    DJ[3] = [['H', [1]], ['H',[2]]]

    code_checker_logical(matrix, 9, 1, 3, 3, 3, DJ)