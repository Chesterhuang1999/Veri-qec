import sys
from condition_multiq import *
from encoder import *
from parser_qec import get_parser
from lark.reconstruct import Reconstructor
from z3 import *
import matplotlib.pyplot as plt
from timebudget import timebudget 
from collections import defaultdict
from smt_partition_merge import *
from smt_testing_meas_err import *
import re
import cvc5
from execute_verify import *

sys.setrecursionlimit(10**6)

### Verification steps: I. Generate the program and assertion from the check matrix and the required logical operations
###                     II. Generate the decoding conditions and error conditions
###                    III. Transform those conditions into a z3 SMT expression
###                    IV. Check the satisfiability of the SMT expression

    
### Scenario II: Logical operations on encoded qubits, with error correction. 


def formula_gen_combine(mat, dx, dz, rnds, N, prog_log):
    ## mat: check matrix, dx, dz: distance, rnd: measurement rounds per layer; N; number of logical qubits;
    numq = mat.shape[1] // 2
    # k = mat.shape[0] - numq
    
    program_qec_x, program_qec_z = program_gen_qec_mul(mat, numq, N, rnds)
    
    postcond_x, postcond_z  = stab_cond_gen_multiq(mat, numq, N)
    # print(postcond_z)
    decoder_cond_x, decoder_cond_z, meas_corr_x, meas_corr_z = decode_cond_gen_mul(mat, numq, N, rnds, dx, dz) 
    precond_x = recon_string(precond_generator(prog_log, postcond_x, postcond_x)[-1])
    precond_z = recon_string(precond_generator(prog_log, postcond_z, postcond_z)[-1])
    meas_cnt_max = max(len(meas_corr_x), len(meas_corr_z))
    bit_width = int(math.log2(numq * N * rnds + meas_cnt_max)) + 1
    print(bit_width)
    # print(precond_x)
    # print(precond_z)
    sum_x = ""
    sum_z = ""
    for ci in meas_corr_x:
        sum_x = sum_x + f"c_({ci}) +"
    for ci in meas_corr_z:
        sum_z = sum_z + f"c_({ci}) +"
    
    sum_x += f"sum i 1 {numq * N * rnds} (cz_(i))"
    sum_z += f"sum i 1 {numq * N * rnds} (cx_(i))" 
    
    # print(precond_x, program_x, postcond_x)
    ## For only logical operation, is verification
    ## For logical op with measurement error, is test
    if rnds > 1:

        packed_x = smtencoding_meas_err(precond_x, program_qec_x, postcond_x, 
                                        decoder_cond_x, sum_x, bit_width, prog_log)
        packed_z = smtencoding_meas_err(precond_z, program_qec_z, postcond_z, 
                                        decoder_cond_z, sum_z, bit_width, prog_log)
        return packed_x, packed_z, meas_corr_x, meas_corr_z 
    elif rnds == 1:

        err_cond_x = f"sum i 1 {numq} (ez_(i)) <= {(dz - 1) // 2}" 
        err_gt_x = f"sum i 1 {numq} (ez_(i)) <= {dz - 1}"
        err_cond_z = f"sum i 1 {numq} (ex_(i)) <= {(dx - 1) // 2}"
        err_gt_z = f"sum i 1 {numq} (ex_(i)) <= {dx - 1}"
        program_x = f"{prog_log};{program_qec_x}"
        program_z = f"{prog_log};{program_qec_z}"
        packed_x = smtencoding(bit_width, precond_x, program_x, postcond_x, 
                            err_cond_x, err_gt_x, 
                            decoder_cond_x)
        packed_z = smtencoding(bit_width, precond_z, program_z, postcond_z, 
                            err_cond_z, err_gt_z, 
                            decoder_cond_z)
        return packed_x, packed_z
    # return packed_x, packed_z, meas_corr_x, meas_corr_z
def random_sample_test(numq, N, meas_cnt, rnds, D):
    max_ham_weight = (D - 1) // 2
    indices = []
    meas_cnt_single = meas_cnt // ((rnds - 1) * N)
    for i in range(rnds):
        num_ones = np.random.randint(1, max_ham_weight + 1)
        qbase = i * N * numq
        mbase = 0
        if i == 0:
            for cnt in range(N):
                
                place_indice = np.arange(qbase, qbase + numq)
                
                if len(indices) == 0:
                    indices = np.random.choice(place_indice, num_ones, replace = False)
                else:
                    indices_i = np.random.choice(place_indice, num_ones, replace = False)
                    
                    indices = np.concatenate((indices, indices_i))
                qbase = qbase + numq 

        else:
            for cnt in range(N):
                mbase = (N * (i - 1) + cnt) * meas_cnt_single
                
                
                place_indice = np.arange(qbase + mbase, qbase + mbase + numq + meas_cnt_single)
                
                indices_i = np.random.choice(place_indice, num_ones, replace = False)
                
                indices = np.concatenate((indices, indices_i))
                qbase = qbase + numq
    bin_arr = np.zeros(numq * N * rnds + meas_cnt, dtype = int)
    bin_arr[indices] = 1
    return bin_arr

@timebudget
def sur_seq_checker_combine(matrix, dx, dz, program, N, rnds):
    numq = matrix.shape[1] // 2
    for inds, gateinfo in program.items():
        prog_log = program_gen_logic(matrix, numq, N, gateinfo, 'steane')
        # print(prog_log)
        if rnds == 1:
            packed_x, packed_z = formula_gen_combine(matrix, dx, dz, 1, N, prog_log)
            t1x, res1_x = seq_cond_checker(packed_x, [0], 'x')
            t1z, res1_z = seq_cond_checker(packed_z, [0], 'z')
            t2x, res2_x = seq_cond_checker(packed_x, [1], 'x')
            t2z, res2_z = seq_cond_checker(packed_z, [1], 'z')
            print(res1_x, res2_x, res1_z, res2_z)
        else:
            packed_x, packed_z, meas_corr_x, meas_corr_z = formula_gen_combine(matrix, dx, dz, rnds, N, prog_log)
            ## Randomly generate 10 test cases
            for i in range(1):
                print(numq * N * rnds + len(meas_corr_x))
                err_vals_x = random_sample_test(numq, N, len(meas_corr_x), rnds, dz)
                err_vals_z = random_sample_test(numq, N, len(meas_corr_z), rnds, dx)
                posx = np.nonzero(err_vals_x)[0]
                posz = np.nonzero(err_vals_z)[0]
                print(posx)

                result_x = seq_checker_meas_err(packed_x, meas_corr_x, rnds, err_vals_x, 'x')
                # result_z = seq_checker_meas_err(packed_z, meas_corr_z, rnds, err_vals_z, 'z')
                
                # with open("Details/sur_meas_err_test.txt", "a") as f:
                #     f.write(f"case id: {i} | type: x_stabs | err counts: {len(posx)}\n")
                #     f.write(f"err pos: {posx} | result: {result_x}\n")
                #     f.write(f"case id: {i} | type: z_stabs | err counts: {len(posz)}\n")
                #     f.write(f"err pos: {posz} | result: {result_z}\n")

## Towards the fault-tolerant quantum computing, first thing is to                 
def formula_gen_logical(matrix, dx, dz, gates, N):
    numq = matrix.shape[1] // 2
    prog_x, prog_z, err_gt_x, err_gt_z = program_gen_log_err(matrix, numq, N, gates, code = 'steane')
    print(prog_x)
    postcond_x, postcond_z = stab_cond_gen_log(matrix, N)
    bit_width = int(math.log2(numq * N)) + 1
    for ind, gateinfo in gates.items():
        prog_log = program_gen_logic(matrix, numq, N, gateinfo, 'steane')
        pre_tree_x = precond_generator(prog_log, postcond_x, postcond_x)[-1]
        pre_tree_z = precond_generator(prog_log, postcond_x, postcond_z)[-1]
        precond_x = recon_string(pre_tree_x)
        precond_z = recon_string(pre_tree_z)
        # totq = numq * N
        err_cond_x = f"sum i 1 {numq} (ez_(i)) + sum i 1 {numq} (pz_(i)) <= {(dz - 1) // 2}"
        err_cond_z = f"sum i 1 {numq} (ex_(i)) + sum i 1 {numq} (px_(i)) <= {(dx - 1) // 2}"
        for i in range(N):
            start = i * numq 
            err_gt_x = err_gt_x + f"&&sum i {start + 1} {start + numq} (ez_(i)) <= {(dz -1)}"
            err_gt_z = err_gt_z + f"&&sum i {start + 1} {start + numq} (ex_(i)) <= {(dx -1)}"
            if i >= 1:
                err_cond_x = err_cond_x + f"&&sum i {start + 1} {start + numq} (ez_(i)) <= {(dz -1) //2 }"
                err_cond_z = err_cond_z + f"&&sum i {start + 1} {start + numq} (ex_(i)) <= {(dx -1) //2 }"
        print(err_cond_x)
        decoder_cond_x, decoder_cond_z, _, _ = decode_cond_gen_mul(matrix, numq, N, 1, dx, dz)
        
        packed_x = smtencoding(bit_width, precond_x, prog_x, postcond_x, 
                            err_cond_x, err_gt_x, 
                           decoder_cond_x)
      
        packed_z = smtencoding(bit_width, precond_z, prog_z, postcond_z,
                            err_cond_z, err_gt_z, 
                            decoder_cond_z)
        
        return packed_x, packed_z
        # print(simplify(tree_to_z3(VCgeneration(precond_x, prog_x, postcond_x))))

if __name__ == "__main__" : 
    D = 3
    N = 2
    rnds = 2
    # matrix = surface_matrix_gen(D)
    matrix = special_codes.stabs_steane()
    # print(matrix)
    # DJ = defaultdict(list)
    # DJ[1] = [['H', [1]], ['H',[2]], ['H', [3]]]
    # DJ[2] = [['CNOT', [1,2]], ['CNOT', [1,3]]]
    # DJ[3] = [['H', [1]], ['H',[2]]]
    H = defaultdict(list)
    H[1] = [['H', [1]], ['H', [2]]]
    # prog_log = program_gen_logic(matrix, 7, 3, H[1], 'surface')
    GHZ = defaultdict(list)
    GHZ[0] = [['H', [2]]]
    GHZ[1] = [['CNOT', [2,1]], ['CNOT', [2, 3]]]
    print(program_gen_logic(matrix, 7, 3, GHZ[0], 'steane'))
    print(program_gen_logic(matrix, 7, 3, GHZ[1], 'steane'))    
    # exit(0)
    packed_x, packed_z = formula_gen_logical(matrix, D, D, GHZ, 3)
    exit(0)
    err_val_x = np.zeros(11, dtype = int)
    err_val_x[9] = 1 
    err_val_z = np.zeros(17, dtype = int)
    err_val_z[9] = 1
    err_val_z[16] = 1

    tx, res_x = seq_cond_checker(packed_x, err_val_x,'x')    
    tz, res_z = seq_cond_checker(packed_z, err_val_z,'z')

    print(tx, res_x)
    print(tz, res_z)
    # print(prog_qec_z)
    DJ = defaultdict(list)
    DJ[1] = [['H', [1]], ['H', [2]], ['H', [3]]]

    # DJ[2] = [['CNOT', [1,2]], ['CNOT', [1,3]]]
    # DJ[3] = [['H', [1]], ['H', [2]]]
    # print(prog_log)
    # packed_x, packed_z = formula_gen_combine(matrix, 3, 3, 1, 3, prog_log)
    # print(packed_x[0])
    # sur_seq_checker_combine(matrix, D, D, H, N, rnds)
    # packed_x, packed_z = formula_gen_combine(matrix, D, D, rnds, N, prog_log)
    # print(packed_x[0])
