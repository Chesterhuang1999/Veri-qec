import sys
from condition_multiq import *
from encoder import *

from z3 import *

from timebudget import timebudget 
from collections import defaultdict
from smt_partition_merge import *
from smt_testing_meas_err import *

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
   
    program_qec_x, program_qec_z = program_gen_qec_mul(mat, numq, N, rnds)
    
    postcond_x, postcond_z  = stab_cond_gen_multiq(mat, numq, N)
    
    decoder_cond_x, decoder_cond_z, meas_corr_x, meas_corr_z = decode_cond_gen_mul(mat, numq, N, rnds, dx, dz, False) 
    precond_x = recon_string(precond_generator(prog_log, postcond_x, postcond_x)[-1])
    precond_z = recon_string(precond_generator(prog_log, postcond_z, postcond_z)[-1])
    
    meas_cnt_max = max(len(meas_corr_x), len(meas_corr_z))
    bit_width = int(math.log2(numq * N * rnds + meas_cnt_max)) + 1
    
    sum_x = ""
    sum_z = ""
    for ci in meas_corr_x:
        sum_x = sum_x + f"c_({ci}) +"
    for ci in meas_corr_z:
        sum_z = sum_z + f"c_({ci}) +"
    
    sum_x += f"sum i 1 {numq * N * rnds} (cz_(i))"
    sum_z += f"sum i 1 {numq * N * rnds} (cx_(i))" 
    
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
        for i in range(1, N):
            start = i * numq 
            err_gt_x = err_gt_x + f"&&sum i {start + 1} {start + numq} (ez_(i)) <= {(dz -1)}"
            err_gt_z = err_gt_z + f"&&sum i {start + 1} {start + numq} (ex_(i)) <= {(dx -1)}"
            err_cond_x = err_cond_x + f"&&sum i {start + 1} {start + numq} (ez_(i)) <= {(dz -1) //2 }"
            err_cond_z = err_cond_z + f"&&sum i {start + 1} {start + numq} (ex_(i)) <= {(dx -1) //2 }"

        program_x = f"{prog_log};{program_qec_x}"
        program_z = f"{prog_log};{program_qec_z}"
        packed_x = smtencoding(bit_width, precond_x, program_x, postcond_x, 
                            err_cond_x, err_gt_x, 
                            decoder_cond_x)
        packed_z = smtencoding(bit_width, precond_z, program_z, postcond_z, 
                            err_cond_z, err_gt_z, 
                            decoder_cond_z)
        return packed_x, packed_z
    
### Randomly generate samples   
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

## Verify the correctness of a program, which consists of multiple layers of logical operations and error correction blocks. ##
@timebudget
def steane_checker_combine(matrix, dx, dz, program, N, rnds):
    numq = matrix.shape[1] // 2
    
    ## verify the program layer by layer
    for inds, gateinfo in program.items():
        prog_log = program_gen_logic(matrix, numq, N, gateinfo, 'steane')
        
        ## packed_x, packed_z are verification conditions
        if rnds == 1:
            packed_x, packed_z = formula_gen_combine(matrix, dx, dz, 1, N, prog_log)
            t1x, res1_x = seq_cond_checker(packed_x, [0], 'x')
            t1z, res1_z = seq_cond_checker(packed_z, [0], 'z')
            t2x, res2_x = seq_cond_checker(packed_x, [1], 'x')
            t2z, res2_z = seq_cond_checker(packed_z, [1], 'z')
            
            if str(res1_x[0]) == 'unsat' and str(res2_x[0]) == 'unsat':
                print(f"Layer {inds}: All Z error can be corrected;")
            else:
                print(f"Layer {inds}: Exist errors that cannot be corrected;")
            if str(res1_z[0]) == 'unsat' and str(res2_z[0]) == 'unsat':
                print(f"Layer {inds}: All X error can be corrected.")
            else:
                print(f"Layer {inds}: Exist errors that cannot be corrected.")
            print(f"SMT time consumed:{t1x + t2x + t1z + t2z}")
            
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
                
## Towards the fault-tolerant quantum computing, first thing is to                 
def formula_gen_logical(matrix, dx, dz, gates, N):
    numq = matrix.shape[1] // 2
    prog_x, prog_z, err_gt_x, err_gt_z = program_gen_log_err(matrix, numq, N, gates, code = 'steane')
    postcond_x, postcond_z = stab_cond_gen_log(matrix, N)
    bit_width = int(math.log2(numq * N)) + 1
    for ind, gateinfo in gates.items():
        prog_log = program_gen_logic(matrix, numq, N, gateinfo, 'steane')
        pre_tree_x = precond_generator(prog_log, postcond_x, postcond_x)[-1]
        pre_tree_z = precond_generator(prog_log, postcond_x, postcond_z)[-1]
        precond_x = recon_string(pre_tree_x)
        precond_z = recon_string(pre_tree_z)
        
        err_cond_x = f"sum i 1 {numq} (ez_(i)) + sum i 1 {numq} (pz_(i)) <= {(dz - 1) // 2}"
        err_cond_z = f"sum i 1 {numq} (ex_(i)) + sum i 1 {numq} (px_(i)) <= {(dx - 1) // 2}"
        
        for i in range(N):
            start = i * numq 
            err_gt_x = err_gt_x + f"&&sum i {start + 1} {start + numq} (ez_(i)) + sum i {start + 1} {start + numq} (pz_(i))<= {(dz -1)}"
            err_gt_z = err_gt_z + f"&&sum i {start + 1} {start + numq} (ex_(i)) + sum i {start + 1} {start + numq} (px_(i)) <= {(dx -1)}"
            if i >= 1:
                err_cond_x = err_cond_x + f"&&sum i {start + 1} {start + numq} (ez_(i)) + sum i {start + 1} {start + numq} (pz_(i)) <= {(dz - 1) //2}"
                err_cond_z = err_cond_z + f"&&sum i {start + 1} {start + numq} (ex_(i)) + sum i {start + 1} {start + numq} (px_(i)) <= {(dx - 1) //2}"
        
        decoder_cond_x, decoder_cond_z, _, _ = decode_cond_gen_mul(matrix, numq, N, 1, dx, dz, True)
        
        packed_x = smtencoding(bit_width, precond_x, prog_x, postcond_x, 
                            err_cond_x, err_gt_x, 
                            decoder_cond_x)
        
        packed_z = smtencoding(bit_width, precond_z, prog_z, postcond_z,
                            err_cond_z, err_gt_z, 
                            decoder_cond_z)
    
    return packed_x, packed_z
        
## A condition checker, with propagated error considered         
def seq_cond_checker_prop(packed_expr, err_vals, p_vals, nums, opt, prop_free = 1):
    expr, variables, constraints = packed_expr
    if opt == 'x':
        err_val_exprs = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        ## Assume that there is a logical qubit free from propagated error;
        ## If prop_free = 2, then p_vals = all zero, we fill in the errors from back to forth
        if prop_free == 2:
            err_val_exprs.extend([f'(pz_({nums - i})) == {p_vals[i]}' for i in range(len(p_vals))])
        else:
            ## Other wise fill in the values from start.
            err_val_exprs.extend([f'(pz_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    else:
        ### Normal form ### 
        err_val_exprs = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
        if prop_free == 2:
            err_val_exprs.extend([f'(px_({nums - i})) == {p_vals[i]}' for i in range(len(p_vals))])
        else:
            err_val_exprs.extend([f'(px_({i + 1})) == {p_vals[i]}' for i in range(len(p_vals))])
    err_val_exprs_str = ' && '.join(err_val_exprs)
    
    formula = smtencoding_constrep(expr, variables, constraints, err_val_exprs_str)
    t3 = time.time()
    result = smtchecking(formula)
    t4 = time.time()
    return t4 - t3, result

## Verify a error correction program with possible propagated errors. 
@timebudget
def steane_checker_prop(matrix, dx, dz, gates, N):
    numq = matrix.shape[1] // 2 
    prog_log = program_gen_logic(matrix, numq, N, gates[0], 'steane')
    packed_x, packed_z = formula_gen_logical(matrix, dx, dz, gates, N)
    
    p_vals = [0] * numq
    err_vals = [0] * numq * N
    nums = numq * N
    print("Possible propagation error in Qubit Block #1: ")
    t1x, res1_x = seq_cond_checker_prop(packed_x, [0], p_vals, nums, 'x', 2)
    t1z, res1_z = seq_cond_checker_prop(packed_z, [0], p_vals, nums, 'z', 2)
    
    t2x, res2_x = seq_cond_checker_prop(packed_x, [1], p_vals, nums, 'x', 2)
    t2z, res2_z = seq_cond_checker_prop(packed_z, [1], p_vals, nums, 'z', 2)
    ## Analyze the results; We need to append err_vals to final results if counterexample detected. 
    if str(res1_x[0]) == 'unsat' and str(res2_x[0]) == 'unsat':
    
        print(f"All Z error can be corrected;")
    elif str(res1_x[0]) == 'sat':
        print(f"Exist Z errors that cannot be corrected: {res1_x[1]}")
    else:
        res2_x[1].append('ez_1')
        print(f"Exist Z errors that cannot be corrected: {res2_x[1]}")
    
    if str(res1_z[0]) == 'unsat' and str(res2_z[0]) == 'unsat':
    
        print(f"All X error can be corrected.")
    elif str(res1_z[0]) == 'sat':
        print(f"Exist X errors that cannot be corrected: {res1_z[1]}")
    else:
        res2_z[1].append('ex_1')
        print(f"Exist X errors that cannot be corrected: {res2_z[1]}")
   
    print(f"SMT time consumed:{t1x + t2x + t1z + t2z}")
    
    print('----------------------')
    ### Qubit block #1 is free from propagation error, but Qubit block #2 is not.
    print("Possible propagation error in Qubit Block #2: ")
    t1x, res1_x = seq_cond_checker_prop(packed_x, [0], p_vals, nums, 'x', 1)
    t1z, res1_z = seq_cond_checker_prop(packed_z, [0], p_vals, nums, 'z', 1)
    
    t2x, res2_x = seq_cond_checker_prop(packed_x, [1], p_vals, nums, 'x', 1)
    t2z, res2_z = seq_cond_checker_prop(packed_z, [1], p_vals, nums, 'z', 1)
    
    if str(res1_x[0]) == 'unsat' and str(res2_x[0]) == 'unsat':
    
        print(f"All Z error can be corrected;")
    elif str(res1_x[0]) == 'sat':
        print(f"Exist Z errors that cannot be corrected: {res1_x[1]}")
    else:
        res2_x[1].append('ez_1')
        print(f"Exist Z errors that cannot be corrected: {res2_x[1]}")
    if str(res1_z[0]) == 'unsat' and str(res2_z[0]) == 'unsat':
    
        print(f"All X error can be corrected.")
    elif str(res1_z[0]) == 'sat':
        print(f"Exist X errors that cannot be corrected: {res1_z[1]}")
    else:
        res2_z[1].append('ex_1')
        print(f"Exist X errors that cannot be corrected: {res2_z[1]}")
    
    print(f"SMT time consumed:{t1x + t1z}")
    print('----------------------')
    

    ## No propagation error, all errors should be corrected.
    print("Without propagation error:")
    
    packed_x, packed_z = formula_gen_combine(matrix, dx, dz, 1, N, prog_log)
    t1x, res1_x = seq_cond_checker(packed_x, [0], 'x')
    t1z, res1_z = seq_cond_checker(packed_z, [0], 'z')
    t2x, res2_x = seq_cond_checker(packed_x, [1], 'x')
    t2z, res2_z = seq_cond_checker(packed_z, [1], 'z')
    if str(res1_x[0]) == 'unsat' and str(res2_x[0]) == 'unsat':
        print(f"All Z error can be corrected;")
    else:
        print(f"Exist Z errors that cannot be corrected;")
    if str(res1_z[0]) == 'unsat' and str(res2_z[0]) == 'unsat':
        print(f"All X error can be corrected.")
    else:
        print(f"Exist X errors that cannot be corrected.")
    print(f"SMT time consumed:{t1x + t2x + t1z + t2z}")
    print('----------------------')

if __name__ == "__main__" : 
    D = 3
    N = 2
    rnds = 2
    
    matrix = special_codes.stabs_steane()
    
    H = defaultdict(list)
    H[1] = [['H', [1]], ['H', [2]]]
    
    GHZ = defaultdict(list)
    GHZ[0] = [['H', [2]]]
    GHZ[1] = [['CNOT', [2,1]], ['CNOT', [2, 3]]]
    
    print("Example I: Verify Fault-tolerance for GHZ state preparation: ")
    print("----------------------")
    print("Fault-free program: ")
    print(f"Layer 0: {program_gen_logic(matrix, 7, 3, GHZ[0], 'steane')}")
    print(f"Layer 1: {program_gen_logic(matrix, 7, 3, GHZ[1], 'steane')}")
    print("Verify with Faults injected:")
    steane_checker_combine(matrix, D, D, GHZ, 3, 1)


    CNOT = {}
    CNOT[0] = [['CNOT', [1, 2]]]
    print("Example II: Verify Fault-tolerance for CNOT gate with propagated error: ")
    steane_checker_prop(matrix, D, D, CNOT, 2)

   