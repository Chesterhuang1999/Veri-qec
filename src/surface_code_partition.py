import sys
from condition import stab_cond_gen, surface_matrix_gen, program_gen, decode_cond_gen
from verifier import precond_generator
from encoder import tree_to_z3, const_errors_to_z3, VCgeneration
from z3 import *
from timebudget import timebudget 
import cvc5
from itertools import combinations
import math
from collections import defaultdict
import argparse
import json
from smtchecking_partition import *
sys.setrecursionlimit(1000000)

def cond_generator(distance):
    num_qubits = distance**2
    max_errors = (distance - 1) // 2
    bit_width = int(math.log2(num_qubits)) + 1
    max_errors = (distance - 1) // 2 
    surface_mat = surface_matrix_gen(distance)
    precond_x, precond_z = stab_cond_gen(surface_mat, num_qubits, 1)
    #precond, cond2, x_inds, z_inds = surface(distance, 1)
    err_cond_z = f"sum i 1 {num_qubits} (ex_(i)) <= {max_errors}"
    err_cond_x = f"sum i 1 {num_qubits} (ez_(i)) <= {max_errors}"
    err_gt_z = f"sum i 1 {num_qubits} (ex_(i)) <= {distance - 1}"
    err_gt_x = f"sum i 1 {num_qubits} (ez_(i)) <= {distance - 1}"
    postcond_x, postcond_z = precond_x, precond_z

    # err_val_exprs_x = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    # err_val_exprs_str_x = ' && '.join(err_val_exprs_x)

    # err_val_exprs_z = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    # err_val_exprs_str_z = ' && '.join(err_val_exprs_z)
    
    program_x, program_z = program_gen(surface_mat, num_qubits, 1)
    decoder_cond_x, decoder_cond_z = decode_cond_gen(surface_mat, num_qubits, 1, distance, distance)
    groups = sym_gen(distance, distance)
    sym_x, sym_z = [], []
    for value in groups.values():
        k, l = value[0], value[1]
        sym_x.append(f"ex_({k + 1}) <= ex_({l + 1})")
        sym_z.append(f"ez_({k + 1}) <= ez_({l + 1})")
    sym_x, sym_z = '&&'.join(sym_x), '&&'.join(sym_z)
    triple_x = [precond_x, program_x, postcond_x]
    triple_z = [precond_z, program_z, postcond_z]

    # err_x = [err_cond_x, err_gt_x]
    err_z = [err_cond_z, err_gt_z]
    cond_x = [triple_x, err_x, decoder_cond_x, sym_x]
    cond_z = [triple_z, err_z, decoder_cond_z, sym_z]
    return cond_x, cond_z, bit_width
    # err_x = [err_cond_x, err_gt_x, err_val_exprs_str_x]
    # # err_z = [err_cond_z, err_gt_z, err_val_exprs_str_z]
    # sym_x, sym_z = ' '  , ' '
#    formula_x = smtencoding(precond_x, program_x, postcond_x, 
#                             err_cond_x, err_gt_x, err_val_exprs_str_x,
#                             decoder_cond_x, bit_width)
#    formula_z = smtencoding(precond_z, program_z, postcond_z, 
#                             err_cond_z, err_gt_z, err_val_exprs_str_z, 
#                             decoder_cond_z, bit_width)
    cond_x = [triple_x, err_x, decoder_cond_x, sym_x]
    cond_z = [triple_x, err_x, decoder_cond_z, sym_z]
    return cond_x, cond_z, bit_width

def sur_seq_cond_checker(cond_x, cond_z, bit_width, err_vals):
    triple_x, err_x, decoder_cond_x, sym_x = 
    err_val_exprs_x = [f'(ez_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    err_val_exprs_str_x = ' && '.join(err_val_exprs_x)

    err_val_exprs_z = [f'(ex_({i + 1})) == {err_vals[i]}' for i in range(len(err_vals))]
    err_val_exprs_str_z = ' && '.join(err_val_exprs_z)
    formula_x = smtencoding_parti('surface', triple_x, err_x,
                            decoder_cond_x, sym_x, bit_width)
    formula_z = smtencoding_parti('surface', triple_z, err_z,  
                            decoder_cond_z, sym_z, bit_width)
    result_x = smtchecking(formula_x)
    result_z = smtchecking(formula_z)
    # print(result_x)
    return result_x, result_z
    # print(result_x, result_z)

# # @timebudget
# def sur_cond_checker(distance, enum_qubit):
#     counter = 0
#     # assert(enum_qubit <= distance)
#     num_qubits = distance ** 2
#     if enum_qubit > num_qubits:
#         enum_qubit = num_qubits
    
#     # if enum_qubit < distance:
#     #     enum_qubit = distance
    
#     # enum_qubit \in [1, d ^ 2]
#     # one_num <= enum
#     # error number:
#     # [1, distance) [1, enum_qubit + 1)

#     err_vals = [0 for _ in range(enum_qubit)]
#     sur_seq_cond_checker(distance, err_vals)
#     for one_num in range(1, min(distance, enum_qubit + 1)):
#         for pos in combinations(range(enum_qubit), one_num):
#             # print(pos)
#             err_vals = [0 for _ in range(enum_qubit)]
#             for j in pos:
#                 err_vals[j] = 1
#             # print(err_vals)
#             sur_seq_cond_checker(distance, err_vals)

# def sur_cond_checker_alt(num_qubits, enum_qubit):
#     counter = 0
#     # assert(enum_qubit <= distance)
#     # num_qubits = distance ** 2
#     if enum_qubit > num_qubits:
#         enum_qubit = num_qubits

#     err_vals = [0 for _ in range(enum_qubit)]
#     if num_qubits > enum_qubit + distance:
#         seq_cond_checker(num_qubits - enum_qubit, err_vals)

#     for one_num in range(1, min(distance, enum_qubit + 1)):
#         for pos in combinations(range(enum_qubit), one_num):
#             # print(pos)
#             err_vals = [0 for _ in range(enum_qubit)]
#             for j in pos:
#                 err_vals[j] = 1
#             # print(err_vals)
#             seq_cond_checker(distance, err_val)
# (1 + t) ^ (d^2) <
# < d
# 0 * '1' -> 1 * '1' -> 2 * '1' -> 
# Debug

if __name__ == '__main__':
    # arg_parser = argparse.ArgumentParser()
    # arg_parser.add_argument('--distance', type=int, required=True, 
    #                             help='distance')
    # arg_parser.add_argument('--err-vals', type=str, required=True, 
    #                             help='error values')
    
    # cmd_args = arg_parser.parse_args()
    # distance: int = cmd_args.distance
    # err_vals: list = json.loads(cmd_args.err_vals)
    # print(distance, err_vals)
    # for x in err_vals:
    #     print(x, type(x))
    # err_vals = [int(x) for x in err_vals]
    # print(distance, err_vals)
    # seq_cond_checker(distance, err_vals)
    
    # sur_cond_checker(3, 1)
    sur_cond_checker(5, 4)
    # seq_cond_checker(7, [0 for i in range(24)])
    #print(encode_time, check_time) 
    # x = [2*i+1 for i in range(1, 5)]
    # # #x.append(25)
    # for i in x:
    #     sur_cond_checker(i, encode_time, check_time)

    # plt.plot(x, encode_time, label = "Encoding Time"
    # plt.plot(x, check_time, label = "Checking Time")
    # plt.xlabel('Code Distance')
    # plt.ylabel('Time (s)')
    # plt.title('Surface Code Verification Time')
    # plt.legend()
    # plt.savefig('surface_9.png')
