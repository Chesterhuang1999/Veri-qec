from contextlib import redirect_stdout  
import argparse
import tblib.pickling_support
import numpy as np
import sys
import os

from Dataset import qldpc_codes, special_codes
from execute_verify import cond_checker_verify
from execute_detect import cond_checker_detect
from execute_detect_Tanner import cond_checker_Tanner

sys.setrecursionlimit(10**6)

tblib.pickling_support.install()

parser = argparse.ArgumentParser(description='Process the metadata.')
parser.add_argument('--cpucount', type=int, default = 8, help='Number of CPU cores to use')
args = parser.parse_args()
max_proc_num = args.cpucount
output_dir = './eval-Output'
if not os.path.exists(output_dir):
    os.makedirs(output_dir)


file_name_corr = f'{output_dir}/eval_correction_benchmarks.txt'
with open(file_name_corr, 'w') as f:
    with redirect_stdout(f):

        print(f"Verifying correction property on code benchmarks:")

        print(f"Using {max_proc_num} CPU cores for parallel processing.")
        print(f"-----------")
    # file_name = file_name_head + f"_613code.txt"
        print(f"Steane code:")
        matrix = special_codes.stabs_steane()
        cond_checker_verify(matrix, 3, 3, max_proc_num)

        print(f"----------")
        print(f"[[6,1,3]] code:")
        matrix = special_codes.stabs_613()
        cond_checker_verify(matrix, 3, 3, max_proc_num)

        print(f"----------")
        print(f"[[11,1,5]] code:")
        matrix = special_codes.stabs_1115()
        cond_checker_verify(matrix, 5, 5, max_proc_num)

        print(f"----------")
        print(f"reed-muller code with m = 8:")
        matrix = special_codes.stabs_Reed_Muller(8)

        cond_checker_verify(matrix, 3, 3, max_proc_num)

        print(f"----------")
        print(f"XZZX code with dx = 9, dz = 11:")
        matrix = special_codes.stabs_XZZX(9, 11)

        cond_checker_verify(matrix, 9, 11, max_proc_num)

        print(f"----------")
        print(f"[[2^r, 2^r-r-2, 3]] Gottesman code with r = 8:")
        matrix = special_codes.stabs_gottesman(8)

        cond_checker_verify(matrix, 3, 3, max_proc_num)

        print(f"----------")
        print(f"Honeycomb with distance = 5:")
        matrix = special_codes.stabs_honeycomb(5)
        
        cond_checker_verify(matrix, 5, 5, max_proc_num)
        print("Finish all the evaluation.")


file_name_dete = f'{output_dir}/eval_detection_benchmarks.txt'
with open(file_name_dete, 'w') as f:
    with redirect_stdout(f):
        print(f"Verifying detection property on code benchmarks:")
        print(f"Using {max_proc_num} CPU cores for parallel processing.")
        print(f"-----------")
        print(f"[[8,3,2]] 3D color code:")
        matrix = special_codes.stabs_832code()
        cond_checker_detect(matrix, 4, 2, max_proc_num)

        print(f"-----------")
        print(f"carbon code:")
        matrix = special_codes.stabs_carbon()
        cond_checker_detect(matrix, 4, 4, max_proc_num)

        print(f"-----------")
        print(f"[[3k+8,k,2]] Triorthogonal code:")
        matrix = special_codes.stabs_triotho(64)
        cond_checker_detect(matrix, 6, 2, max_proc_num)

        print(f"-----------")
        print(f"[[6k+2, 3k, 2]] campbell-howard code:")
        matrix = special_codes.stabs_camp_howard(2)
        cond_checker_detect(matrix, 4, 2, max_proc_num)

        print(f"-----------")
        print(f"Hypergraph product code constructed by classical [7,3,4] code:")
        classical734 = np.array([[1, 1, 0, 1, 0, 0, 0],
                        [0, 1, 1 ,0, 1, 0, 0],
                        [0, 0, 1, 1, 0, 1, 0],
                        [0, 0, 0, 1, 1, 0, 1],
                        [1, 0, 0, 0, 1, 1, 0],
                        [0, 1, 0, 0, 0, 1, 1],
                        [1, 0, 1, 0, 0, 0, 1]], dtype = int)
        
        matrix = qldpc_codes.stabs_hyp_prod(classical734, classical734)
        cond_checker_detect(matrix, 4, 4, max_proc_num)

        print("Finish all the evaluation.")
file_name_head = f'{output_dir}/detection_benchmar_tanner'

file_name = file_name_head + f"_Tanner_Rep51.txt"
with open(file_name, 'w') as f:
    with redirect_stdout(f):
        
        print(f"Quantum Tanner code constructed by classical [5, 1, 5] repetition code:")
        Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0],
                        [1, 0, 1, 1, 0, 1, 0],
                        [0, 1, 1, 1, 0, 0, 1]])
        Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                        [0, 1, 0, 0, 1, 0, 1],
                        [0, 0, 1, 0, 0, 1, 1],
                        [0 ,0, 0, 1, 1, 1, 1]])
        Rep51 = np.array([[1, 1, 0, 0, 0],
                        [1, 0, 1, 0, 0],
                        [1, 0, 0, 1, 0],
                        [1, 0, 0, 0, 1]])
        Par54 = np.array([[1, 1, 1, 1, 1]])
        matrix = qldpc_codes.stabs_Tanner(1, 1, Par54, Rep51)
        cond_checker_Tanner(matrix, 4, 4, max_proc_num)


matrix = qldpc_codes.stabs_Tanner(1, 1, Ham743, Ham733)
file_name = file_name_head + f"_Tanner_Ham733.txt"
with open(file_name, 'w') as f:
    with redirect_stdout(f):
    
        print(f"Quantum Tanner code constructed by classical [7, 3, 3] Hamming code:")

        cond_checker_Tanner(matrix, 4, 4, max_proc_num)


