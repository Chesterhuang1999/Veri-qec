from execute_user_provide import cond_checker_usrprov, sur_cond_checker_usrprov

from contextlib import redirect_stdout  
import argparse
import tblib.pickling_support
import numpy as np
import sys
import os

sys.setrecursionlimit(10**6)

tblib.pickling_support.install()

parser = argparse.ArgumentParser(description='Process the metadata.')
parser.add_argument('--cpucount', type=int, default = 8, help='Number of CPU cores to use')
args = parser.parse_args()
max_proc_num = args.cpucount

# distance_candidate = [3, 5, 7, 9, 11, 13, 15, 17, 19]

output_dir = './eval-Output'
if not os.path.exists(output_dir):
    os.makedirs(output_dir)
file_name_head = f'{output_dir}/eval_usrprov_surface.txt'
with open(file_name_head, 'w') as f:
    with redirect_stdout(f):
        print(f"Verifying with user-provided constraints")
        print(f"Using {max_proc_num} CPU cores for parallel processing.")
        
### Verification with only discreteness
        distance_candidate = [3, 5, 7, 9, 11]
        print("Verifying Correction Property on Surface code with Discreteness constraint")
        cstype = "discrete"
        for d in distance_candidate:
            print(f"Distance {d}:")
            sur_cond_checker_usrprov(d, max_proc_num, cstype)
            print("-----------------")   
### Verification with only locality
        distance_candidate = [5, 7, 9, 11, 13]
        cstype = "local"
        print("Verifying Correction Property on Surface code with Locality constraint")
        for d in distance_candidate:
            print(f"Distance {d}:")
            sur_cond_checker_usrprov(d, max_proc_num, cstype)
            print("-----------------")   
### Verification with both discreteness and locality
        distance_candidate = [5, 7, 9, 11, 13, 15, 17, 19]
        cstype = "combined"
        print("Verifying Correction Property on Surface with Discreteness and Locality constraints")
        for d in distance_candidate:
            print(f"Distance {d}:")
    
                
            sur_cond_checker_usrprov(d, max_proc_num, cstype)
            print("-----------------")


        print("Finish all the evaluations.")