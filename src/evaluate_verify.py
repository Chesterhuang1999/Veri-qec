from execute_verify import cond_checker_verify, sur_cond_checker_verify
from execute_serial import serial_cond_checker
from contextlib import redirect_stdout  
import argparse
import tblib.pickling_support
import numpy as np
import sys
import os
import time

sys.setrecursionlimit(10**6)

tblib.pickling_support.install()

parser = argparse.ArgumentParser(description='Process the metadata.')
parser.add_argument('--cpucount', type=int, default = 8, help='Number of CPU cores to use')
args = parser.parse_args()
max_proc_num = args.cpucount

distance_candidate = [3, 5, 7, 9, 11]

output_dir = './eval-Output'
if not os.path.exists(output_dir):
    os.makedirs(output_dir)
file_name_head = f'{output_dir}/correction_surface'
with open(file_name_head, 'w') as f:
    with redirect_stdout(f):
        print("Verifying correction property on surface code")
        
        print(f"Baseline method:serial")
# print(f"Verifying correction property sequentially")
        for i in range(1, 4):
    
            d = 2 * i + 1
            print(f"Distance {d}:")
            time, result = serial_cond_checker(d)
            print(f"Verification time: {time:.5f} seconds")

print("--------------------------")

print(f"Using {max_proc_num} CPU cores for parallel processing.")
print(f"Detailed outputs will be redirected to files in the eval-Output directory.")

print(f"Verifying correction property on surface code")
for d in distance_candidate:
    print(f"Distance {d}:")
    file_name = file_name_head + f"_{d}.txt"
    with open(file_name, 'w') as f:
        with redirect_stdout(f):
                
            sur_cond_checker_verify(d, max_proc_num)
    print("---------------------")
    
print("Finish all the evaluations.")