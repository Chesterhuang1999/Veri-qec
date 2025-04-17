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

distance_candidate = [3, 5, 7]

output_dir = './eval-Output'
if not os.path.exists(output_dir):
    os.makedirs(output_dir)
file_name_head = f'{output_dir}/correction_surface.txt'
with open(file_name_head, 'w') as f:
    with redirect_stdout(f):
        print("Verifying correction property on surface code")
        
        print(f"Baseline method:sequential")

        for i in range(1, 3):
    
            d = 2 * i + 1
            print(f"Distance {d}:")
            t1, t2, result = serial_cond_checker(d)
            
            print(f"total time for Verification: {t2:.5f} sec")
            print(f"cond_checker_serial took {t1 + t2:.5f} sec")

        print("--------------------------")
        print("Our method: parallel")
        print(f"Using {max_proc_num} CPU cores for parallel processing.")

        for d in distance_candidate:
            print(f"Distance {d}:")
            file_name = file_name_head + f"_{d}.txt"
    
            sur_cond_checker_verify(d, max_proc_num)
            print("---------------------")
    
        print("Finish all the evaluations.")