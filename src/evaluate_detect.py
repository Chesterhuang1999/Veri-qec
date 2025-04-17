## Test script for precise detection property on surface code ##

from execute_detect import cond_checker_detect, sur_cond_checker_detect

from contextlib import redirect_stdout  
import argparse
import numpy as np
import sys
import os
import tblib.pickling_support

sys.setrecursionlimit(10**6)

tblib.pickling_support.install()

parser = argparse.ArgumentParser(description='Process the metadata.')
parser.add_argument('--cpucount', type=int, default = 8, help='Number of CPU cores to use')
args = parser.parse_args()
max_proc_num = args.cpucount

output_dir = './eval-Output'
# distance_candidate = [5, 7, 9, 11, 13, 17, 21, 23, 25]

distance_candidate = [7, 9, 11]
if not os.path.exists(output_dir):
    os.makedirs(output_dir)
file_name_head = f'{output_dir}/detection_surface.txt'
with open(file_name_head, 'w') as f:
    with redirect_stdout(f):
        print("Verifying detection property on surface code")
        print(f"Using {max_proc_num} CPU cores for parallel processing.")

# print(f"Detailed outputs will be redirected to files in the eval-Output directory.")
        for d in distance_candidate:
            print(f"Distance {d}")     
            sur_cond_checker_detect(d, max_proc_num)
    
        print("Finish all the evaluations.")