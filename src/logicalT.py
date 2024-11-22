from condition import *
import numpy as np
from transformer import precond_generator, recon_string
import sys
import time
sys.setrecursionlimit(10**7)

def program_const(distance):
    matrix = surface_matrix_gen(distance)
    numq = distance**2
    prog_part = []
    for i in range(1, numq):
        if (matrix[numq-1][i] == 1):
            prog_part.append(f"q_(1), q_({i + 1}) *= CNOT;")
    for i in range(1, numq):
        if(matrix[numq][i + numq] == 1):
            prog_part.append(f"q_({i + 1}), q_(1) *= CNOT;")

    return " ".join(prog_part)[:-1]

def computeT1(distance):
    start = time.time()
    numq = distance**2
    matrix = surface_matrix_gen(distance)
    condx, condz = stab_cond_gen(matrix, numq, 1)
    # print(condx, condz)
    program = program_const(distance)
    # print(program)
    condx_tree = precond_generator(program, condx ,condx)[-1]
    condz_tree = precond_generator(program, condz, condz)[-1]
    condx_trans = recon_string(condx_tree)
    condz_trans = recon_string(condz_tree)
    
    end = time.time()
    return end - start

if __name__ == "__main__":
    list_d = [3,5,7,9,11,21,31,41,51,61,71]
    time_T = []
    for i in range(len(list_d)):
        print(f"Distance: {list_d[i]}, Time: ")
        timei = computeT1(list_d[i])
        time_T.append(timei)
        print(timei)
        print("\n")

    print(time)
    