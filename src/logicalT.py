from condition import *
import numpy as np
from lark import Token
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
    # prog_part.append(f"q_(1) *= T;")
    prog_T = "q_(1) *= T;"
    prog_part_rev = prog_part[::-1]
    
    prog_op = " ".join(prog_part)
    prog_rev = " ".join(prog_part_rev)[:-1]
    prog = prog_op + prog_T + prog_rev
    return prog, prog_op[:-1]
def computeT1(distance):
    start = time.time()
    numq = distance**2
    matrix = surface_matrix_gen(distance)
    condx, condz = stab_cond_gen(matrix, numq, 1)
    
    # condx = "QR2[0,1,1](1,1,1) + QR2[0,1,1](-1)^(b_(1))(0,1,1)" + condx[7:]
    # print(condx)
    # condx_str = recon_string(condx)
    # condz_str = recon_string(condz)
    # print(condx, condz)
    program, prog_op = program_const(distance)
    
    print(program)
    condx_tree = precond_generator(program, condx ,condx)[-1]
    condx_tree_orig = precond_generator(prog_op, condx, condx)[-1]
    # condz_tree = precond_generator(program, condz, condz)[-1]
    # condx_tree.children[0].children[0].children[0] = 
    # condx_tree.children[0].children[0].children[0].children[0] = Token('NUMBER', 1)
    condx_trans = recon_string(condx_tree)
    condx_orig = recon_string(condx_tree_orig)
    print(condx_trans)
    print(condx_orig)
    # condx_trans = "QR2[0,1,1](1,1,1) + QR2[0,-1,1](0,1,1)" + condx_trans[7:]
    # print(condx_trans)
    # condx_orig_tree = precond_generator(prog_rev, condx, condx_trans)[-1]
    # print(condx_orig_tree)
    # condx_orig = recon_string(condx_orig_tree)
    # print(condx_orig)
    # condz_trans = recon_string(condz_tree)
    exit(0)
    # print(condx_trans, condz_trans)
    end = time.time()
    return end - start, condx_str, condz_str, condx_trans, condz_trans

if __name__ == "__main__":
    list_d = [3,5,7,9,11,21,31,41,51,61,71]
    
    time, cxs, czs, cxe, cze = computeT1(3)

    print(cxs)
    print(cxe)

    # time_T = []
    # for i in range(len(list_d)):
    #     print(f"Distance: {list_d[i]}, Time: ")
    #     timei = computeT1(list_d[i])
    #     time_T.append(timei)
    #     print(timei)
    #     print("\n")

    # print(time)
    