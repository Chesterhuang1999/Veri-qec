import numpy as np
import time
import math
from collections import defaultdict
# For test
from parser_qec import get_parser
from transformer import precond_generator
from lark.reconstruct import Reconstructor
import re
##
from encoder import *
### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   
# Here is a condition generation for logical operations which perform on multiple logical qubits


### Condition and program generation from check matrix ###
def decode_cond_gen_multiq(H, n, k, N, dx, dz): 
    cond_parts_x = []
    cond_parts_z = []
    max_err_x = int((dx - 1) // 2)
    max_err_z = int((dz - 1) // 2)
    # start = (rnd - 1) * N
    for cnt in range(N): 
        cpx = []
        cpz = []
        for i in range(n - k):
            if np.all(H[i, :n] == 0) == False:
                cpx.extend(f"s_({i + 1 + cnt * (n - k)}) == ")
                for j in range(n):
                    if H[i][j] == 1 :
                        cpx.extend(f"cz_({j + 1 + cnt * n})")
                        cpx.append("@^")
                cpx.pop()
                cpx.append("&&")
            if np.all(H[i, n:] == 0) == False:
                cpz.extend(f"s_({i + 1 + cnt * (n - k)}) == ")
                for j in range(n):
                    if H[i][j + n] == 1:
                        cpz.extend(f"cx_({j + 1 + cnt * n})")
                        cpz.append("@^")
                cpz.pop()
                cpz.append("&&")

        cpx.append(f"sum i {1 + cnt * n} {n + cnt * n} (cz_(i)) <= Min(sum i {1 + cnt *n} {n + cnt*n} (ez_(i)), {max_err_z})")
        cpz.append(f"sum i {1 + cnt * n} {n + cnt * n} (cx_(i)) <= Min(sum i {1 + cnt *n} {n + cnt*n} (ex_(i)), {max_err_x})")
        cond_parts_x.append(''.join(cpx))
        cond_parts_z.append(''.join(cpz))
    return '&&'.join(cond_parts_x), '&&'.join(cond_parts_z)

def decode_cond_gen_mul(H, n, k, N, rnd):
   pass

def stab_cond_gen_multiq(H, n, k, N):
    cond_parts_x = []
    cond_parts_z = []
    for cnt in range(N):
        cpx, cpz = [], []
        for i in range(n - k):
            hasx, hasz = False, False
            for j in range(n):
                if H[i][j] == 1:
                    cpx.extend(f"(0,1,{j + 1 + cnt * n})")
                    hasx = True
                if H[i][j + n] == 1:
                    cpz.extend(f"(1,0,{j + 1 + cnt * n})")
                    hasz = True
            if hasx == True:
                cpx.append("&&")
            if hasz == True:
                cpz.append("&&")

        for i in range(2 * k):
        
            if np.all(H[n - k + i, :n] == 0) == False:
                cpx.append(f"(-1)^(b_({i + 1 + cnt * k}))")
                for j in range(n):
                    if H[n - k + i][j] == 1:
                        cpx.extend(f"(0,1,{j + 1 + cnt * n})")
                cpx.append("&&")
            if np.all(H[n - k + i, n:] == 0) == False:
                cpz.append(f"(-1)^(b_({i + 1 + (cnt - 1) * k}))")
                for j in range(n):
                    if H[n - k + i][j + n] == 1:
                        cpz.extend(f"(1,0,{j + 1 + cnt * n})")
                cpz.append("&&")
        if len(cpx) > 0: 
            cpx.pop()
        if len(cpz) > 0:
            cpz.pop()
        cond_parts_x.append(''.join(cpx))
        cond_parts_z.append(''.join(cpz))
    return '&&'.join(cond_parts_x), '&&'.join(cond_parts_z)

### Generation of error correction programs ### 
def program_gen_qec(H, n, k, N):   
    prog_parts_x = []
    prog_parts_z = []
    prog_parts_z.append(f"for i in 1 to {n} do q_(i) *= ex_(i) X end;")
    prog_parts_x.append(f"for i in 1 to {n} do q_(i) *= ez_(i) Z end;")
    for cnt in range(N):
        ppx = []
        ppz = []
        for i in range(n - k):
            if (np.all(H[i,:n] == 0) == False):
                ppx.append(f"s_({i + 1 + cnt * (n-k)}) := meas")
                for j in range(n):
                    if H[i][j] == 1:
                        ppx.append(f"(0,1,{j + 1 + cnt * n})")
                ppx.append("; ")
            if (np.all(H[i,n:] == 0) == False):
                ppz.append(f"s_({i + 1 + cnt * (n - k)}) := meas")
                for j in range(n):
                    if H[i][j + n] == 1:
                        ppz.append(f"(1,0,{j + 1 + cnt * n})")
                ppz.append(";")
        prog_parts_x.append(''.join(ppx))
        prog_parts_z.append(''.join(ppz))
    prog_parts_z.append(f"for i in 1 to {n} do q_(i) *= cx_(i) X end")
    prog_parts_x.append(f"for i in 1 to {n} do q_(i) *= cz_(i) Z end")
    return ''.join(prog_parts_x), ''.join(prog_parts_z)

def program_gen_qec_mul(H, n, k, N, rnd):
    prog_x, prog_z = [], []
    for m in range(rnd):
        prog_parts_x = []
        prog_parts_z = []
        prog_parts_z.append(f"for i in {1} to {n} do q_(i) *= ex_(i + {m * n}) X end;")
        prog_parts_x.append(f"for i in {1} to {n} do q_(i) *= ez_(i + {m * n}) Z end;")
        for cnt in range(N):
            s_base = cnt * (n - k) + m * (n - k)
            print(s_base)
            q_base = cnt * n 
            ppx = []
            ppz = []
            for i in range(n - k):
                if (np.all(H[i,:n] == 0) == False):
                    if m >= 1:
                        ppx.append(f"s_({i + 1 + s_base}) := s_({i + 1 + s_base}) + e_({i + 1 + s_base});")
                    ppx.append(f"s_({i + 1 + s_base}) := meas")
                    for j in range(n):
                        if H[i][j] == 1:
                            ppx.append(f"(0,1,{j + 1 + q_base})")
                    ppx.append(";")
                if (np.all(H[i,n:] == 0) == False):
                    if m >= 1:
                        ppz.append(f"s_({i + 1 + s_base}) := s_({i + 1 + s_base}) + e_({i + 1 + s_base});")
                    ppz.append(f"s_({i + 1 + s_base}) := meas")
                    for j in range(n):
                        if H[i][j + n] == 1:
                            ppz.append(f"(1,0,{j + 1 + q_base})")
                    ppz.append(";")

            prog_parts_x.append(''.join(ppx))
            prog_parts_z.append(''.join(ppz))
        if m == rnd - 1:
            prog_parts_z.append(f"for i in {1} to {n} do q_(i) *= cx_(i) X end")
            prog_parts_x.append(f"for i in {1} to {n} do q_(i) *= cz_(i) Z end")
        tempx = ''.join(prog_parts_x)
        tempz = ''.join(prog_parts_z)
        if tempx[-1] == ';':
            tempx = tempx[:-1]
        if tempz[-1] == ';':
            tempz = tempz[:-1]

        prog_z.append(tempz)
        prog_x.append(tempx)

        # if m < rnd - 1:
        #     prog_parts_z.append(";")
        #     prog_parts_x.append(";")
    # prog_x = ''.join(prog_parts_x)
    # prog_z = ''.join(prog_parts_z)
    # print("prog_x: ", prog_x)   
    # print("prog_z: ", prog_z)
    # return prog_x, 
    return prog_x, prog_z



### Condition and program generation for special codes ###

##Surface code
def surface_matrix_gen(n):
    H = np.zeros((n * n + 1, 2 * n * n), dtype = int)
    t = n // 2
    halfrow = (pow(n, 2) - 1) // 2
    z_cnt = 0
    x_cnt = 0
    for i in range(t):
        i2 = 2 * i
        for j in range(t):
            j2 = 2 * j
            topl_od_z = i2 * n + j2 
            topl_ev_z = (i2 + 1) * n + (j2 + 1)
            topl_od_x = (i2) * n + (j2 + 1)
            topl_ev_x = (i2 + 1) * n + (j2)
            for k in [topl_od_x, topl_ev_x]:
                H[x_cnt][k] = 1
                H[x_cnt][k + 1] = 1
                H[x_cnt][k + n] = 1
                H[x_cnt][k + n + 1] = 1
                x_cnt += 1
            for k in [topl_od_z, topl_ev_z]:
                k1 = k + n * n
                H[halfrow + z_cnt][k1] = 1
                H[halfrow + z_cnt][k1 + 1] = 1
                H[halfrow + z_cnt][k1 + n] = 1
                H[halfrow + z_cnt][k1 + n + 1] = 1
                z_cnt += 1
        H[x_cnt][i2 * n] = 1
        H[x_cnt][(i2 + 1) * n] = 1
        x_cnt += 1
        temp = (i2 + 2) * n - 1 
        H[x_cnt][temp] = 1
        H[x_cnt][temp + n] = 1    
        x_cnt += 1
        H[halfrow + z_cnt][i2 + 1 + n * n] = 1
        H[halfrow + z_cnt][i2 + 2 + n * n] = 1
        z_cnt += 1
        temp = i2 + (2*n-1) * n
        H[halfrow + z_cnt][temp] = 1
        H[halfrow + z_cnt][temp + 1] = 1
        z_cnt += 1

    for i in range(n):
        H[n * n - 1][i] = 1
    
    for i in range(n):
        H[n * n][(n + i) * n] = 1 
    
    return H
def rep_cond(n, k): ## n: num of physical qubits, k: num of logical qubits
    #row_ind, col_ind = zip(*((i, j) for i in range(1, n) for j in (i, (i + 1))))
    cond = ""
    for i in range(1, n):
        cond = cond + f"(1,0,{i})" + f"(1,0,{i+1})&&"
    cond = cond + f"(-1)^(b_(1))(1,0,1)"
    # for i in range(1,n+1):
    #     cond = cond + f"(1,0,{i})"
    return cond

def rep_program(n):
    program = ""
    program = program + f"for i in 1 to {n} do q_(i) *= e_(i) X end;"
    for i in range(1, n):
        program = program + f"s_({i}) := meas (1,0,{i})(1,0,{i+1}); "
    program = program + f"for i in 1 to {n} do q_(i) *= c_(i) X end"

    return program

### Condition and program generation for logical operation ###
#### Here we have to design programs specifically for each code, so only special cases are considered ####
def program_gen_logic(matrix, numq, N, gateinfo, code):
    prog_parts_log = []
    prog_parts_x, prog_parts_z = [], []
    
    for i in range(len(gateinfo)):
        gate, inds = gateinfo[i]
        if gate == 'CNOT':
            assert len(inds) == 2
            k, l = inds[0], inds[1]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q1 = (k - 1) * numq + i
                    q2 = (l - 1) * numq + i
                    prog_parts_log.append(f"q_({q1}), q_({q2}) *= CNOT")
            # elif code == '':
        elif gate == 'H':
            assert len(inds) == 1
            k = inds[0]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q = (k - 1) * numq + i
                    prog_parts_log.append(f"q_({q}) *= H")
    prog_log =  ';'.join(prog_parts_log)
    return prog_log
    

if __name__ == "__main__":
    mat = surface_matrix_gen(3)

    ## Program and condition for Measurement error
    # def program_gen_meas(matrix, numq, k, N, rnd):
    Zmat = np.array([[1,1,0],[0,1,1],[0,0,1]])
    mat = np.zeros((4, 6), dtype = int) 
    mat[0:3,3:] = Zmat
    _, prog_z_parts = program_gen_qec_mul(mat, 3, 1, 1, 2)

    for i in range(len(prog_z_parts)):
        print(f"{i}-th meas:", prog_z_parts[i])
    
    _, postcond_z = stab_cond_gen_multiq(mat, 3, 1, 1)
    precond_z = postcond_z
    print("precond_z: ", precond_z)
    # for i in range(len(prog_z_parts)):
    #     pre_tree, program_tree, post_tree = precond_generator(prog_z_parts[i], precond_z, postcond_z)
    #     cass_transformer = qassertion2c(pre_tree)
    #     cass_tree = cass_transformer.transform(post_tree.children[0].children[-1])
    #     cass_tree = simplifyeq().transform(cass_tree)
    #     # print("cass_tree: ", cass_tree)
    #     print(tree_to_z3(cass_tree, {}, 1, [], False))
    pre_tree, program_tree, post_tree1 = precond_generator(prog_z_parts[1], precond_z, postcond_z) 
    postcond_z1 = re.sub( r'\s*_\s*', '_', Reconstructor(parser = get_parser()).reconstruct(post_tree1.children[0].children[-1]))
    print("postcond_z1: ", postcond_z1)
    pre_tree, program_tree, post_tree2 = precond_generator(prog_z_parts[0], precond_z, postcond_z1) 
    postcond_z2 = re.sub( r'\s*_\s*', '_', Reconstructor(parser = get_parser()).reconstruct(post_tree2.children[0].children[-1]))
    print("postcond_z2: ", postcond_z2)
    cass_transformer = qassertion2c(post_tree1)
    cass_tree = cass_transformer.transform(post_tree2.children[0].children[-1])
    cass_tree = simplifyeq().transform(cass_tree)
    print("formula:", tree_to_z3(cass_tree, {}, 1, [], False))
    # _, program_tree, post_tree2 = precond_generator(prog_z_parts[0], precond_z, post_cond_z)
    # cass_transformer = qassertion2c(pre_tree)
    # cass_tree1 = 
    # cass_tree = cass_transformer.transform(post_tree1.children[0].children[-1])
    # cass_tree = simplifyeq().transform(cass_tree)
    # cass_tree = VCgeneration(precond_x, program_x, postcond_x)
    # print(tree_to_z3(cass_tree, {}, 1, [], False))