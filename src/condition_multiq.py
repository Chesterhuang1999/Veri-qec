import numpy as np
import time
import math
from collections import defaultdict
# For test
from parser_qec import get_parser
from transformer import precond_generator
from lark.reconstruct import Reconstructor
import re
from Dataset import special_codes
##
from encoder import *
### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   
# Here is a condition generation for logical operations which perform on multiple logical qubits


### Condition and program generation from check matrix ###
def decode_cond_gen(H, n, N, dx, dz): 
    cond_parts_x = []
    cond_parts_z = []
    k = H.shape[0] - n
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

def decode_cond_gen_mul(H, n, N, rnd, dx, dz):
    dec_x = []
    dec_z = []
    k = H.shape[0] - n
    max_err_x = (dx - 1) // 2
    max_err_z = (dz - 1) // 2
    meas_corr_x = []
    meas_corr_z = []
    for m in range(rnd):
        dec_parts_x = []
        dec_parts_z = []
        for cnt in range(N):
            for i in range(n - k):
                posx = np.where(H[i, :n] == 1)[0]
                index = i + 1 + (m * N + cnt) * (n - k)
                if len(posx) > 0:
                    dec_parts_x.append(f"s_({index}) == ")
                    for j in posx:
                        dec_parts_x.append(f"cz_({j + 1 + (m * N + cnt) * n})")
                        dec_parts_x.append("@^")
                    if m > 0:
                        dec_parts_x.append(f"c_({index - N * (n-k)})")
                        meas_corr_x.append(index - N * (n-k))
                    else:
                        dec_parts_x.pop()
                    dec_parts_x.append("&&")
                posz = np.where(H[i, n:] == 1)[0]
                if len(posz) > 0:
                    dec_parts_z.append(f"s_({index}) == ")
                    for j in posz:
                        dec_parts_z.append(f"cx_({j + 1 + (m * N + cnt) * n})")
                        dec_parts_z.append("@^")
                    if m > 0:
                        dec_parts_z.append(f"c_({index - N * (n-k)})")
                        meas_corr_z.append(index - N * (n-k))
                    else:
                        dec_parts_z.pop()
                    dec_parts_z.append("&&")

            # dec_parts_x.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cz_(i)) <= Min(sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ez_(i)), {max_err_z})&&")
            # dec_parts_z.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cx_(i)) <= Min(sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ex_(i)), {max_err_x})&&")
            dec_parts_x.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cz_(i)) <= Min(sum i 1 {n} (pz_(i)) + sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ez_(i)), {max_err_z})&&")
            dec_parts_z.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cx_(i)) <= Min(sum i 1 {n} (px_(i)) + sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ex_(i)), {max_err_x})&&")
            
        dec_x.append(''.join(dec_parts_x))
        dec_z.append(''.join(dec_parts_z))
    
    
    return ''.join(dec_x)[:-2], ''.join(dec_z)[:-2], meas_corr_x, meas_corr_z
   


def stab_cond_gen_multiq(H, n, N):
    k = H.shape[0] - n  
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
def program_gen_qec(H, n, N):   
    k = H.shape[0] - n
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

def program_gen_qec_mul(H, n, N, rnd):
    prog_x, prog_z = [], []
    k = H.shape[0] - n
    for m in range(rnd):
        totq = N * n
        prog_parts_x = []
        prog_parts_z = []
        prog_parts_z.append(f"for i in {1} to {totq} do q_(i) *= ex_(i + {m * totq}) X end;")
        prog_parts_x.append(f"for i in {1} to {totq} do q_(i) *= ez_(i + {m * totq}) Z end;")
        for cnt in range(N):
            s_base = cnt * (n - k) + m * N * (n - k)
            q_base = cnt * n 
            ppx = []
            ppz = []
            for i in range(n - k):
                if (np.all(H[i,:n] == 0) == False):
                    # if m >= 1:
                        # ppx.append(f"s_({i + 1 + s_base}) := s_({i + 1 + s_base}) + e_({i + 1 + s_base});")
                    ppx.append(f"s_({i + 1 + s_base}) := meas")
                    for j in range(n):
                        if H[i][j] == 1:
                            ppx.append(f"(0,1,{j + 1 + q_base})")
                    ppx.append(";")
                if (np.all(H[i,n:] == 0) == False):
                    # if m >= 1:
                    #     ppz.append(f"s_({i + 1 + s_base}) := s_({i + 1 + s_base}) + e_({i + 1 + s_base});")
                    ppz.append(f"s_({i + 1 + s_base}) := meas")
                    for j in range(n):
                        if H[i][j + n] == 1:
                            ppz.append(f"(1,0,{j + 1 + q_base})")
                    ppz.append(";")

            prog_parts_x.append(''.join(ppx))
            prog_parts_z.append(''.join(ppz))
        
        prog_parts_z.append(f"for i in {1} to {totq} do q_(i) *= cx_(i + {m * totq}) X end")
        prog_parts_x.append(f"for i in {1} to {totq} do q_(i) *= cz_(i + {m * totq}) Z end")
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
    progx, progz = ';'.join(prog_x), ';'.join(prog_z)
    return progx, progz


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
                    q1 = (k - 1) * numq + i + 1
                    q2 = (l - 1) * numq + i + 1
                    prog_parts_log.append(f"q_({q1}), q_({q2}) *= CNOT")
            # elif code == '':
        elif gate == 'H':
            assert len(inds) == 1
            k = inds[0]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q = (k - 1) * numq + i + 1
                    prog_parts_log.append(f"q_({q}) *= H")
        elif gate == 'S':
            assert len(inds) == 1
            k = inds[0]
            for i in range(numq):
                q = (k - 1) * numq + i + 1
                prog_parts_log.append(f"q_({q}) *= Z")
                prog_parts_log.append(f"q_({q}) *= S")
    prog_log =  ';'.join(prog_parts_log)
    return prog_log
    
### Prog generation for logical ops with pre-introduced errors
def stab_cond_gen_log(matrix, N):
    n = matrix.shape[1] // 2
    k = matrix.shape[0] - n
    
    cond_parts_x = []
    cond_parts_z = []
    for cnt in range(N):
        s = cnt * n
        l = k * cnt
        for i in range(n - k):
            temp1 = [f"(0,1,{s + j + 1})" for j in range(n) if matrix[i][j] == 1]
            temp2 = [f"(1,0,{s + j + 1})" for j in range(n) if matrix[i][j + n] == 1]
            cond_parts_x.append(''.join(temp1 + temp2) + "&&")
            cond_parts_z.append(''.join(temp2 + temp1) + "&&")

        for i in range(k):
            tempx = f"(-1)^(b_({i + l + 1}))" + ''.join([f"(0,1,{s + j + 1})" for j in range(n) if matrix[n - k + i][j] == 1]) + ''.join([f"(1,0,{j + 1})" for j in range(n) if matrix[n - k + i][j + n] == 1])
            tempz = f"(-1)^(b_({i + l + 1}))" + ''.join([f"(1,0,{s + j + 1})" for j in range(n) if matrix[n + i][j + n] == 1]) + ''.join([f"(0,1,{j + 1})" for j in range(n) if matrix[n + i][j] == 1])
            cond_parts_x.append(tempx + "&&")
            cond_parts_z.append(tempz + "&&")

    return ''.join(cond_parts_x)[:-2], ''.join(cond_parts_z)[:-2]


def prog_gen_qec_rnd(H, n, N, rnd):
    prog_parts_z = []
    prog_parts_x = []
    # start = rnd * N * n 
    k = H.shape[0] - n
    spx = defaultdict(list)
    spz = defaultdict(list)
    for ind in range(N):
        qbase = n * ind
        sbase = (n - k) * ind
        for i in range(n - k):
            if (np.all(H[i,:n] == 0) == False):
                for j in range(n):
                    if H[i][j] == 1:
                        spx[i + sbase].append(f"(0,1,{j + 1 + qbase})")
            if (np.all(H[i,n:] == 0) == False):
                for j in range(n):
                    if H[i][j + n] == 1:
                        spz[i + sbase].append(f"(1,0,{j + 1 + qbase})")
    
    err_ind_start = rnd * N * n
    corr_ind_start = rnd * N * n
    meas_ind_start = rnd * N * (n-k)
    prog_parts_z.append(f"for i in 1 to {n * N} do q_(i) *= ex_(i + {err_ind_start}) X end;")
    prog_parts_x.append(f"for i in 1 to {n * N} do q_(i) *= ez_(i + {err_ind_start}) Z end;")
    for cnt, sinfo in spx.items():
        smeas_x = f"s_({cnt + 1 + meas_ind_start}) := meas" + ''.join(sinfo) + ";"
        prog_parts_x.append(smeas_x)
        prog_parts_z.append(smeas_x)
    for cnt, sinfo in spz.items():
        smeas_z = f"s_({cnt + 1 + meas_ind_start}) := meas" + ''.join(sinfo) + ";"
        prog_parts_x.append(smeas_z)
        prog_parts_z.append(smeas_z)
    prog_parts_z.append(f"for i in 1 to {n * N} do q_(i) *= cx_(i + {corr_ind_start}) X end")
    prog_parts_x.append(f"for i in 1 to {n * N} do q_(i) *= cz_(i + {corr_ind_start}) Z end")
    
    return ''.join(prog_parts_x), ''.join(prog_parts_z)

def program_gen_log_noerr(matrix, numq, N, gates, code):
    prog_parts = []
    for ind in range(len(gates)):
        prog_parts.append(program_gen_logic(matrix, numq, N, gates[ind], code))

    return ';'.join(prog_parts)

def program_gen_log_err(matrix, numq, N, gates, code):
    prog_parts_x = []
    prog_parts_z = []
    err_gt_x = []
    err_gt_z = []
    # print(len(gates))
    for ind, gateinfo in gates.items():
        
        prog_log = program_gen_logic(matrix, numq, N, gateinfo, code)
        
        totq = N * numq
        if ind >= 0:
            start = ind * totq
            prog_parts_z.append(f"for i in 1 to {numq} do q_(i) *= px_(i) X end")
            prog_parts_x.append(f"for i in 1 to {numq} do q_(i) *= pz_(i) Z end")
            err_gt_x.append(f"sum i 1 {numq} (pz_(i)) <= 1")
            err_gt_z.append(f"sum i 1 {numq} (px_(i)) <= 1")
        prog_parts_x.append(prog_log)
        prog_parts_z.append(prog_log)
        prog_qec_x, prog_qec_z = prog_gen_qec_rnd(matrix, numq, N, ind)
        prog_parts_z.append(prog_qec_z)
        prog_parts_x.append(prog_qec_x)
        
        # ppx.append(';'.join(prog_parts_x))
        # ppz.append(';'.join(prog_parts_z))

    return ';'.join(prog_parts_x), ';'.join(prog_parts_z), '&&'.join(err_gt_x), '&&'.join(err_gt_z)

if __name__ == "__main__":
    mat = surface_matrix_gen(3)
    gates = defaultdict(list)
    gates[0] = [['H', [1]], ['H', [2]]]
    gates[1] = [['CNOT', [1,2]]]
    # prog_x, prog_z = program_gen_log_err(mat, 9, 2, gates, 'surface')
    # prog_log = program_gen_log_noerr(mat, 9, 2, gates, 'surface')
    # print(prog_log)
    print(stab_cond_gen_log(mat))
    # Zmat = np.array([[1,1,0],[0,1,1],[0,0,1]])
    # mat = np.zeros((4, 6), dtype = int) 
    # mat[0:3,3:] = Zmat
    # _, prog_z_parts = program_gen_qec_mul(mat, 3, 1, 1, 2)

    # for i in range(len(prog_z_parts)):
    #     print(f"{i}-th meas:", prog_z_parts[i])
    
    # _, postcond_z = stab_cond_gen_multiq(mat, 3, 1, 1)
    # precond_z = postcond_z
    # print("precond_z: ", precond_z)

    # pre_tree, program_tree, post_tree1 = precond_generator(prog_z_parts[1], precond_z, postcond_z) 
    # postcond_z1 = re.sub( r'\s*_\s*', '_', Reconstructor(parser = get_parser()).reconstruct(post_tree1.children[0].children[-1]))
    # print("postcond_z1: ", postcond_z1)
    # pre_tree, program_tree, post_tree2 = precond_generator(prog_z_parts[0], precond_z, postcond_z1) 
    # postcond_z2 = re.sub( r'\s*_\s*', '_', Reconstructor(parser = get_parser()).reconstruct(post_tree2.children[0].children[-1]))
    # print("postcond_z2: ", postcond_z2)
    # cass_transformer = qassertion2c(post_tree1)
    # cass_tree = cass_transformer.transform(post_tree2.children[0].children[-1])
    # cass_tree = simplifyeq().transform(cass_tree)
    # print("formula:", tree_to_z3(cass_tree, {}, 1, [], False))
