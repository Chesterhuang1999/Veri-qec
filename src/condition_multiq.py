#----------#
# Developer: Chester Huang
# Date: 2024/10/20
# Description: Here is a condition generation for logical operations 
# which perform on multiple logical qubits.
#----------#

import numpy as np
import time
import math
from collections import defaultdict

import re
from Dataset import special_codes
##
from encoder import *
### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   



### Condition and program generation from check matrix, 
# only support single round measurement ###
def decode_cond_gen(H, n, N, dx, dz): 
    cond_parts_x = []
    cond_parts_z = []
    k = H.shape[0] - n
    max_err_x = int((dx - 1) // 2)
    max_err_z = int((dz - 1) // 2)
    
    for cnt in range(N): 
        cpx = []
        cpz = []
        ## Stabilizers' syndrome must be erased
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
        ## decoder's condition
        cpx.append(f"sum i {1 + cnt * n} {n + cnt * n} (cz_(i)) <= Min(sum i {1 + cnt *n} {n + cnt*n} (ez_(i)), {max_err_z})")
        cpz.append(f"sum i {1 + cnt * n} {n + cnt * n} (cx_(i)) <= Min(sum i {1 + cnt *n} {n + cnt*n} (ex_(i)), {max_err_x})")
        cond_parts_x.append(''.join(cpx))
        cond_parts_z.append(''.join(cpz))
    return '&&'.join(cond_parts_x), '&&'.join(cond_parts_z)

### A more general case ### 
### Condition and program generation from check matrix, 
# support multiple rounds measurement and propagation error ###
def decode_cond_gen_mul(H, n, N, rnd, dx, dz, isprop):
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
            ## Judging whether propagation error exists in the setting ##
            if isprop == True:
                dec_parts_x.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cz_(i)) <= Min(sum i 1 {n + (m * N + cnt) * n} (pz_(i)) + sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ez_(i)), {max_err_z})&&")
                dec_parts_z.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cx_(i)) <= Min(sum i 1 {n + (m * N + cnt) * n} (px_(i)) + sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ex_(i)), {max_err_x})&&")
            else:
                ### The counts of corrections must not exceed the number of errors ###
                # To meet the requirement of minimum weight #.
                dec_parts_x.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cz_(i)) <= Min(sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ez_(i)), {max_err_z})&&")
                dec_parts_z.append(f"sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (cx_(i)) <= Min(sum i {1 + (m * N + cnt) * n} {n + (m * N + cnt) * n} (ex_(i)), {max_err_x})&&")
        dec_x.append(''.join(dec_parts_x))
        dec_z.append(''.join(dec_parts_z))
    
    
    return ''.join(dec_x)[:-2], ''.join(dec_z)[:-2], meas_corr_x, meas_corr_z
   
### Pre/post-condition generation, support multiple logical qubits ###   
def stab_cond_gen_multiq(H, n, N):
    k = H.shape[0] - n  
    cond_parts_x = []
    cond_parts_z = []
    for cnt in range(N):
        cpx, cpz = [], []
        ## Stabilizers
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
        ## Logical operators
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

### Generation of error correction programs, support multiple logical qubits ### 
def program_gen_qec(H, n, N):   
    k = H.shape[0] - n
    prog_parts_x = []
    prog_parts_z = []
    ## Error injection 
    prog_parts_z.append(f"for i in 1 to {n} do q_(i) *= ex_(i) X end;")
    prog_parts_x.append(f"for i in 1 to {n} do q_(i) *= ez_(i) Z end;")
    for cnt in range(N):
        ppx = []
        ppz = []
        ## stabilizers
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
    ## Error correction
    prog_parts_z.append(f"for i in 1 to {n} do q_(i) *= cx_(i) X end")
    prog_parts_x.append(f"for i in 1 to {n} do q_(i) *= cz_(i) Z end")
    return ''.join(prog_parts_x), ''.join(prog_parts_z)

### Generation of error correction programs, with possible multiple rounds of measurement ### 
def program_gen_qec_mul(H, n, N, rnd):
    prog_x, prog_z = [], []
    k = H.shape[0] - n
    for m in range(rnd):
        totq = N * n
        prog_parts_x = []
        prog_parts_z = []

        ## Error injection program
        prog_parts_z.append(f"for i in {1} to {totq} do q_(i) *= ex_(i + {m * totq}) X end;")
        prog_parts_x.append(f"for i in {1} to {totq} do q_(i) *= ez_(i + {m * totq}) Z end;")
        for cnt in range(N):
            s_base = cnt * (n - k) + m * N * (n - k)
            q_base = cnt * n 
            ppx = []
            ppz = []

            ## Measuring stabilizers
            for i in range(n - k):
                if (np.all(H[i,:n] == 0) == False):
                    
                    ppx.append(f"s_({i + 1 + s_base}) := meas")
                    for j in range(n):
                        if H[i][j] == 1:
                            ppx.append(f"(0,1,{j + 1 + q_base})")
                    ppx.append(";")
                if (np.all(H[i,n:] == 0) == False):
                    
                    ppz.append(f"s_({i + 1 + s_base}) := meas")
                    for j in range(n):
                        if H[i][j + n] == 1:
                            ppz.append(f"(1,0,{j + 1 + q_base})")
                    ppz.append(";")

            prog_parts_x.append(''.join(ppx))
            prog_parts_z.append(''.join(ppz))

        ## Correction program ##
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
## Repetition code
def rep_cond(n, k): ## n: num of physical qubits, k: num of logical qubits
    
    cond = ""
    for i in range(1, n):
        cond = cond + f"(1,0,{i})" + f"(1,0,{i+1})&&"
    cond = cond + f"(-1)^(b_(1))(1,0,1)"
    
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
                ## Transversal CNOT
                for i in range(numq):
                    q1 = (k - 1) * numq + i + 1
                    q2 = (l - 1) * numq + i + 1
                    prog_parts_log.append(f"q_({q1}), q_({q2}) *= CNOT")
            
        elif gate == 'H':
            ## Transversal Hadamard
            assert len(inds) == 1
            k = inds[0]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q = (k - 1) * numq + i + 1
                    prog_parts_log.append(f"q_({q}) *= H")
        elif gate == 'S':
            ## Transversal S (phase) gate (for steane only)
            assert len(inds) == 1
            k = inds[0]
            for i in range(numq):
                q = (k - 1) * numq + i + 1
                prog_parts_log.append(f"q_({q}) *= Z")
                prog_parts_log.append(f"q_({q}) *= S")
    prog_log =  ';'.join(prog_parts_log)
    return prog_log
    
### Pre/post-condtion generation for logical operation ###
def stab_cond_gen_log(matrix, N):
    n = matrix.shape[1] // 2
    k = matrix.shape[0] - n
    
    cond_parts_x = []
    cond_parts_z = []
    for cnt in range(N):
        s = cnt * n
        l = k * cnt
        ## Stabilizers
        for i in range(n - k):
            temp1 = [f"(0,1,{s + j + 1})" for j in range(n) if matrix[i][j] == 1]
            temp2 = [f"(1,0,{s + j + 1})" for j in range(n) if matrix[i][j + n] == 1]
            cond_parts_x.append(''.join(temp1 + temp2) + "&&")
            cond_parts_z.append(''.join(temp2 + temp1) + "&&")
        ## Logical operators
        for i in range(k):
            tempx = f"(-1)^(b_({i + l + 1}))" + ''.join([f"(0,1,{s + j + 1})" for j in range(n) if matrix[n - k + i][j] == 1]) + ''.join([f"(1,0,{j + 1})" for j in range(n) if matrix[n - k + i][j + n] == 1])
            tempz = f"(-1)^(b_({i + l + 1}))" + ''.join([f"(1,0,{s + j + 1})" for j in range(n) if matrix[n + i][j + n] == 1]) + ''.join([f"(0,1,{j + 1})" for j in range(n) if matrix[n + i][j] == 1])
            cond_parts_x.append(tempx + "&&")
            cond_parts_z.append(tempz + "&&")

    return ''.join(cond_parts_x)[:-2], ''.join(cond_parts_z)[:-2]

### Program generation, multi logical qubits, multi measurement rounds, no propagation error ###
def prog_gen_qec_rnd(H, n, N, rnd):
    prog_parts_z = []
    prog_parts_x = []
    # start = rnd * N * n 
    k = H.shape[0] - n
    spx = defaultdict(list)
    spz = defaultdict(list)
    ## Rnds
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
    ### Error injection in each physical qubits
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

## Error-free logical programs ## 
def program_gen_log_noerr(matrix, numq, N, gates, code):
    prog_parts = []
    for ind in range(len(gates)):
        prog_parts.append(program_gen_logic(matrix, numq, N, gates[ind], code))

    return ';'.join(prog_parts)

### Logical operations programs with errors ### 
def program_gen_log_err(matrix, numq, N, gates, code):
    prog_parts_x = []
    prog_parts_z = []
    err_gt_x = []
    err_gt_z = []
    
    for ind, gateinfo in gates.items():
        
        prog_log = program_gen_logic(matrix, numq, N, gateinfo, code)
        
        totq = N * numq
        if ind >= 0:
            start = ind * totq
            ## Propagated error
            prog_parts_z.append(f"for i in 1 to {totq} do q_(i) *= px_(i) X end")
            prog_parts_x.append(f"for i in 1 to {totq} do q_(i) *= pz_(i) Z end")
            err_gt_x.append(f"sum i 1 {totq} (pz_(i)) <= 1")
            err_gt_z.append(f"sum i 1 {totq} (px_(i)) <= 1")
        prog_parts_x.append(prog_log)
        prog_parts_z.append(prog_log)
        ## Generate error correction program
        prog_qec_x, prog_qec_z = prog_gen_qec_rnd(matrix, numq, N, ind)
        prog_parts_z.append(prog_qec_z)
        prog_parts_x.append(prog_qec_x)
        
    return ';'.join(prog_parts_x), ';'.join(prog_parts_z), '&&'.join(err_gt_x), '&&'.join(err_gt_z)


