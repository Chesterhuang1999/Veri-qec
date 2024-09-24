import numpy as np
import time
import math
from collections import defaultdict
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
        cpx.pop()
        cpz.pop()
        cond_parts_x.append(''.join(cpx))
        cond_parts_z.append(''.join(cpz))
    return '&&'.join(cond_parts_x), '&&'.join(cond_parts_z)

### Generation of error correction programs ### 
def program_gen_qec(H, n, k, N):   
    prog_parts_x = []
    prog_parts_z = []
    prog_parts_z.append(f"for i in 1 to {n} do q_(i) *= ex_(i) X end")
    prog_parts_x.append(f"for i in 1 to {n} do q_(i) *= ez_(i) Z end")
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
DJ = defaultdict(list)
DJ[1] = [['H', [1]], ['H',[2]], ['H', [3]]]
DJ[2] = [['CNOT', [1,2]], ['CNOT', [1,3]]]
DJ[3] = [['H', [1]], ['H',[2]]]

CNOT = [['CNOT',[1,2]]]
def program_gen_logic(matrix, numq, N, gateinfo, code):
    prog_parts_log = []
    prog_parts_x, prog_parts_z = [], []
    
    for i in range(len(gateinfo)):
        gate, inds = gateinfo[i]
        if gate == 'CNOT':
            assert len(inds[i]) == 2
            k, l = inds[i]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q1 = (k - 1) * numq + i
                    q2 = (l - 1) * numq + i
                    prog_parts_log.append(f"q_({q1}), q_{(q2)} *= CNOT")
            # elif code == '':
            #     for i in range(numq):
        elif gate == 'H':
            assert len(inds) == 1
            k = inds[0]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q = (k - 1) * numq + i
                    prog_parts_log.append(f"q_({q}) *= H")
    prog_log =  ';'.join(prog_parts_log)
    return prog_log
    

mat = surface_matrix_gen(3)
print(stab_cond_gen_multiq(mat, 9, 1, 2))