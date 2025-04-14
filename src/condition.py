import numpy as np
import time
import math
from collections import defaultdict

### Notes: postscript z: z-stabilizers, z measurement, x error and corrections; 
# postscript x: x-stabilizers, x measurement, z error and corrections   
### Condition and program generation from check matrix ###
def decode_cond_gen(H, n, k, dx, dz, alts = 'verify'):
    cond_parts_x = []
    cond_parts_z = []
    max_err_x = int((dx - 1) // 2)
    max_err_z = int((dz - 1) // 2)
    for i in range(n - k):
        if np.all(H[i, :n] == 0) == False:
            cond_parts_x.extend(f"s_({i + 1}) == ")
            for j in range(n):
                if H[i][j] == 1 :
                    cond_parts_x.extend(f"cz_({j + 1})")
                    cond_parts_x.append("@^")
            cond_parts_x.pop()
            cond_parts_x.append("&&")
        if np.all(H[i, n:] == 0) == False:
            cond_parts_z.extend(f"s_({i + 1}) == ")
            for j in range(n):
                if H[i][j + n] == 1:
                    cond_parts_z.extend(f"cx_({j + 1})")
                    cond_parts_z.append("@^")
            cond_parts_z.pop()
            cond_parts_z.append("&&")
        
   
    if alts == 'test-opt':
        return ''.join(cond_parts_x)[:-2], ''.join(cond_parts_z)[: -2]
    
    cond_parts_x.append(f"sum i 1 {n} (cz_(i)) <= Min(sum i 1 {n} (ez_(i)), {max_err_z})")
    cond_parts_z.append(f"sum i 1 {n} (cx_(i)) <= Min(sum i 1 {n} (ex_(i)), {max_err_x})")
    return ''.join(cond_parts_x), ''.join(cond_parts_z)
    
    
    
def stab_cond_gen(H, n, k):
    cond_parts_x = []
    cond_parts_z = []
    for i in range(2 * k):
       
        if np.all(H[n - k + i, :n] == 0) == False:
            

            for j in range(n):
                if H[n - k + i][j] == 1:
                    cond_parts_x.extend(f"(0,1,{j + 1})")
            cond_parts_x.append("&&")
        if np.all(H[n - k + i, n:] == 0) == False:
            
            for j in range(n):
                if H[n - k + i][j + n] == 1:
                    cond_parts_z.extend(f"(1,0,{j + 1})")
            cond_parts_z.append("&&")
    for i in range(n - k):
        hasx, hasz = False, False
        for j in range(n):
            if H[i][j] == 1:
                cond_parts_x.extend(f"(0,1,{j + 1})")
                hasx = True
            if H[i][j + n] == 1:
                cond_parts_z.extend(f"(1,0,{j + 1})")
                hasz = True
        if hasx == True:
            cond_parts_x.append("&&")
        if hasz == True:
            cond_parts_z.append("&&")
    
    
    cond_parts_x.pop()
    cond_parts_z.pop()
    return ''.join(cond_parts_x), ''.join(cond_parts_z)

def program_gen(H, n, k):   
    prog_parts_x = []
    prog_parts_z = []
    prog_parts_z.append(f"for i in 1 to {n} do q_(i) *= ex_(i) X end; ")
    prog_parts_x.append(f"for i in 1 to {n} do q_(i) *= ez_(i) Z end; ")
    for i in range(n - k):
        if (np.all(H[i,:n] == 0) == False):
            prog_parts_x.append(f"s_({i + 1}) := meas")
            for j in range(n):
                if H[i][j] == 1:
                    prog_parts_x.append(f"(0,1,{j + 1})")
            prog_parts_x.append("; ")
        if (np.all(H[i,n:] == 0) == False):
            prog_parts_z.append(f"s_({i + 1}) := meas")
            for j in range(n):
                if H[i][j + n] == 1:
                    prog_parts_z.append(f"(1,0,{j + 1})")
            prog_parts_z.append(";")
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
H = [['H', [1]]]
CNOT = [['CNOT',[1,2]]]
def program_gen_logical(matrix, numq, N, gateinfo, code):
    prog_parts_log = []
    prog_parts_x, prog_parts_z = [], []
    
    for i in range(len(gateinfo)):
        gate, inds = gateinfo[i]
        print(gate, inds)
        if gate == 'CNOT':
            assert len(inds[i]) == 2
            k, l = inds[i]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q1 = (k - 1) * numq + i
                    q2 = (l - 1) * numq + i
                    prog_parts_log.append(f"q_({q1}), q_{(q2)} *= CNOT")
            
        elif gate == 'H':
            assert len(inds) == 1
            k = inds[0]
            if code in ('surface', 'steane'):
                for i in range(numq):
                    q = (k - 1) * numq + i
                    prog_parts_log.append(f"q_({q}) *= H")
    prog_log =  ';'.join(prog_parts_log)
    for i in range(numq - 1):
        prog_parts_x = []
    return prog_log
    

