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
        
    # if alts == 'verify':
    #     cond_parts_x.append(f"sum i 1 {n} (cz_(i)) <= Min(sum i 1 {n} (ez_(i)), {max_err_z})")
    #     cond_parts_z.append(f"sum i 1 {n} (cx_(i)) <= Min(sum i 1 {n} (ex_(i)), {max_err_x})")
    # elif alts == 'test':
    #     cond_parts_x.append(f"sum i 1 {n} (cz_(i)) <= sum i 1 {n} (ez_(i))")
    #     cond_parts_z.append(f"sum i 1 {n} (cx_(i)) <= sum i 1 {n} (ex_(i))")
    if alts == 'test-opt':
        return ''.join(cond_parts_x)[:-2], ''.join(cond_parts_z)[: -2]
    
    cond_parts_x.append(f"sum i 1 {n} (cz_(i)) <= Min(sum i 1 {n} (ez_(i)), {max_err_z})")
    cond_parts_z.append(f"sum i 1 {n} (cx_(i)) <= Min(sum i 1 {n} (ex_(i)), {max_err_x})")
    return ''.join(cond_parts_x), ''.join(cond_parts_z)
    
    #cond_parts_x.append(f"sum i 1 {n} (cz_(i)) <= sum i 1 {n} (ez_(i))")
    #cond_parts_z.append(f"sum i 1 {n} (cx_(i)) <= sum i 1 {n} (ex_(i))")
    # return '&&'.join(cond_parts_x), '&&'.join(cond_parts_z)
    # cond_x = ''.join(cond_parts_x)
    # cond_z = ''.join(cond_parts_z)
    # return cond_x[:-2], cond_z[:-2]
    
def stab_cond_gen(H, n, k):
    cond_parts_x = []
    cond_parts_z = []
    for i in range(2 * k):
       
        if np.all(H[n - k + i, :n] == 0) == False:
            # cond_parts_x.append(f"(-1)^(b_({i + 1}))")

            for j in range(n):
                if H[n - k + i][j] == 1:
                    cond_parts_x.extend(f"(0,1,{j + 1})")
            cond_parts_x.append("&&")
        if np.all(H[n - k + i, n:] == 0) == False:
            # cond_parts_z.append(f"(-1)^(b_({i + 1}))")
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
    # for i in range(2 * k):
       
    #     if np.all(H[n - k + i, :n] == 0) == False:
    #         cond_parts_x.append(f"(-1)^(b_({i + 1}))")

    #         for j in range(n):
    #             if H[n - k + i][j] == 1:
    #                 cond_parts_x.extend(f"(0,1,{j + 1})")
    #         cond_parts_x.append("&&")
    #     if np.all(H[n - k + i, n:] == 0) == False:
    #         cond_parts_z.append(f"(-1)^(b_({i + 1}))")
    #         for j in range(n):
    #             if H[n - k + i][j + n] == 1:
    #                 cond_parts_z.extend(f"(1,0,{j + 1})")
    #         cond_parts_z.append("&&")
    
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
    for i in range(numq - 1):
        prog_parts_x = []
    return prog_log
    
mat = surface_matrix_gen(3)
# print(program_gen_logical(mat, 9, 2, H, 'surface'))


##### Example: condition generation for surface code (deprecated) #####
# def surface_program(n, x_inds, z_inds):
#     prog_parts = []
#     prog_parts.append(f"for i in 1 to {pow(n, 2)} do q_(i) *= ex_(i) X end; for i in 1 to {pow(n, 2)} do q_(i) *= ez_(i) Z end; ")
#     i = 0
#     for pos in z_inds.values():
#         i += 1
#         prog_parts.append(f"sz_({i}) := meas" + ''.join([f"(1,0,{p})" for p in pos]) + "; ")
#     i = 0
#     for pos in x_inds.values():
#         i += 1
#         prog_parts.append(f"sx_({i}) := meas" + ''.join([f"(0,1,{p})" for p in pos]) + "; ")
#     prog_parts.append(f"for i in 1 to {pow(n, 2)} do q_(i) *= cx_(i) X end; for i in 1 to {pow(n, 2)} do q_(i) *= cz_(i) Z end")
#     program = ''.join(prog_parts)
#     return program
# def sur_cond_gen(x_inds, z_inds, mod):
#     cond_parts = []
#     for pos in z_inds.values():
#         cond_parts.extend([f"(1,0,{p})" for p in pos])
#         cond_parts.append("&&")
#     for pos in x_inds.values():
#         cond_parts.extend([f"(0,1,{p})" for p in pos])
#         cond_parts.append("&&")
#     cond_parts.append(f"(-1)^(b_(1))")
#     if mod == 'z':
#         for i in range(n):
#             cond_parts.extend(f"(1,0,{i + 1})")
#     else:
#         for i in range(n):
#             cond_parts.extend(f"(0,1,{i * n + 1})")
#     return ''.join(cond_parts)
# def sur_decode_gen(x_inds, z_inds):
#     dec_parts = []
#     num_qubits = len(x_inds) + len(z_inds) + 1 
#     max_err = (int(math.sqrt(num_qubits)) - 1) // 2
#     i = 0
#     for pos in z_inds.values():
#         i += 1
#         dec_parts.append(f"sz_({i}) == ")
#         dec_parts.extend([f"cx_({p})@^" for p in pos[:-1]])
#         dec_parts.extend(f"cx_({pos[-1]})") 
#         dec_parts.append("&&")
#     i = 0
#     for pos in x_inds.values():
#         i += 1
#         dec_parts.append(f"sx_({i}) == ")
#         dec_parts.extend([f"cz_({p})@^" for p in pos[:-1]])
#         dec_parts.extend(f"cz_({pos[-1]})") 
#         dec_parts.append("&&")
#     dec_parts.append(f"sum i 1 {num_qubits} (cz_(i)) <= Min(sum i 1 {num_qubits} (ez_(i)), {max_err}) && sum i 1 {num_qubits} (cx_(i)) <= Min(sum i 1 {num_qubits} (ex_(i)), {max_err})")
#     return ''.join(dec_parts)
# def surface(n, k): ## n is the subspace of 
#     t = n // 2 + 1
#     x_inds = defaultdict(list)
#     z_inds = defaultdict(list)
#     for i in range(1, t):
#         i2 = 2 * i
#         for j in range(1, t):
#             j2 = 2 * j
#             topl_od_z = (i2 - 2) * n + (j2 - 1)
#             topl_ev_z = (i2 - 1) * n + (j2)
#             topl_od_x = (i2 - 2) * n + (j2)
#             topl_ev_x = (i2 - 1) * n + (j2 - 1)
#             for k in [topl_od_z, topl_ev_z]:
#                 z_inds[k] = [k, k + 1, k + n, k + n + 1] 
#             for k in [topl_od_x, topl_ev_x]:
#                 x_inds[k] = [k, k + 1, k + n, k + n + 1]  
#         z_inds[i2] = [i2, i2 + 1]
#         temp = n * (n - 1) + i2 - 1
#         z_inds[temp] = [temp, temp + 1] 
#         l = (i2 - 2) * n + 1    
#         x_inds[l] = [l, l + n]
#         x_inds[i2 * n] = [i2 * n, i2 * n + n]

#     # for i in range(1, t):
#     #     for j in range(1, t):
          
#     #         for k in [topl_odd, topl_even]:
#     #             x_inds[k] = [k, k + 1, k + n, k + n + 1]
#     cond1 = sur_cond_gen(x_inds, z_inds,'z')
#     cond2 = sur_cond_gen(z_inds, x_inds,'x')
    
#     return cond1, cond2,  x_inds, z_inds

# n = 5
# k = 1
# ### generate the Hoare triple for given code, with 2 precondition needs to be verified ### 
# def triple_gen(model, n, k):
#     if model == 'repetition':
#         return rep_program(n)
#     elif model == 'surface':
#         cond1, cond2, x_inds, z_inds = surface(n, k)
#         return cond1, cond2, surface_program(n, x_inds, z_inds)
#     else:
#         return None

# # cond1, cond2, surf_prog = triple_gen('surface', n, k)

# # #print(cond1)

# #print(decode_cond_gen(H, 3, 1))
