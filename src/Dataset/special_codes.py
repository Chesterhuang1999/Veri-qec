
import numpy as np
from scipy.linalg import lu
from scipy.sparse import csc_matrix, block_diag, kron, eye
import math
import galois
# import time
from collections import defaultdict

# from .linalg_GF import *
from Dataset.linalg_GF import *
##### Stabilizer code check matrix generation #####

## Steane code
def stabs_steane():
    n = 7
    k = 1
    matrix = np.zeros((n - k, 2*n), dtype = int) 
    css_1 = np.array([[1, 0, 1, 0, 1, 0, 1],[0, 1, 1, 0, 0, 1, 1],[0, 0, 0, 1, 1, 1, 1]])
    matrix[0:3, 0:n] = css_1    
    matrix[3:, n:] = css_1
    stabs = np.zeros((n+1, 2*n), dtype = int)

    # x_stabs = np.zeros((n, 2*n), dtype = int)
    # z_stabs = np.zeros((n, 2*n), dtype = int)
    # x_stabs[0:n, :] = matrix
    # z_stabs[0:n, :] = matrix
    logs = np.array([[1, 1, 1, 1, 1, 1, 1]])
    stabs[0:n - 1, :] = matrix
    stabs[n - 1, 0:n] = logs
    stabs[n, n:] = logs
    # x_stabs[n, 0:n] = logs
    # z_stabs[n, n:] = logs
    return stabs

## [[2^r, 2^r - r- 2, 3]] Goettsman code
def stabs_goettsman(m):
    n = int(math.pow(2, m))
    k = n - m - 2
    d = 3
    matrix = np.zeros((n - k, 2*n), dtype = int)
    # x_stabs_matrix = np.zeros((n, 2*n), dtype = int) 
    # z_stabs_matrix = np.zeros((n, 2*n), dtype = int)
    # stabs_matrix = np.zeros((n + k, 2*n), dtype = int)
    for i in range(n):
        matrix[0][i] = 1
        matrix[1][i + n] = 1
        temp = i
        for j in range(2, m + 2):
            matrix[m + 3 - j][i + n] = temp % 2
            temp = temp // 2
            if temp == 0:
                break
    
    for j in range(2, m + 2):
        for i in range(n):
            temp = i // 2
            comp = i % 2
            binary_str = format(temp, f'0{m}b')
            #print(binary_str)
            bit_pos = j - 2 
            if bit_pos < m:
                bit_value = int(binary_str[bit_pos])
            
                if comp == 0:
                    matrix[j][i] = bit_value
                else:
                    matrix[j][i] = 1 - bit_value
            else:
                matrix[j][i] = 0

    matrix[[1, m+1]] = matrix[[m+1, 1]]
    rank = np.linalg.matrix_rank(matrix[:, :n])
    matrix = stab_matrix_transformation(matrix, n)
    logs_Z, logs_X = logical_op_gen(matrix, rank, n, k)
    stabs_matrix = np.concatenate((matrix, logs_X, logs_Z), axis = 0)
    # stabs_matrix[0:n - k, :] = matrix
    # stabs_matrix[n - k:n, 0:n] = logs_X
    # stabs_matrix[n:n + k, n:] = logs_Z
    # x_stabs_matrix, z_stabs_matrix = stab_matrix_transformation(matrix, rank, n, k, d)
    # return x_stabs_matrix, z_stabs_matrix
    return stabs_matrix
## [[6, 1, 3]] stabilizer code
def stabs_613():
    matrix = np.zeros((5,12), dtype = int)
    matrix[0] = [1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1]
    matrix[1] = [0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1]
    matrix[2] = [0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0]
    matrix[3] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]
    matrix[4] = [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0]

    # x_stabs_mat = np.zeros((6, 12), dtype = int)    
    # z_stabs_mat = np.zeros((6, 12), dtype = int)
    # x_stabs_mat[0:5, :] = matrix
    # z_stabs_mat[0:5, :] = matrix
    stabs_mat = np.zeros((7, 12), dtype = int)
    # x_stabs_mat[5] = [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]
    # z_stabs_mat[5] = [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1]
    stabs_mat[0:5, :] = matrix
    stabs_mat[5] = [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]
    stabs_mat[6] = [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1]
    return stabs_mat
## [[11, 1, 5]] stabilizer code
def stabs_1115():
    matrix = np.zeros((10, 22), dtype = int)
    z_nonz = defaultdict(list)
    x_nonz = defaultdict(list)
    z_nonz[0] = [0, 1, 2, 3, 4, 5]
    z_nonz[1] = []
    z_nonz[2] = [3, 5, 6, 7, 8, 10]
    z_nonz[3] = [4, 5, 6, 7, 8, 10]
    z_nonz[4] = [0, 1, 6, 7]
    z_nonz[5] = [1, 2, 7, 8]
    z_nonz[6] = [3, 4, 7, 8]
    z_nonz[7] = [4, 5, 6, 8]
    z_nonz[8] = [0, 2, 6, 7, 8, 10]
    z_nonz[9] = [0, 1, 6, 7, 8, 9]
    x_nonz[0] = []
    x_nonz[1] = [0, 1, 2, 3, 4, 5]
    x_nonz[2] = [4, 5, 6, 7, 8, 9]
    x_nonz[3] = [3, 4, 9, 10]
    x_nonz[4] = [1, 2, 7, 8]
    x_nonz[5] = [0, 2, 6, 8]
    x_nonz[6] = [4, 5, 6 ,7]
    x_nonz[7] = [3, 5, 7, 8]
    x_nonz[8] = [1,2, 9, 10]
    x_nonz[9] = [0, 2, 6, 7, 8, 9]
    for i in range(10):
        for j in z_nonz[i]:
            matrix[i][11 + j] = 1
        for j in x_nonz[i]:
            matrix[i][j] = 1
    
    # x_stabs_mat = np.zeros((11, 22), dtype = int) 
    # z_stabs_mat = np.zeros((11, 22), dtype = int)
    # x_stabs_mat[0:10, :] = matrix
    # z_stabs_mat[0:10, :] = matrix
    stabs = np.zeros((12, 22), dtype = int)
    stabs[0:10, :] = matrix

    for i in range(6, 11):
        # x_stabs_mat[10, i] = 1
        # z_stabs_mat[10, i + 11] = 1
        stabs[10, i] = 1    
        stabs[11, i + 11] = 1
    return stabs

## Brown-Fawzi random circuit code
def Brown_Fawzi(n, k, d):
    pass


## [[2^r-1, 1, 3]] Reed-Muller code

def stabs_Reed_Muller(m):
    n = int(math.pow(2, m)) - 1
    # Generate classical RM(1,m)
    gen_c1 = np.array([[1, 1], [0, 1]])
    matrix = np.zeros((n - 1, 2* n), dtype = int)
    x_stabs_mat = np.zeros((n, 2* n), dtype = int)
    z_stabs_mat = np.zeros((n, 2* n), dtype = int)

    i = 2
    while(i <= m):
        col = int(math.pow(2, i - 1))
        temp_mat = np.zeros((i + 1, 2 * col), dtype = int)
        temp_mat[:i,:col] = gen_c1
        temp_mat[:i,col:] = gen_c1
        temp_mat[-1,col:] = np.ones((1, col), dtype = int)
        gen_c1 = temp_mat
        i += 1 
    classical_RM = gen_c1
    # print(classical_RM)
    gf = galois.GF(2)
    gen_c1_gf = gen_c1.view(gf)
    #print(isinstance(gen_c1_gf, galois.FieldArray))
    gen_c2_gf = gen_c1_gf.null_space()
    gen_c2 = gen_c2_gf.view(np.ndarray)
    
    gen_c1 = gen_c1[1:, 1:]
    gen_c2 = gen_c2[1:, 1:]

    matrix[0:m, 0:n] = gen_c1
    matrix[m:, n:] = gen_c2
    x_stabs_mat[:n - 1, :] = matrix
    z_stabs_mat[:n - 1, :] = matrix
    rank = np.linalg.matrix_rank(matrix[:, :n])
    # matrix = stab_matrix_transformation(matrix, n)

    stabs_mat = np.zeros((n + 1, 2*n), dtype = int)
    stabs_mat[0:n - 1, :] = matrix
    stabs_mat[n - 1, 0:n] = np.ones((1, n), dtype = int)
    stabs_mat[n, n:] = np.ones((1, n), dtype = int)
    # x_stabs_mat[n - 1, 0:n] = np.ones((1, n), dtype = int)
    # z_stabs_mat[n - 1, n:] = np.ones((1, n), dtype = int)
    
    

    # return classical_RM, x_stabs_mat, z_stabs_mat
    return stabs_mat

#RM, X, Z = stabs_Reed_Muller(3)

# XZZX twisted surface code

def stabs_XZZX(dx, dz):
    numq = dx * dz
    stabs = np.zeros((numq + 1, 2 * numq), dtype = int)
    cnt = 0
    for i in range(dx - 1):
        for j in range(dz - 1):
            base = i * dz + j
            stabs[cnt][base] = 1
            stabs[cnt][base + 1 + numq] = 1
            stabs[cnt][base + dz + numq] = 1
            stabs[cnt][base + dz + 1] = 1
            cnt += 1
    ex_max = (dx - 1) // 2
    ez_max = (dz - 1) // 2
    for i in range(ez_max):
        stabs[cnt][2 * i + 1 + numq] = 1
        stabs[cnt][2 * i + 2] = 1
        cnt += 1
        bottom = (dx - 1) * dz
        stabs[cnt][bottom + 2 * i] = 1
        stabs[cnt][bottom + 2 * i+ 1 + numq] = 1
        cnt += 1
    for i in range(ex_max):
        stabs[cnt][2 * i * dz + numq] = 1
        stabs[cnt][(2 * i + 1) * dz] = 1
        cnt += 1
        stabs[cnt][(dz - 1) + (2 * i + 1) * dz] = 1
        stabs[cnt][(dz - 1) + (2 * i + 2) * dz + numq] = 1
        cnt += 1
    
    for i in range(dz):
        if i % 2 == 0:
            stabs[cnt][i] = 1
        else:
            stabs[cnt][i + numq] = 1
    
    cnt += 1
    
    for i in range(dx):
        if i % 2 == 0:
            stabs[cnt][i * dz + numq] = 1
        else:
            stabs[cnt][i * dz] = 1

    return stabs
        
### Stabilizers that detect single qubit errors

## 3D [[8,3,2]] color code, minimum 
def stabs_832code():
    matrix = np.zeros((11, 16), dtype = int)
    matrix[0,:8] = np.ones((1, 8), dtype = int)
    matrix[1,8:] = [1,1,1,1,0,0,0,0]
    matrix[2,8:] = [1,1,0,0,1,1,0,0]
    matrix[3,8:] = [1,0,1,0,1,0,1,0]
    matrix[4,8:] = [0,0,0,0,1,1,1,1]
    matrix[5,:8] = [1,1,1,1,0,0,0,0]
    matrix[6,:8] = [1,1,0,0,1,1,0,0]
    matrix[7,:8] = [1,0,1,0,1,0,1,0]
    matrix[8,8:] = [1,0,0,0,1,0,0,0]
    matrix[9,8:] = [1,0,1,0,0,0,0,0]
    matrix[10,8:] = [1,1,0,0,0,0,0,0]

    return matrix

## [[3k+8, k, 2]] triorthogonal code
def stabs_triotho(k):
    assert k % 2 == 0
    M = np.array([[1,1,1,1],
                  [1,1,1,1]])
    N = np.array([[1,1,1,0,0,0],
                  [0,0,0,1,1,1]])
    U = np.array([[0,1,0,1],
                  [0,0,1,1],
                  [1,1,1,1]])
    V = np.array([[1,0,1,1,0,1],
                  [0,1,1,0,1,1],
                  [0,0,0,0,0,0]])
    L = np.zeros((k, 3 * k + 8), dtype = int)
    S = np.concatenate((U, U), axis = 1)

    for i in range(k // 2):
        S = np.concatenate((S, V), axis = 1)
        L[2 * i: 2*i + 2, 4:8] = M
        L[2 * i: 2*i + 2, 8 + 6 * i: 14 + 6 * i] = N
    
    G = np.concatenate((L, S), axis = 0)
    
    SO = np.zeros((3, 3 * k + 8), dtype = int)
    SX = np.concatenate((S, SO), axis = 1)
    O = np.zeros((k, 3 * k + 8), dtype = int)
    LX = np.concatenate((L, O), axis = 1)
    LZ = np.concatenate((O, L), axis = 1)

    G_orth = find_null_space_GF2(G)

    m, n = G_orth.shape
    GO = np.zeros((m, n), dtype = int)
    SZ = np.concatenate((GO, G_orth), axis = 1)
    
    matrix = np.concatenate((SX, SZ, LX, LZ), axis = 0)
    
    return matrix

## [[6k+2, 3k, 2]] campbell-howard code
def stabs_choward(k):
    pass 
if __name__ == "__main__":  
    stabs_mat = stabs_Reed_Muller(3)
    print(stabs_mat)