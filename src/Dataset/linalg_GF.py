import numpy as np
from scipy.linalg import lu
from scipy.sparse import csc_matrix, block_diag, kron, eye
from copy import deepcopy
import math
import galois
import time
from collections import defaultdict

#### Some basic linear algebra for binary matrices (reload_) ####
# Return symplectic product of two 1*2n vectors(matrices)
def symplectic_product(a, b):
    
    n = a.shape[1] // 2 if len(a.shape) == 2 else a.shape[0] // 2
    inner = np.zeros((2*n, 2*n), dtype = int)
    inner[0:n, n:2*n] = eye(n).toarray()
    inner[n:2*n, 0:n] = eye(n).toarray()
    product = a @ inner @ b.T   
    product = product % 2
    return product

# Compute the matrix rank over GF(2)
def gf2_matrix_rank(A):
    # Ensure the matrix consists of binary entries
    A = np.mod(A, 2)
    num_rows, num_cols = A.shape
    rank = 0

    for col in range(num_cols):
        # Find the pivot row
        pivot_row = None
        for row in range(rank, num_rows):
            if A[row, col] == 1:
                pivot_row = row
                break

        if pivot_row is None:
            continue

        # Swap the pivot row to the current rank row
        if pivot_row != rank:
            A[[rank, pivot_row]] = A[[pivot_row, rank]]

        # Eliminate all rows below pivot
        for row in range(rank + 1, num_rows):
            if A[row, col] == 1:
                A[row] = np.logical_xor(A[row], A[rank]).astype(int)

        # Move to the next row in the reduced matrix
        rank += 1

    return rank
# Reduce a matrix over GF(2) to its row-echelon form
def row_reduce_binary(matrix):
    """ Perform row reduction over GF(2) (binary field) """
    matrix = matrix.copy()
    num_rows, num_cols = matrix.shape
    
    lead = 0
    for r in range(num_rows):
        if lead >= num_cols:
            return matrix
        i = r
        while matrix[i, lead] == 0:
            i += 1
            if i == num_rows:
                i = r
                lead += 1
                if lead == num_cols:
                    return matrix
        # Swap rows
        matrix[[i, r]] = matrix[[r, i]]
        
        # Make the leading coefficient 1
        matrix[r] = matrix[r] % 2
        
        # Make all rows below and above this one 0 in the current column
        for i in range(num_rows):
            if i != r and matrix[i, lead] == 1:
                matrix[i] = (matrix[i] + matrix[r]) % 2
        lead += 1
    
    return matrix
## Find the null_space of a matrix over GF(2)
def find_null_space_GF2(G):
    G = row_reduce_binary(G)
    
    num_rows, num_cols = G.shape
    
    # Identify pivot columns
    pivot_columns = []
    free_columns = []
    for i in range(num_rows):
        for j in range(num_cols):
            if G[i, j] == 1:  # There's at least one non-zero entry in column j
                pivot_columns.append(j)
                break
    
    free_columns = [col for col in range(num_cols) if col not in pivot_columns]


    print(pivot_columns)
    print(free_columns)
    
   
    null_space_basis = []
    
    
    for free_col in free_columns:
        
        solution = np.zeros(num_cols, dtype=int)
        solution[free_col] = 1
        
       
        for row in range(num_rows - 1, -1, -1):
            pivot_col = next((j for j in range(num_cols) if G[row, j] == 1), None)
            if pivot_col is not None:
                solution[pivot_col] = np.dot(G[row, :], solution) % 2
        
        null_space_basis.append(solution)
    
    return np.array(null_space_basis)
## Find the transformation matrix between two matrices 
def aug_Gaussian(A, k):
    n = A.shape[0]
    row_pivot = 0
    for c in range(k):
        pivot = -1
        for r in range(row_pivot, n):
            if A[r, c]  == 1:
                pivot = r
                break
        if pivot == -1:
            continue

        if pivot != row_pivot: 
            temp = deepcopy(A[row_pivot,:])
            A[row_pivot,:] = deepcopy(A[pivot,:])
            A[pivot,:] = deepcopy(temp)
            # A[row_pivot], A[pivot] = A[pivot], A[row_pivot]

    
        for r in range(row_pivot + 1, n):
            if A[r, c] == 1:
                for i in range(c, k + 1):
                    A[r, i] ^= A[row_pivot, i]
        row_pivot += 1
        if row_pivot == n:
            break

    v = np.zeros((k, 1), dtype=int)
    for row in range(row_pivot - 1, -1, -1):
        pivot_col = None 
        for c in range(k):
            if A[row, c] == 1:
                pivot_col = c
                break
        if pivot_col is None:
            continue

        rhs = A[row][k]
        for c in range(pivot_col + 1, k):
            rhs ^= (A[row][c] & v[c])

        v[pivot_col] = rhs

    return A, v

## Perform gaussian elimination of a matrix over GF(2)
def gaussian_elimination(matrix):
    m, n = matrix.shape
    
    n = n // 2
    #col_swaps = list(range(2 * n))
    r = gf2_matrix_rank(matrix[:, :n]) # Rank of G1
  
    ## Gaussian elimination of G1
    # i, j = 0, m - 1
    # while(i < j):
    #     while(np.all(matrix[i, :n] == 0) == False):
    #         i += 1
    #     while(np.all(matrix[j,:n] == 0) == True):
    #         j -= 1
    #     if i < j:
    #         matrix[[i, j], :] = matrix[[j, i], :]
    botnz = m - 1
    for i in range(m):
        if np.all(matrix[i, :n] == 0) == True:
            j = botnz
            while(j > i and np.all(matrix[j, :n] == 0) == True):
                j -= 1
            if j > i: 
                matrix[[i, j], :] = matrix[[j, i], :]
                botnz = j - 1
        # swap the pivot col to the diagonal line
        if matrix[i, i] == 0:
            for j in range(i + 1, n):
                if matrix[i, j] == 1:
                    matrix[:, [i, j]] = matrix[:, [j, i]]
                    matrix[:, [n + i, n + j]] = matrix[:, [n + j, n + i]]
                    #col_swaps[i], col_swaps[j] = col_swaps[j], col_swaps[i]
                    #col_swaps[n + i], col_swaps[n + j] = col_swaps[n + j], col_swaps[n + i]
                    break

        # print(matrix[i,:n]) 
        # print(matrix[i+1,:n])           
        for j in range(i + 1, m):
            if matrix[j, i] == 1:
                matrix[j, :] ^= matrix[i, :]
        
        # print(matrix[i + 1,:n])

    # i, j = 0, m - 1
    # while(i < j):
    #     while(np.all(matrix[i, :n] == 0) == False):
    #         i += 1
    #     while(np.all(matrix[j,:n] == 0) == True):
    #         j -= 1
    #     if i < j:
    #      matrix[[i, j], :] = matrix[[j, i], :]

    for i in range(r-1, -1, -1):
        for j in range(i):
            if matrix[j, i] == 1:
                matrix[j, :] ^= matrix[i, :]
    
    
    ### Gaussian elimination of G2, bottom right part
    #r2 = np.linalg.matrix_rank(matrix[r:, n+r:]) # Rank of G2
    botnz = m - 1
    for i in range(r, m):
        if np.all(matrix[i, n+r:] == 0) == True: 
            j = botnz
            while(j > i and np.all(matrix[j, n+r:] == 0) == True):
                j -= 1
            if j > i:
                matrix[[i, j], :] = matrix[[j, i], :]
                botnz = j - 1
        if matrix[i, n + i] == 0:
            for j in range(i + 1, n):
                if matrix[i, n + j] == 1:
                    matrix[:, [n + i, n + j]] = matrix[:, [n + j, n + i]]
                    matrix[:, [i, j]] = matrix[:, [j, i]]  
                    break
        
        for j in range(i + 1, m):
            if matrix[j, n + i] == 1:
                matrix[j, :] ^= matrix[i, :]

    
    # i, j = r, m - 1
    # while(i < j):
    #     while(np.all(matrix[i, n:] == 0) == False and i < j):
    #         i += 1
    #     while(np.all(matrix[j,n:] == 0) == True and i < j):
    #         j -= 1
    #     if i < j:
    #      matrix[[i, j], :] = matrix[[j, i], :]
    for i in range(m - 1, r - 1, -1):
        
        for j in range(i):
            if matrix[j, n + i] == 1:
                matrix[j, :] ^= matrix[i, :]

    nz = m - 1
    print(nz)
    while(np.all(matrix[nz, :] == 0) == True):
        nz -= 1
    
    
    matrix = matrix[:nz + 1, :]

    return matrix

## Generate logical operators for a given matrix without direct knowledge
def logical_op_gen(matrix, rank, n, k):
    
    #Generate logical Z
    submat_A2 = matrix[0:rank, n-k:n]
    submat_A2 = submat_A2.T
    submat_C = matrix[ 0:rank, (2*n -k):2*n]
    submat_C = submat_C.T
    submat_E = matrix[rank:, 2*n-k : 2*n]
    submat_E = submat_E.T
    logical_X = np.zeros((k, 2*n), dtype = int)
    logical_X[:, rank: n - k] = submat_E
    logical_X[:, n:n+rank] = submat_C
    logical_X[:, n-k:n] = eye(k).toarray()

    logical_Z = np.zeros((k, 2*n), dtype = int)
    logical_Z[:, n:n+rank] = submat_A2
    logical_Z[:, 2*n-k:2*n] = eye(k).toarray()

    return logical_Z, logical_X

def stab_matrix_transformation(matrix, n):
    
    r = gf2_matrix_rank(matrix[:, :n])
    x_stabs_matrix = np.zeros((n, 2*n), dtype = int) 
    z_stabs_matrix = np.zeros((n, 2*n), dtype = int)
    matrix = gaussian_elimination(matrix)
    #matrix[r:, n+r:] = gaussian_elimination(matrix[r:,n+r:], rank2)
    # for col in range(n + r, n + m):
    #     # 对于右侧的每一列，从上往下进行消元
    #     for row in range(r):
    #         if matrix[row, col] == 1:
    #             # 使用第 r 到 k 行的行进行消元操作
    #             for target_row in range(r, m):
    #                 if matrix[target_row, col] == 1:
    #                     matrix[row, :] ^= matrix[target_row, :]
    #                     break  # 按位异或消元
    return matrix
    

if __name__ == '__main__':
    pass
