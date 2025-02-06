import numpy as np
from scipy.stats import binom
from copy import deepcopy
import numpy as np
from scipy.linalg import solve
from linalg_GF import gf2_matrix_rank, find_null_space_GF2
import galois
# Define the matrices and vectors
# Replace these with your n*k matrices and k*1 vectors
def find_image_space(G):
    rows, cols = G.shape
    # pivot_columns = []
    supp_IM = np.zeros((rows, cols), dtype = int)
    for i in range(rows):
        j = 0
        while(j < cols and G[i, j] == 0):
            j += 1
        supp_IM[i, j] = 1
    supp_IM = galois.GF(2)(supp_IM)
    return supp_IM

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


# Q = np.array([[1,0,1],[1,1,0],[0,1,1],[1,1,1]])
# l = np.array([1,0,1,1]).reshape(-1,1)
# aug = np.concatenate((Q, l), axis=1)
# v = aug_Gaussian(aug, 3)
# print(v)
# exit(0)

Ham = np.array([[1,0,1,0,1,0,1],[0,1,1,0,0,1,1],[0,0,0,1,1,1,1]])
L = np.array([1,1,1,0,0,0,0])
P = np.zeros((7,14), dtype = int)
# P = np.zeros((3,7), dtype = int)    
P[:3,:7] = Ham
P[6,:7] = L                                                                                                                                                                                                                                                                                                                                                               
P[3:6,7:] = Ham
Q = deepcopy(P)
Q[1,:7] = np.array([1,1,0,0,1,1,0])
Q[2,:7] = np.array([1,0,1,1,0,1,0])
# P = np.array([[1,0,0,1,0,0,1,1,0,1],[0,1,0,0,1,0,0,1,1,0],[1,0,1,0,0,0,0,0,1,1],[0,1,0,1,0,1,0,0,0,1],[1,1,1,1,1,0,0,0,0,0]])
# Q = np.zeros((5,10), dtype = int)
# Q[0,:] = P[0,:]
# Q[1,:] = P[1,:] ^ P[2,:]
# Q[2,:] = P[0,:] ^ P[2,:]
# Q[3,:] = P[0,:] ^ P[1,:] ^ P[3,:]
# Q[4,:] = P[0,:]^ P[4,:]
print(P)
print(Q)
# GF2 = galois.GF(2)
# Pt = GF2(P.T)
# P = GF2(P)
# Qt = GF2(Q.T)
# Q = GF2(Q)

# # Pred = P.row_reduce()
# # print(P,Q)
# print(Q)
# print(Pred)
# # print(Qred)
# supp_Im = find_image_space(Pred)
# print(supp_Im)
# print(np.dot(supp_Im, Qt))
Qt = Q.T
n, k = Qt.shape
# print(Q@Q.T)
L = np.zeros((k, k), dtype=int)
# print(find_null_space_GF2(Q.T))
# exit(0)
Pt = P.T 
rhs = Pt[:, -1].reshape(-1, 1)
aug = np.concatenate((Qt, rhs), axis=1)
print(aug)
aug, sol = aug_Gaussian(aug, k)
# sol = np.mod(solve(Q.T @ Q, Q.T @ rhs), 2).reshape(-1).astype(int)

print(sol)
print(aug)
# L[:, i] = sol.reshape(-1)
# print(Qt)
# for i in range(k):
#     # print(col_i)
#     # Solve for the column of L that maps col_i (P2) to the corresponding column in P1
#     rhs = Pt[:, i].reshape(-1, 1)
#     # print(rhs)
    
#     aug = np.concatenate((Qt, rhs), axis=1)
#     print(aug)
#     aug, sol = aug_Gaussian(aug, k)
#     # sol = np.mod(solve(Q.T @ Q, Q.T @ rhs), 2).reshape(-1).astype(int)
#     if i == k - 1:
#         print(sol)
#         print(aug)
#     L[:, i] = sol.reshape(-1)
    

# Apply the transformation matrix to the vector v2
# result_vector = np.dot(L, v2)

print("Transformation Matrix L:")
print(L.T)

# print(result_vector)
