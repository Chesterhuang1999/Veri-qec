#----------#
# Developer: Chester Huang
# Date: 2024/10/20
# Description: A benchmark libarary for quantum LDPC codes
#----------#

import numpy as np
from timebudget import timebudget
import math

from dataclasses import dataclass
import galois

from .linalg_GF import *
from scipy.sparse import csr_matrix, csc_matrix, coo_matrix, kron
from scipy.linalg import block_diag


### Check matrix generation for Quantum LDPC codes
## Quantum Tanner code
@dataclass
class PrimeG:
    p: int
    v: int

    def __post_init__(self):
       self.v = self.v % self.p
    
    def __mul__(self, other):
        return PrimeG(self.p, self.v + other.v)
    def __eq__(self, other):
        return self.p == other.p and self.v == other.v
    def __hash__(self):
        return hash((self.p, self.v))
    def inv(self):
        return PrimeG(self.p, self.p - self.v)
    
def stabs_Tanner(k, m, Ca, Cb):
    n = Ca.shape[1]
    p = k*(n**m)
    q = k*n**(m - 1)
    G = [PrimeG(p, j) for j in range(p)]
    A = [PrimeG(p, j*q) for j in range(n)]
    B = [PrimeG(p, j*q) for j in range(n)]
    Cat = Cb
    Cbt = Ca
    ng = len(G)
    na = len(A) 
    nb = len(B)
    Cplx = [((g,(0,0)), (a*g, (0,1)),(a*g*b,(1,1)), (g*b, (1,0))) for g in G for a in A for b in B]
    nc = len(Cplx)
    Cplx_dict = dict([(Cplx[j], j) for j in range(nc)]) 

    IaX = np.empty(na * nb * ng * 2, dtype=int)
    IbX = np.empty(na * nb * ng * 2, dtype=int)
    IgX = np.empty(na * nb * ng * 2, dtype=int)
    IcX = np.empty(na * nb * ng * 2, dtype=int)
    IaZ = np.empty(na * nb * ng * 2, dtype=int)
    IbZ = np.empty(na * nb * ng * 2, dtype=int)
    IgZ = np.empty(na * nb * ng * 2, dtype=int)
    IcZ = np.empty(na * nb * ng * 2, dtype=int)

    for idg in range(ng):
        g = G[idg]
        for idb in range(nb):
            b = A[idb]
            for ida in range(na):
                a = B[ida]
                j = idg*na*nb*2 + idb * na *2 + ida*2 # each (g,a,b) correspond to 2 index
                IaX[j], IaX[j + 1], IaZ[j], IaZ[j + 1] = ida , ida , ida , ida 
                IbX[j], IbX[j + 1], IbZ[j], IbZ[j + 1] = idb , idb, idb, idb 
                IgX[j], IgX[j + 1], IgZ[j], IgZ[j + 1] = idg, idg + ng, idg, idg + ng
                IcX[j], IcX[j + 1], IcZ[j], IcZ[j + 1] = (
                    Cplx_dict[((g, (0,0)), (a*g,(0,1)),(a*g*b,(1,1)),(g*b,(1,0)))],
                    Cplx_dict[((a.inv()*g*b.inv(),(0,0)),(g*b.inv(),(0,1)),(g,(1,1)),(a.inv()*g,(1,0)))],
                    Cplx_dict[((a.inv()*g,(0,0)),(g,(0,1)),(g*b,(1,1)),(a.inv()*g*b,(1,0)))],
                    Cplx_dict[((g*b.inv(),(0,0)),(a*g*b.inv(),(0,1)),(a*g, (1,1)),(g,(1,0)))]
                )
    
    IX = (IgX) * nc + IcX
   
    JX = (IaX) * nb + IbX

    VX = np.ones(na*nb*ng*2, dtype = int)

    IZ = (IgZ) * nc + IcZ
    JZ = (IaZ) * nb + IbZ
    VZ = np.ones(na*nb*ng*2, dtype = int)
    HXt = coo_matrix((VX, (IX, JX)), shape = (nc * 2 * ng, na * nb))
    HZt = coo_matrix((VZ, (IZ, JZ)), shape = (nc * 2 * ng, na * nb))
    HXt = HXt.toarray()
    HZt = HZt.toarray()
 
    HXt = np.reshape(HXt @ kron(Ca.T, Cb.T), (nc, -1), order = 'F')
    HZt = np.reshape(HZt @ kron(Cat.T, Cbt.T), (nc, -1), order = "F")

    HXt = HXt.T
    HZt = HZt.T
    n1, n2 = HXt.shape ## n2 is number of physical qubits, n1 is number of stabilizers
    # print(n1, n2)
    matrix = np.zeros((2*n1, 2*n2), dtype = int)
    matrix[:n1, :n2] = HXt
    matrix[n1:, n2:] = HZt
    matrix = stab_matrix_transformation(matrix, n2)
    k = n2 - matrix.shape[0]
    
    rank = np.linalg.matrix_rank(matrix[:n1, :n2])

    log_Z, log_X = logical_op_gen(matrix, rank, n2, k)
    
    stabs_mat = np.concatenate((matrix, log_X, log_Z), axis = 0)    
    x_stabs_mat = np.concatenate((matrix, log_X), axis = 0)
    z_stabs_mat = np.concatenate((matrix, log_Z), axis = 0)
    return stabs_mat

Ham743 = np.array([[1, 1, 0, 1, 1, 0, 0]
                   ,[1, 0, 1, 1, 0, 1, 0],
                   [0, 1, 1, 1, 0, 0, 1]])
Ham733 = np.array([[1, 0, 0, 0, 1, 1, 0], 
                   [0, 1, 0, 0, 1, 0, 1],
                   [0, 0, 1, 0, 0, 1, 1],
                   [0 ,0, 0, 1, 1, 1, 1]])



Rep51 = np.array([[1, 1, 0, 0, 0],
                  [1, 0, 1, 0, 0],
                  [1, 0, 0, 1, 0],
                  [1, 0, 0, 0, 1]])
Par54 = np.array([[1, 1, 1, 1, 1]])

Rep31 = np.array([[1, 1, 0],
                  [1, 0, 1]])
Par32 = np.array([[1, 1, 1]])


## Hypergraph product code

def stabs_hyp_prod(C1, C2):
    m1, n1 = C1.shape
    m2, n2 = C2.shape  
    r1 = gf2_matrix_rank(C1)
    r2 = gf2_matrix_rank(C2)
    k1 = n1 - r1
    k2 = n2 - r2
    k1t = m1 - r1
    k2t = m2 - r2
 
    HX = np.concatenate((np.kron(C1, np.eye(n2, dtype = int)), np.kron(np.eye(m1, dtype = int), C2.T)), axis = 1)
    HZ = np.concatenate((np.kron(np.eye(n1, dtype = int), C2), np.kron(C1.T, np.eye(m2, dtype = int))), axis = 1)
    M = m1*n2 + m2*n1
    N = n1*n2 + m1*m2
    matrix = np.zeros((M, 2*N), dtype = int)
    matrix[:m1*n2, :N] = HX
    matrix[m1*n2:, N:] = HZ
    matrix = stab_matrix_transformation(matrix, N)
    K = k1*k2 + k1t*k2t
    rank = gf2_matrix_rank(HX)
    log_Z, log_X = logical_op_gen(matrix, rank, N, K) 
    stabs_mat = np.concatenate((matrix, log_X, log_Z), axis = 0)
   
    return stabs_mat

classical734 = np.array([[1, 1, 0, 1, 0, 0, 0],
                        [0, 1, 1 ,0, 1, 0, 0],
                        [0, 0, 1, 1, 0, 1, 0],
                        [0, 0, 0, 1, 1, 0, 1],
                        [1, 0, 0, 0, 1, 1, 0],
                        [0, 1, 0, 0, 0, 1, 1],
                        [1, 0, 1, 0, 0, 0, 1]], dtype = int)

## Bivariate bicycle code [[]]
def cyc_shift(l):
    """Cyclic shift matrix of size l"""
    mat = np.zeros((l, l), dtype = int)
    for i in range(l):
        mat[i, (i + 1) % l] = 1
    return mat
def mat_pow(A, n):
    """Matrix power"""
    if n == 0:
        return np.eye(A.shape[0], dtype = int)
    elif n == 1:
        return A
    else:
        return np.linalg.matrix_power(A, n)
bi_choice_A = [[3, 1, 2],
               [9, 1, 2],
               [3, 1, 2],
               [3, 1, 2],
               [3, 2, 7],
               [9, 1, 2],
               [3, 10, 17]]
bi_choice_B = [[3, 1, 2],
               [0, 2, 7],
               [3, 1, 2],
               [3, 1, 2],
               [3, 1, 2],
               [3, 25, 26],
               [5, 3, 19]]
numq_set = np.array([72, 90, 108, 144, 288, 360, 756])
def bivariate_bicycle(l, m):
    """Bivariate bicycle code for code parameter (l, m)"""
    """"""
    matx = np.kron(cyc_shift(l), np.eye(m, dtype = int))
    maty = np.kron(np.eye(l, dtype = int), cyc_shift(m))
    numq = 2*l*m
    choice = np.where(numq_set == numq)[0][0]
    # print(f"numq = {numq}, choice = {choice}")
    matA = mat_pow(matx, bi_choice_A[choice][0]) + mat_pow(maty, bi_choice_A[choice][1]) + mat_pow(maty, bi_choice_A[choice][2])
    matB = mat_pow(maty, bi_choice_B[choice][0]) + mat_pow(matx, bi_choice_B[choice][1]) + mat_pow(matx, bi_choice_B[choice][2])
    Hx = np.concatenate((matA, matB), axis = 1)
    Hz = np.concatenate((matB.T, matA.T), axis = 1)

    stabilizer = block_diag(Hx, Hz)

    rank = gf2_matrix_rank(Hx)
    k = numq - stabilizer.shape[0]
    log_X, log_Z = logical_op_gen(stabilizer, rank, numq, k)
    
    total_mat = np.concatenate((stabilizer, log_X, log_Z), axis = 0)
    return total_mat

