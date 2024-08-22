import numpy as np
import time
from collections import defaultdict

def repetition (n, k): ## n: num of physical qubits, k: num of logical qubits
    row_ind, col_ind = zip(*((i, j) for i in range(1, n) for j in (i, (i + 1))))
    cond = ""
    for i in range(1, n):
        cond = cond + f"(1,0,{i})" + f"(1,0,{i+1})&&"
    cond = cond + f"(-1)^b_(1)(1,0,1)"
    # for i in range(1,n+1):
    #     cond = cond + f"(1,0,{i})"
    return cond

def rep_program(n, k):
    program = ""
    program = program + f"for i in 1 to {n} do q_(i) *= e_(i) X end;"
    for i in range(1, n):
        program = program + f"s_({i}) := meas (1, 0, {i})(1,0,{i+1}); "
    program = program + f"for i in 1 to {n} do q_(i) *= c_(i) X end;"

    return program

def surface(n, k): ## n is the subspace of 
    t = n // 2 + 1
    x_inds = defaultdict(list)
    z_inds = defaultdict(list)
    for i in range(1, t):
        for j in range(1, t):
            topl = (2 * i - 2) * n + (2 * j - 1)
            print(topl)
            x_inds[topl] = [topl, topl + 1, topl + n, topl + n + 1]

    return x_inds

# n = 51
# k = 1

# start = time.time()
# print(repetition(n, k))
# print(rep_program(n, k))
# end = time.time()

# print(end - start)