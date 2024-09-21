from bitwuzla import * 
from timebudget import timebudget
import numpy as np

def fun(choice):
    err_vals = [1 for _ in range(choice)]
    str_parts = []
    for i in range(1, 10):
        str_parts.append(f"e{choice}_{i+1} == {err_vals[i]}")
    
    return '&'.join(str_parts)

print(fun('x'), fun('z'))