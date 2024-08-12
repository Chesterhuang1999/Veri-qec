#------------
# author: Chester Huang
# date: 2024.8.11
# version: 1.1.0
#------------

### A basic test for the running time of rule processor 


from lark import Tree, Token, Lark, Transformer, v_args
from data import repetition, surface, rep_program
from parser_bexp2 import get_parser
from transformer_bexp2 import precond_generator
import matplotlib.pyplot as plt
from z3 import * 
import time
import sys

sys.setrecursionlimit(1000000)
parser = get_parser()
k = 1 
cum_time = []
for i in range(1, 242):
    print(i)
    n = 2 * i - 1
    start = time.time()
    precond = repetition(n, k)
    postcond = repetition(n,k)
    program = rep_program(n, k)

    pre_tree, program_tree, post_tree = precond_generator(program, precond, postcond)

    end = time.time()
    cum_time.append(round(end - start, 7))

num_q  = [i for i in range(1, 242)]
plt.plot(num_q, cum_time)
plt.savefig('time501.png')
# n = 31
# start = time.time()
# precond = repetition(n, k)
# postcond = repetition(n,k)
# program = rep_program(n, k)

# pre_tree, program_tree, post_tree = precond_generator(program, precond, postcond)

# end = time.time()
# print(round(end - start, 10))