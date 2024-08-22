#------------
# author: Chester Huang
# date: 2024.8.11
# version: 1.1.0
#------------

### A basic test for the running time of rule processor 

from lark import Tree, Token, Lark, Transformer, v_args
from data import rep_cond, surface, rep_program
from parser_bexp2 import get_parser
from transformer_bexp2 import precond_generator
import matplotlib.pyplot as plt
from z3 import * 
import time
from multiprocessing import Pool
from timebudget import timebudget
import sys

sys.setrecursionlimit(1000000)
parser = get_parser()
k = 1 
parse_time = []
trans_time = []
# for i in range(2500):
#     if( i % 100 == 0):
#         print(i)
#     n = 2 * i + 1
#     start = time.time()
#     precond = rep_cond(n, k)
#     postcond = rep_cond(n,k)
#     program = rep_program(n, k)
#     triple = "{" + precond + "}" + program + "{" + postcond + "}"
#     tree = parser.parse(triple)
#     end = time.time()
#     parse_time.append(round(end - start, 7))
# num_q = [i for i in range(2500)]
# plt.plot(num_q, parse_time)
# plt.savefig('ptime5000.png')

def vcgen_test(i):
    print("index", i)
    n = 10 * i + 1
    start = time.time()
    precond = rep_cond(n, k)
    postcond = rep_cond(n,k)
    program = rep_program(n)
    triple = "{" + precond + "}" + program + "{" + postcond + "}"
    #tree = parser.parse(triple)
    t1, t2, pre_tree, program_tree, post_tree = precond_generator(program, precond, postcond)

    end = time.time()
    parse_time.append(round(t1, 7))
    trans_time.append(round(t2, 7))
    #parse_time.append(round(end - start, 7))

# start = time.time()
for i in range(50, 120):
    vcgen_test(i)
# end = time.time()
# print(end - start)

print(trans_time)
# @timebudget
# def run_op_para(op, input, pool):
#     pool.map(op, input)

# processes_count = 5
# if __name__ == '__main__':
#     processes_pool = Pool(processes_count)
#     run_op_para(vcgen_test, range(100, 120), processes_pool) 
# #     print(trans_time)
num_q  = [i for i in range(50, 120)]
plt.plot(num_q, parse_time,label = 'parse time')
plt.legend()
# plt.savefig('ptime350.png')
plt.plot(num_q, trans_time, label = 'transform time') 
plt.legend()
plt.savefig('time1000.png') 
# for i in range(300, 350):
#     vcgen_test(i)

# start = time.time()
# n = 5000
# precond = repetition(n, k)
# postcond = repetition(n,k)
# program = rep_program(n, k)
# triple = "{" + precond + "}" + program + "{" + postcond + "}"
# tree = parser.parse(triple)
# end = time.time()
# print(end - start)
# t1, t2, pre_tree, program_tree, post_tree = precond_generator(program, precond, postcond)
#print(t1, t2)
# n = 31
# start = time.time()
# precond = repetition(n, k)
# postcond = repetition(n,k)
# program = rep_program(n, k)

# pre_tree, program_tree, post_tree = precond_generator(program, precond, postcond)

# end = time.time()
# print(round(end - start, 10))