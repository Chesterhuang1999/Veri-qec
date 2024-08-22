from z3 import *

# Define the bit-vector variables for c1, c2, c3 with width 1

e1, e2, e3 = BitVecs('e1 e2 e3', 1)
c1, c2, c3 = ZeroExt(4, e1), ZeroExt(4, e2), ZeroExt(4, e3)

N = BitVecVal(3, 5)

sum_e = Sum(c1, c2, c3)

print(sum_e.sort())
print(sum_e.size())

s = Solver()
s.add(UGT(sum_e, N))
if s.check() == sat:
    print(s.model())
else: 
    print("unsat")