from z3 import *

# Step 1: Create a solver for a specific logic
solver = SolverFor("QF_BV")

# Step 2: Create some BitVector variables and add constraints
x = BitVec('x', 32)
y = BitVec('y', 32)

solver.add(x + y == 10)

# Step 3: Check satisfiability
print(solver.check())

# Step 4: Export the formula to an SMT-LIB v2 file
with open('output.smt2', 'w') as f:
    # Manually write the logic declaration
    f.write("(set-logic QF_BV)\n")
    
    # Write the assertions in SMT-LIB format
    f.write(solver.to_smt2())
