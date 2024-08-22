from z3 import *

file_path = 'SMT/fuladder.smt2'

parsed_formula = parse_smt2_file(file_path)

s = Solver()
s.add(parsed_formula)
print(s)
# Check satisfiability
if s.check() == sat:
    print('Model is sat')
    print(s.model())    
else:
    print("No solution found")

