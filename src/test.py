from bitwuzla import * 
from timebudget import timebudget
@timebudget
def check_satisfiability(file_path):
    # Initialize a Bitwuzla instance
    
    tm = TermManager()
    # Set options (add any specific options if needed)
    options = Options()
    bzla = Parser(tm, options)
    # Example: Enable model generation
    options.set("produce-models", True)

    # Parse the SMT-LIB file
    res = bzla.parse(file_path)
    assertions = bzla.bitwuzla().get_assertions()
    for a in assertions: 
        print(a)
    # Check satisfiability

 

if __name__ == "__main__":
    # Path to your formula in SMT-LIB format
    formula_smt2_path = 'src/surface.smt2'
    check_satisfiability(formula_smt2_path)
