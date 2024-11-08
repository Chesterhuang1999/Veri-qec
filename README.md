# Veri-qec

A prototype tool for formal verification of quantum error correcting programs. 

We implemented parsing and interpretation of quantum error correction programs and assertion logic based on Lark and encoded the inferred verification conditions as SMT formulas and invoking an SMT solver for resolution.

## Evaluations 

We have evaluated Veri-qec in paper. 

Clone this repo and cd `./Veri-qec/src`. 

```bash
git clone https://github.com/Chesterhuang1999/Veri-qec.git
```


## Installation 

Our tool depends on Lark as its parser and interpreter development tool; Furthermore Z3 and CVC5 are adopted as default SMT solvers. They can be directed installed via `pip`. 

```bash
pip install lark

pip install z3-solver

pip install cvc5
```

We recommend [Python 3.9.18] as the default running environment. 
