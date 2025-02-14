# Veri-qec: A formal verification tool for quantum error correcting programs

*Veri-qec* is a prototype tool for formal verification of quantum error correcting programs, based on quantum Hoare logic. 

We developed a parsing and interpretation framework for quantum error-correcting programs and its associated assertion logic using Lark, encoding the inferred verification conditions as SMT formulas. Subsequently, we employed an SMT solver to verify the correctness of these formulas.

## Installation dependencies

Our tool applies Lark as its parser and interpreter development tool; Furthermore, Z3 and CVC5 are adopted as default SMT solvers. All of them can be directly installed via `pip`. 

```bash
pip install lark=0.12.0

pip install z3-solver

pip install cvc5
```

[Lark 0.12.0] is required to ensure proper operation. On the other hand, We recommend [Python 3.9.18], [z3 4.13.0], [cvc5 1.2.0] as the default running environment. 

## Main features
- Automatic parsing, interpretation for input Hoare triples.
- Transformation from hybrid classical-quantum verification condition (VC) to purely classical VC
- Apply z3 to encode the verification into SMT formula
- Provide interfaces for various SMT solvers, cvc5 as default
<!-- Specifically, we verify the general correctness property of various codes. 
For error-correcting codes with odd code distances, we verify its ability to accurately correct errors; For error-detecting codes with even code distances, its capability of detecting errors is evaluated.  -->

## Evaluations 

We have evaluated *Veri-qec* in the paper 'Efficient Formal Verification for Quantum Error Correcting Programs' (arxiv: ). 

Specifically, we derived the parity-check matrices and logical operators of the QEC codes selected in our benchmark set, the database is at `./src/Dataset/special_codes.py` and `./src/Dataset/qldpc_codes.py`.

The readers can reproduce the experiments done in the paper via the following steps. First, clone this repo at local: 

```bash
git clone https://github.com/Chesterhuang1999/Veri-qec.git
```

To verify the correctness of accurate decoding property, use 'execute_verify.py':
```bash
python src/execute_verify.py
```

To verify the correctness of accurate detection property, use 'execute_detect.py':

```bash
python src/execute_detect.py
```

Besides, users can also specify the conditions satisfied by the errors based on the actual model. Use:
```bash
python src/execute_user_provide.py
```
We provide two default constraints, locality and discreteness in current work. Users can specify the desired constraints by defining custom subclasses of `subtask_generator`.

We also support the implementation of logical Clifford + T gate, in fault-free case. To the correctness of our logical T gate protocol, we provide an exmaple in `src/execute_logical.py` to automatically evaluate the precondition of logical T gate under the surface code, with arbitrary code distance. Just use: 
```bash 
python src/execute_logical.py
```
