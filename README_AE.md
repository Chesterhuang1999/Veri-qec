<!-- This is the documentation for the artifacts attached to the paper 'Efficient Formal Verification of Quantum Error Correcting Programs'. As introduced in the paper, the artifacts include two modules, a verified verifier in Coq and an automatic verifier, Veri-QEC in Python. -->
# Basic Information
- Artifact: Veri-QEC (A **Verification** tool for **Quantum Error Correcting** Programs)
- Paper Title: Efficient Formal Verification for Quantum Error Correcting Programs
- Submission ID (Track: PLDI 2025 Artifacts): 10
- Zenodo Link: 

Veri-QEC is a prototype tool designed for automatic verification of quantum error correcting programs. 
<!-- As outlined in the paper, the artifacts include two modules, a verified verifier in Coq an an automatic verifier, Veri-QEC in Python.  -->
Veri-QEC introduces a robust framework for parsing and interpretating quantum error-correcting programs and its associated assertion logic. It then encodes the derived verification conditions into logical formulas. Leveraging SMT solvers building upon a parallel solving framework, the tool efficiently checks the satisfiability of these formulas.

# Getting Started for Evaluation


## Veri-QEC
A docker image is provided for evaluation. Firstly, you need to obtain the number of CPU cores in your machine. 

In Linux/MacOS using Bash: 
```bash
lscpu | grep "CPU(s):"
```

In Windows using PowerShell, you can use the following command:

```bash
(Get-WMiObject Win32_Processor).NumberOfCores
```
After obtaining the number of CPU cores in your machine, you can load the docker image and start the evaluation.

For Linux/ MacOS: 
```bash
docker load < docker/docker-veriqec-image
```
PowerShell: 
```bash
docker load -i docker\docker-veriqec-image
```

Execute the following commands to start the docker container, enter the working directory and load the directory of the output scripts:

```bash 
docker run -v `pwd`/Output: /Veri-qec/Output --rm -it docker-veriqec
```

You can load the /Output/ 

# Detailed Instructions for Evaluation

## Verifier in Coq

## Veri-QEC