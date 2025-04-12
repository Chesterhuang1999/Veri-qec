<!-- This is the documentation for the artifacts attached to the paper 'Efficient Formal Verification of Quantum Error Correcting Programs'. As introduced in the paper, the artifacts include two modules, a verified verifier in Coq and an automatic verifier, Veri-QEC in Python. -->
# Research Artifact for Paper 228 'Efficient Formal Verification for Quantum Error Correcting Programs'

## Basic Information
- Artifact: Veri-QEC (A **Verification** tool for **Quantum Error Correcting** Programs)
- Paper Title: Efficient Formal Verification for Quantum Error Correcting Programs
- Submission ID (Track: PLDI 2025 Artifacts): 10
- Zenodo Link: 10.5281/zenodo.15050947

As for the artifact evaluation, we claim for available and reusable badges. If the artifacts do not fulfill the criteria for reusability, we instead request consideration for the functional badge.

As described in the paper, the artifacts include two modules. The first module is a verified verifier for QEC programs, developed in Coq and built upon the CoqQ library. The second one is a Python-based tool designed to automate the verification for quantum error correction programs. Here is the documentation for the Python-based tool, Veri-QEC.

<!-- ## Verified QEC Program Verifier
In this verified program verifier, We first formalize the semantics of the classical-quantum programs and then build the verified prover, prove the soundness of its program logic. This is achieved by ~4700 lines of Coq codes based on the CoqQ project. 

### Getting started 
Installing dependencies requires **opam**, the source-based package manager for OCaml. To install opam, executing the following commands:

- Debian and Ubuntu:
```bash
apt install opam
```
- MacOS: (Homebrew or MacPorts is required)
```bash
# Homebrew 
brew install opam

#MacPort
port install opam
```

We depend on the following external libraries to build this project: 
```
  "coq"                      { = "8.18.0"           }
  "coq-core"                 { = "8.18.0"           }
  "coq-elpi"                 { = "2.0.0"            }
  "dune"                     {>= "3.2" & <= "3.13.0"}
  "dune-configurator"        { = "3.12.1"           }
  "coq-hierarchy-builder"    { = "1.7.0"            }
  "coq-mathcomp-ssreflect"   { = "2.2.0"            }
  "coq-mathcomp-algebra"     { = "2.2.0"            }
  "coq-mathcomp-fingroup"    { = "2.2.0"            }
  "coq-mathcomp-analysis"    { = "1.3.1"            }
  "coq-mathcomp-real-closed" { = "2.0.0"            }
  "coq-mathcomp-finmap"      { = "2.1.0"            }
```

You can install them by opam directly: 
```bash 

```
### Evaluation -->


## Veri-qec: A prototype tool for automatic verification of quantum error correcting programs


Veri-QEC is a prototype tool designed for automatic verification of quantum error correcting programs. 
<!-- As for the artifact evaluation, we claim for available and reusable badges. If it does not fulfill the reusable criteria, we claim the functional badge instead. -->

We introduce a robust framework for parsing and interpretating quantum error-correcting programs and its associated assertion logic. It then encodes the derived verification conditions into logical formulas. Leveraging SMT solvers building upon a parallel solving framework, the tool efficiently checks the satisfiability of these formulas.


### Getting Started for Evaluation

#### Preparation for docker container
A docker image is provided for evaluation, so you don't need to install all of the dependencies by yourself.

Firstly, you need to obtain the number of CPU cores in your machine. 

In Linux/MacOS using Bash: 
```bash
lscpu | grep "CPU(s):"
```

In Windows using PowerShell, you can use the following command:

```bash
(Get-WMiObject Win32_Processor).NumberOfCores
```
After obtaining the number of CPU cores in your machine, you can load the docker image from the archive file `docker-veriqec.tar` and start the evaluation.

For Linux/ MacOS: 
```bash
tar -xvf docker-veriqec.tar
docker load < docker-veriqec
```
PowerShell: 
```bash
tar -xvf docker-veriqec.tar
docker load -i docker-veriqec
```

If it fails, try the following in Linux/MacOS:
```bash
cat docker-veriqec.tar 
sudo docker load
```
or in PowerShell:
```bash
Get-Content docker-veriqec.tar -Raw | docker load
```

Or you can directly build from the zip file of source codes `Veri-qec.zip`:

Linux, MacOS and PowerShell:
```bash
docker build -t docker-veriqec .
```

Execute the following commands to start the docker container, enter the bash environment and load the directory of the output results:

For Linux/MacOS with bash: 
```bash 
docker run -v `pwd`/eval-Output:/Veri-qec/eval-Output --rm -it docker-veriqec
```
Powershell:
```bash
docker run -v ${PWD}$ /eval-Output:/Veri-qec/eval-Output --rm -it docker-veriqec
```

`-v` options mounts the `eval-Output` folder in the current directory to the corresponding directory within the docker container, while `--rm` creates a container that will be deleted once exit. Through this you can view the evaluation results even when the container is closed. 

We set the default working directory to be `/Veri-qec/` and you can use `pwd` at the initial interface to verify whether the working directory is correct.

### Package lists in Zenodo

- docker-veriqec.tar: The archive file for the docker environment containing the artifact Veri-qec.

- dirac-project-veriqec.zip: The source codes and Dockerfile for the verified verifier developed in Coq. 

- Veri-qec.zip: The source codes and Dockerfile for Veri-qec along with the output scripts.

#### Artifact Usage 

We primarily evaluate the effectiveness of the tool in verifying the following three functionalities for quantum error correcting programs:

- Accurately decode the syndromes and correct the errors (full-verification)
- Accurately correct errors with constraints on the errors (part-verification)
- Accurately detect all errors (full-verification)


We use argparse to support the parsing of parameters. The explanations of the parameters can be seen below: 

| **Parameters** | **Explanation**| 
| ---------------| ---------------| 
| --cpucount     |  The number of CPU cores you wish to use | 
| --code         |  The type of the QEC code | 
| --param1       |  Additional Parameter #1 for the QEC code (Optional) |
| --param2       |  Additional Parameter #2 for the QEC code (Optional) | 

For some simple codes, e.g. carbon codes or Steane code additional parameters are not required. For other codes, additional parameters are necessary to determine the exact construction and the code distances. For example, to verify the properties of XZZX codes the distances for Pauli $X$ and Pauli $Z$ errors ($d_x, d_z$) should be provided. 

We recommend starting the evaluation from simple cases, for example the rotated surface codes we used to evaluate the effectiveness of the functionalities of correcting errors. Here are an example illustrating the usage of *Veri-qec*:

```bash
python3 src/execute_verify.py \
--cpucount 16 --code surface --param1 7 
```

To evaluate the results of the first functionality, using the command above and adjust the additional parameter (which is the distance of the surface code) from the set $\{3,5,7,9,11\}$. 
In terminal, the output is like:
```
cond_checker took 3.611sec
```

**You can find the detailed output results in the `eval-Output/correction` directory.** The typical output for this example will be (the running time is obtained using 240 cores): 
```
Task generated. Start checking.
total_job: 4018
tasks for X error: 2009 | tasks for Z error: 2009
task generation time: 0.46747398376464844
No counterexample found, all errors can be corrected.

Finish all jobs. Checking time: 3.138540744781494
```

The second line illustrates the total subtasks we divide and the third line is the time consumed to parsing and generate the logical formulas. If there are no counterexamples (which means all of the subtasks will output `unsat`), then you'll see the fourth line which reports success. The final line displays the time taken by the solver to resolve all subtasks. If it takes a relatively long time ($>10s$, or $>60s$, depending on the estimated time cost in total) to finish the check, then we present the phased verification results and the current progress in the following way:

```
3078/67800: finish job file[3191], cost_time: 0.19430899620056152
[3191, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ['num_bit: 44', 'num_zero: 41', 'num_one: 3', 'one_pos: [20, 24, 43]'], 0.19430899620056152, 'unsat']
 ++++++ show progress ++++++ 
start time: 2025-03-08 09:23:37
current time: 2025-03-08 09:23:47
cost time: 0:00:10.000808
left time: 0:03:30.289905
estimated time: 0:03:40.290713
estimated finished time: 2025-03-08 09:27:17
instance per seconed(all process): 307.78
instance average runtime(s): 0.78
finished persent: 4.54%
processed jobs: 3078
unprocessed jobs: 64722
```

The array starting with $3191$ reports information about the subtasks completed at that moment, including the length of the enumeration, the number of ones, the verification time, and the check result. If there exists some counterexamples that indicate the violation of the property, we would report it immediately, as shown below. 
```
There exists a counterexample for X error:

rank: 719 | id: 719 | time: 0.053060293197631836 | result: sat

[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]
num_bit: 11 | num_zero: 8 | num_one: 3 | one_pos: [8, 9, 10]
```

It may take a long time ($\approx 19.25$ CPU days or $\approx 24$ hours for a 16-core CPU) to reproduce the result when the code distance equals to $11$, so you may refer to the `/Output/` directory for the experimental results for all of the benchmark codes while waiting for the results.

You can exit the container by typing `exit`. The test outputs will remain available in `pwd/eval-Output`. You can refer to it for evaluation. Once you have finished all evaluation, you can delete the docker image from the Docker environment:

```bash 
docker rmi docker-veriqec
```
### Detailed Instructions for Evaluation


#### Benchmarks 
During our evaluation of the tool's functionality, we use a total of 14 types of stabilizer codes and their implementations. Based on their properties (primarily code distance), we divided them into two categories: Error Correcting codes and Error Detecting codes. Most of the stabilizer codes can detect and correct errors below certain thresholds; these codes often have odd code distances to saturate the upper bound of correctable errors; typical examples are surface codes (and the variants) and quantum reed-muller code. Error Detecting codes, for example the basic [8,3,2] color code or the campbell-howard code have even code distance (for Z error, it is $2$), indicating that they can only detect a single Pauli $Z$ error but are not capable of determining the locations and correct it. For these codes along with some codes with even code distances, we tend to verify their abilities to detect certain number of errors. 
<!-- There are also some codes whose exact code distances are not straightforward; to advance in identifying and verifying the precise code distances of these codes, we also  -->

We list the benchmarks of codes and properties we aim to verify for them in the table below. For scalable codes with svariable parameters we provide the general forms. 

<!-- - Error Correcting Properties:

| Codes | Surfaces code | 
| ------ | -----------|  -->


<table>
  <tr>
    <th colspan = "2">Error correcting property</th>
    <th colspan = "2">Error detecting property</th>
  </tr>
  <tr>
    <td >Codes</td>
    <td>Parameters</td>
    <td >Codes</td>
    <td>Parameters</td> 
  </tr>
  <tr>
    <td>Surface code</td>
    <td>[d^2, 1, d]</td>
    <td>basic 3D color code</td>
    <td>[8,3,2]</td>
  </tr>
  <tr>
      <td> Reed-Muller code</td>
      <td> [2^r - 1, 1, 3] </td>
      <td> Carbon code </td>
      <td> [12,2,4] </td>
  </tr>
  <tr>
      <td> Goettsman code </td>
      <td> [2^r, 2^r - r - 2, 3] </td>
      <td> Campbell-howard code </td>
      <td> 
  </tr>
  <tr>
      <td> Steane code </td>
      <td> [7,1,3] </td>
      <td> Triorthogonal code </td>
      <td> [3k +8, k, 2] </td>
  </tr>
  <tr>
      <td> XZZX code </td>
      <td> [d_xd_z, 1, min(d_x, d_z)] </td>
      <td> Hypergraph product code</td>
      <td>[98,18,4]</td>
  </tr>
  <tr>
    <td> Honeycomb code </td>
    <td> [(3d^2+1)/4, 1, d] </td>
    <td> Tanner code </td>
    <td> [343, 31, d >= 4] </td>
  </tr>
  <tr>
    <td> Dodecacode </td>
    <td> [11,1,5] </td>
    <td> </td>
    <td></td>
  </tr>
  <tr>
    <td> Six-qubit code </td>
    <td> [6,1,3]</td>
    <td></td>
    <td></td>
  </tr>
</table>

For Hypergraph product code and quantum Tanner code we fix the classical codes used as constructors. 

The evaluation commands and parameters set for verification are as follows.

- Evaluation for error correcting property (full verification)
```bash
python3 src/execute_verify.py --cpucount nc --code codename --param1 d1 --param2 d2
```
Parameters for verification: 
| codename | param1 | param2 |
| --------- | ------| -------| 
| surface  | {3,5,7,9,11}| / | 
| reed_muller | {3,4,5,6,7,8,9} | / |
| XZZX | {5,7,9,11} | {5,7,9,11} |
| Goettsman | {3,4,5,6,7,8} | / | 
| Honeycomb | {3,5} | / | 
| steane | / | /|
| dodecacode | / | / | 


- Evaluation for error correcting property with user-provided constraints (partial verification)
```bash
python3 src/execute_user_provide.py --cpucount nc --distance d --constraint cstype 
```

We use surface code as the benchmark code here and the distances for three types of constraints are:

|cstype | distance |
|------- | --------|
| discrete | {3,5,7,9,11} | 
| local | {5,7,9,11,13} | 
| combined | {7,9,11,13,15,17,19} |

- Evaluation for error detecting property (full-verification)

```bash 
python3 src/execute_detect.py --cpucount nc --code codename --p1 d1 --p2 d2
```
We configured the corresponding parameters for the error-correcting codes used in these experiments. Note that for triorthogonal code we additionally set the second parameter as to provide an example for incorrect parameters ($d_x = 6$ is correct, while $d_x = 7$ is not). If set to 7, the SMT solver would report counterexamples and terminate the process pool. 

| codename | p1 | p2| 
|----------|--------|--------|
| camp_howard | {2} | /| 
| carbon | / | / |
| basic_color | / | / | 
| triorthogonal | {32, 64} | {6,7} |

The only exception is quantum Tanner code. Due to the number of qubits and relative large weight of stabilizers, we specifically designed another empirical function to dividing the problem into subtasks. The evaluation command for quantum Tanner code is:
```bash 
python3 src/execute_detect_Tanner.py --cpucount nc --basis (Ham7, Rep5)
```

Ham7 refers to the quantum Tanner code which have 343 qubits; Rep5 refers to the code with 125 qubits. 

Detailed discussions for verification of quantum Tanner code in the following section. 

- Evaluation for examples of fault-tolerant gadgets 

Our tool supports the verification of simple fault-tolerant gadgets, with or without propagated errors from the previous QEC cycle. We choose the logical GHZ state preparation (without propagated errors) and a logical CNOT gate (with propagated errors) as the examples. To see the results, you can execute the following command:
```bash 
python3 src/logical_op_test.py
```

#### Claims and Updates for the evaluation results in the paper

I. The experimental results produced by Veri-QEC can support the following claims mentioned in the paper:

- Veri-QEC can perform general verification for all error configurations on surface codes with up to 121 qubits in $\sim 200$ minutes (see `Output/correction/correction_surface_11.txt`); 

- Veri-QEC can verify the correctness detection property on surface code with distance up to 23; It can detect an counterexample when distance is set to be the real value + 1 for surface codes with distance up to 25 (see `Output/detection_surface/detection_surface_(23,25).txt`). 

- Veri-QEC can perform partial verification for certain user-provided constraints up to 361 qubits within $\sim 100$ minutes (see `Output/userprov_constraint/usrprov_comb_19.txt`).

- Veri-QEC can verify simple examples of fault-tolerant gadgets. (See Section 7.4 in the paper, and the outputs of `src/logical_op_test.py`).

- Veri-QEC can verify a benchmark of 14 kinds of QEC codes. 

II. When revising the experimental results for the QEC code benchmarks, we identified opportunities for updates and improvements. The updates of experimental results include:

1) Results of quantum reed-muller code. We extend the scale of the code to $r = 9$ and verified the correctness of the program implementation for this $[511,1,3]$ code within $\sim 47$ hours. The time consumption is large but it has been the largest code we verified. 


2) Results of Triorthogonal code. We first extend the scale of the code to $r = 64$ and further verify that the distance for $X$ error is $6$ for both codes. 


3) Results of quantum Tanner code. We selected two sets of classical linear codes: the 5-bit repetition code and its dual, as well as the 7-bit Hamming code and its dual. We also choose *bitwuzla* as the SMT solver for Tanner code. We claim that the data in the paper should be updated from two perspectives:
    - For Tanner code constructed with the 5-qubit repetition code Rep5, we verify the exact code distance **$d = 4$** in about **$20.5$** minutes, following the termination condition $4*d * N(ones) + 3 * N(bits) > N$. This matches the results in Table 4. We remove the result with running time being $137$ seconds because the verification condition is not correctly set. The details are illustrated in `Veri-qec/Output/detection/detection_Tanner_Rep5_4.txt`.

    - For Tanner code constructed with the Hamming [7,4,3] code, the upper bound **$d <= 12$** is directly obtained from the construction of logical operators; However, due to the exceedingly large problem size, which surpasses the solvable range of current SMT solvers, we ultimately provide a formally verified lower bound for the code distance, namely **$d >= 4$** and it already takes **$\approx 2$** hours to verify. The details are illustrated in `Veri-qec/Output/detection/detection_Tanner_Ham7_4_4.txt`.

