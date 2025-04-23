
# Research Artifact for Paper 228 'Efficient Formal Verification for Quantum Error Correcting Programs'

## Basic Information
- Artifact: Veri-QEC (A **Verification** tool for **Quantum Error Correcting** Programs)
- Paper Title: Efficient Formal Verification for Quantum Error Correcting Programs
- Submission ID (Track: PLDI 2025 Artifacts): 10
- Zenodo Link: 10.5281/zenodo.15050947

As for the artifact evaluation, we claim for available and reusable badges. If the artifacts do not fulfill the criteria for reusability, we instead request consideration for the functional badge.

As described in the paper, the artifacts include two modules. The first module is a verified verifier for QEC programs, formalized in Coq and built upon the CoqQ library. The second one is a Python-based tool designed to automate the verification for quantum error correction programs. Here is the documentation for the Python-based tool, Veri-QEC.

</br>

## Veri-qec: A prototype tool for automatic verification of quantum error correcting programs

Veri-QEC is a prototype tool designed for automatic verification of quantum error correcting programs. 

We introduce a robust framework for parsing and interpretating quantum error-correcting programs and its associated assertion logic. It then encodes the derived verification conditions into logical formulas. Leveraging SMT solvers building upon a parallel solving framework, the tool efficiently checks the satisfiability of these formulas.


### Getting Started for Evaluation

#### Package lists in Zenodo

Here are the contents of the archive files in Zenodo.

- docker-veriqec.tar: The archive file for the docker environment containing the artifact Veri-qec.

- dirac-project-veriqec.zip: The source codes and Dockerfile for the verified verifier developed in Coq.  

- Veri-qec.zip: The source codes and Dockerfile for Veri-qec along with the output scripts.

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


#### Artifact Usage 

We primarily evaluate the effectiveness of the tool in verifying the following three functionalities for quantum error correcting programs:

- Accurately decode the syndromes and correct the errors (full-verification)
- Accurately correct errors with constraints on the errors (partial-verification)
- Accurately detect all errors (full-verification)

We designed the test scripts from two perspectives: for users wishing to test specific quantum error correction codes, we provide scripts that accept input parameters; to reproduce the experimental results in the paper, we have also integrated the test cases used in the paper into automated test scripts.

**Scripts accept input parameters**

In the scripts that accept input parameters, we use argparse to support the parsing of parameters. The explanations of the parameters can be seen below: 

| **Parameters** | **Explanation**| 
| ---------------| ---------------| 
| --cpucount     |  The number of CPU cores you wish to use | 
| --code         |  The type of the QEC code | 
| --param1 (--p1)  |  Additional Parameter #1 for the QEC code (Optional) |
| --param2 (--p2)  |  Additional Parameter #2 for the QEC code (Optional) | 

For some simple codes, e.g. carbon codes or Steane code additional parameters are not required. For other codes, additional parameters are necessary to determine the exact construction and the code distances. For example, to verify the properties of XZZX codes the distances for Pauli $X$ and Pauli $Z$ errors ($d_x, d_z$) should be provided. 

We recommend starting the evaluation from simple cases, for example the rotated surface codes we used to evaluate the effectiveness of the functionalities of correcting errors. Here are an example illustrating the usage of *Veri-qec*:

```bash
python3 src/execute_verify.py \
--cpucount 16 --code surface --param1 7 
```

To evaluate the results of the first functionality, using the command above and adjust the additional parameter (which is the distance of the surface code) from the set $\{3,5,7,9,11\}$. 

*You can find the detailed output results in the `eval-Output/correction` directory.* The typical output for this example will be (the running time is obtained using 240 cores): 

```
Distance 7:
Task generated. Start checking.
total_job: 4018
tasks for X error: 2009 | tasks for Z error: 2009
verification condition generation time: 0.46747 sec
-----------------
No counterexample found, all errors can be corrected.

All tasks finished, total time for verification: 3.13854 sec
cond_checker_verify took 3.60601 sec
```

The third line illustrates the total subtasks we divide into and the fifth line is the time consumed to parsing and generate the logical formulas. If there are no counterexamples (which means all of the subtasks will output `unsat`), then you'll see the sixths line which reports success. The penultimate line displays the time consumed by invoking the SMT solver to resolve all subtasks; The final line is the total running time for this case. If it takes a relatively long time ($>60s$, or $>300s$, depending on the estimated time cost in total) to finish the check, then we present the phased verification results and the current progress in the following way: 

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

**Automated test scripts**:
We also integrate test cases into four automated test scripts with names starting with `evaluate`, according to the quantitative experiments we carried out in the paper and their results (Figure 4, 6,7 and Table 4). You can reproduce the results simply by running these test scripts. The detailed introduction is postponed to the next section.

#### Finish the evaluation 
You can exit the container by typing `exit`. The test outputs will remain available in `pwd/eval-Output`. You can refer to it for evaluation. Once you have finished all evaluation, you can delete the docker image from the Docker environment:

```bash 
docker rmi docker-veriqec
```
</br>

### Detailed Instructions for Evaluation

In this section we carefully go through the experiments in the paper, and provide guidances on how to reproduce those results. The output of all experiments conducted on your device will be redirected to the `eval-Output` directory. Besides, given that reproducing all experimental results may take a considerable amount of time, we have provided the output scripts from running the experiments on our device in `Output` directory.

#### Claims and Updates for the evaluation results in the paper

The experimental results produced by Veri-QEC can support the following claims mentioned in the paper:

- Veri-QEC can verify the accurate-correction property for all error configurations on surface codes with up to 121 qubits in $\sim 200$ minutes (see `./Output/correction/correction_surface_11.txt`); 

- Veri-QEC can verify the correct-detection property on surface code with distance up to 23; It can detect an counterexample when distance is set to be the real value + 1 for surface codes with distance up to 25 (see `./Output/detection_surface/detection_surface_(23,25).txt`). 

- Veri-QEC can perform partial verification for certain user-provided constraints up to 361 qubits within $\sim 100$ minutes (see `./Output/userprov_constraint/usrprov_comb_19.txt`).

- Veri-QEC can verify simple examples of fault-tolerant gadgets. (See Section 7.4 in the paper, and the outputs of `src/logical_op_test.py`).

- Veri-QEC can verify a benchmark of 14 kinds of QEC codes. (see the results reproduced by `src/evaluate_userprov.py`).

In following sections, we're going to introduce how to reproduce the results that supports those claims. 

#### Accurately correct errors (Figure 4)
The first experiment explores the speedup we achieved in verifying the property of correcting errors accurately. 

- *Evaluation commands*: `python3 src/evaluate_verify.py --cpucount nc`.
- *Output location*: `eval-Output/eval_correction_surface.txt`.
- *Results for reference*: `./Output/correction/correction_surface_{3,5,7,9,11}.txt`
- *Details*: We provide programs to reproduce both baseline results 'sequential' and our results 'parallel'. Please notice that only setting the CPU cores $nc = 1$ cannot obtain the results of 'sequential'. The reason is that although only 1 CPU core is used, this script still divides the whole problem into subtasks and it just sequentially executes these subtasks. The 'sequential' flag means that the logical formula to be checked is viewed as a single task and executed in a single CPU core. You can refer to `src/execute_serial.py` to look at how we implement the baseline method. 

#### Accurately detect errors (Figure 7)
In this experiment we explore the our tool's capability to verifying the detection properties of quantum error correcting codes. We still use the rotated surface code as the benchmark but extend the maximum code distance to 25.

- *Evaluation commands*: `pythonse src/evaluate_detect.py --cpucount nc`
- *Output location*: `eval-Output/eval_detection_surface.txt`.
- *Results for reference*: `./Output/detection_surface`
- *Details*: For each code distance $d$, we verify two properties with different values $d_t$: (1) When $d_t = d$, the code can detect all of the errors with weight $< d_t$; (2) When $d_t = d + 1$, there exist an error with weight $< d_t $ that cannot be detected. The typical outputs are illustrated below:
```
Distance 7
Verifying the correctness when dt = d
Check condition: dx = 7, dz = 7
tasks for X error: 39 | tasks for Z error: 39
total_job: 78
Task generated. Start checking.
verification condition generation time for dt = 7: 1.619 sec <- a
--------------
No counterexample for Z error is found, all errors can be detected.

No counterexample for X error is found, all errors can be detected.
-----------------
All tasks finished, total time for verification: 2.364 sec <- b 
cond_checker_detect took 3.98310 sec <- c
-------------
Detecting counterexamples when dt = d + 1
Check condition: dx = 8, dz = 8
tasks for X error: 33 | tasks for Z error: 33
total_job: 66
Task generated. Start checking.
verification condition generation time for dt = 8: 1.760 sec <-a 
--------------
Counterexample found, there exists Z errors cannot be corrected.

Counterexample Info:

rank: 21 | id: 21 | time: 0.11774206161499023 | result: sat

[0, 0, 0, 0, 0, 0, 1]
num_bit: 7 | num_zero: 6 | num_one: 1 | one_pos: [6]

About to terminate
Time to detect a Z-type error: 0.921 sec <- c1 
------------------
Counterexample found, there exists X errors cannot be corrected.

Counterexample Info:

rank: 65 | id: 65 | time: 0.07342076301574707 | result: sat

[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
num_bit: 17 | num_zero: 17 | num_one: 0 | one_pos: []

About to terminate
Time to detect an X-type error: 0.897 sec <- c2 
---------------
All tasks finished, total time for verification: 1.818 sec <- c
cond_checker_detect took 3.578 sec <- d
```
The basic information, including description and counts for tasks are shown first. Then the time to generate verification condition and subtasks in Figure 6(a) are printed. Afterwards the checking results along with the time consumed in this stage are presented. (*a*: Condition generation time, *b*: Verify time with $d_t = d$, c: Verify time with $d_t = d+1$, *$c_1$*: detect Z error, *$c_2$*: detect X error.) Finally the total time consumed by cond_checker_detect is shown. It is obvious that $a+b \approx d$ and $c = c_1 + c_2$. 

#### Verification using user-provided constraints (Figure 7)
In this experiment we investigate the efficiency improvement when user-provided constraints are imposed. 
- *Evaluation command*: `python3 src/evaluate_userprov.py --cpucount nc`

- *Output location*: `eval-Output/userprov_surface.txt`
- *Results for reference*: `./Output/userprov_constraint`
- *Details*: We use surface code as the benchmark code here. The evaluated code distances for three types of constraints are:

|cstype | distance |
|------- | --------|
| discrete | {3,5,7,9,11} | 
| local | {5,7,9,11,13} | 
| combined | {7,9,11,13,15,17,19} |

If you want to test a single case instead of go through the experiment, you may use the following command:
`python3 src/execute_user_provide.py --cpucount nc --distance d --cstype (your input)`.

#### Benchmarks (Table 4)

During our evaluation of the tool's functionality, we use a total of 14 types of stabilizer codes and their implementations as a benchmark set. We show how to reproduce the results in Table 4.

- *Evaluation command*: `python3 src/evaluate_benchmark.py --cpucount nc`.

- *Output location*: `eval-Output/eval_correction_benchmark.py`, `eval-Output/eval_detection_benchmark.py`

- *Results for reference*: `.Output/correction`, `.Output/detection`. 

- *Details*: Based on the properties of these codes (primarily code distance), we divided them into two categories: Error Correcting codes and Error Detecting codes. Most of the stabilizer codes can detect and correct errors below certain thresholds; these codes often have odd code distances to saturate the upper bound of correctable errors; typical examples are surface codes (and the variants) and quantum reed-muller code. Error Detecting codes, for example the basic [8,3,2] color code or the campbell-howard code have even code distance (for Z error, it is $2$), indicating that they can only detect a single Pauli $Z$ error but are not capable of determining the locations and correct it. For these codes along with some codes with even code distances, we tend to verify their abilities to detect certain number of errors. 

We list the benchmarks of codes and properties we aim to verify for them in the table below. For scalable codes with svariable parameters we provide the general forms. 

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

If you do not want to go through all of the candidate codes like what we did in `evaluate_benchmark.py`, you could use the following commands to verify a single instance of QEC codes.

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

#### Evaluation for examples of fault-tolerant gadgets (Figure 9 & 10)
Our tool supports the verification of simple fault-tolerant gadgets, with or without propagated errors from the previous QEC cycle. We choose the logical GHZ state preparation (without propagated errors) and a logical CNOT gate (with propagated errors) as the examples. To see the results, you can execute the following command:
```bash 
python3 src/logical_op_test.py
```

#### Updates compared with the submitted version of the paper

When revising the experimental results for the QEC code benchmarks, we identified opportunities for updates and improvements. The updates of experimental results include:

1) Results of quantum reed-muller code. We extend the scale of the code to $r = 9$ and verified the correctness of the program implementation for this $[511,1,3]$ code within $\sim 47$ hours. The time consumption is large but it has been the largest code we verified. 

2) Results of Triorthogonal code. We first extend the scale of the code to $r = 64$ and further verify that the distance for $X$ error is $6$ for both codes. 

3) Results of quantum Tanner code. We selected two sets of classical linear codes: the 5-bit repetition code and its dual, as well as the 7-bit Hamming code and its dual. We also choose *bitwuzla* as the SMT solver for Tanner code. We claim that the data in the paper should be updated from two perspectives:

    - For Tanner code constructed with the 5-qubit repetition code (Rep5), we verify the code distance **$d = 4$** in about **$20.5$** minutes, following the termination condition $4*d * N(ones) + 3 * N(bits) > N$. This matches the results in Table 4. We remove the result with running time being $137$ seconds because the verification condition is not correctly set. The details are illustrated in `./Output/detection/detection_Tanner_Rep5_4.txt`.

    - For Tanner code constructed with the Hamming [7,4,3] code (Ham7), the upper bound **$d <= 12$** is directly obtained from the construction of logical operators; However, due to the exceedingly large problem size, which surpasses the solvable range of current SMT solvers, we ultimately provide a formally verified lower bound for the code distance, namely **$d >= 4$** and it already takes **$\approx 2$** hours to verify. The details are illustrated in `./Output/detection/detection_Tanner_Ham7_4_4.txt`.


### Instructions on adding new codes
Our artifact supports verification of user-defined codes. You can follow this instruction to add a new code to the dataset and verify it. Try yourself!

Generally speaking, define/add a new code requires two types of information: the parity-check matrix (a binary matrix encoding its stabilizers and logical operators) and the supposed code distance. If users want to define a new code, we provide interfaces for the following two scenarios separately:

- The user knows the construction of the code with respect to some parameters (for example, the stabilizers of surface code with respect to distance $d$). In this case they can define a customized function to mathematically describe the code, similar to what we've done in qldpc_codes.py and special_codes.py. Then they can invoke cond_checker to verify if the supposed code distance satisfies the properties.

- The user is aware of the matrix of a specific instance of this code. We provide a sample interface in `src/execute_verify.py`, which supports direct matrix reading from a file. The user will be asked to provide the file path of the matrix and the code distances to be verified.

Moreover, the efficiency of SMT solver depends heavily on how we divide the problem to be checked into subtasks. Too many subtasks will lead to overflows; Too few subtasks can make it exceedingly difficult for the solver to address an individual problem. If you encounter each of these issues, you can try to adjust the termination condition by yourself. We provide the termination condition in the `easy_enough` member function of the `subtask_generator` class. You can adjust the coefficients of `assigned_one_num` and `assigned_bit_num` to adjust the number of subtasks. For large codes, we recommend an average run time $0.5s$ to $10s$ for each instance. W