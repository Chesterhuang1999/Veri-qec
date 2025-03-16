<!-- This is the documentation for the artifacts attached to the paper 'Efficient Formal Verification of Quantum Error Correcting Programs'. As introduced in the paper, the artifacts include two modules, a verified verifier in Coq and an automatic verifier, Veri-QEC in Python. -->
# Veri-qec: A prototype tool for automatic verification of quantum error correcting programs

## Basic Information
- Artifact: Veri-QEC (A **Verification** tool for **Quantum Error Correcting** Programs)
- Paper Title: Efficient Formal Verification for Quantum Error Correcting Programs
- Submission ID (Track: PLDI 2025 Artifacts): 10
- Zenodo Link: 

Veri-QEC is a prototype tool designed for automatic verification of quantum error correcting programs. 
<!-- As outlined in the paper, the artifacts include two modules, a verified verifier in Coq an an automatic verifier, Veri-QEC in Python.  -->
We introduce a robust framework for parsing and interpretating quantum error-correcting programs and its associated assertion logic. It then encodes the derived verification conditions into logical formulas. Leveraging SMT solvers building upon a parallel solving framework, the tool efficiently checks the satisfiability of these formulas.


## Getting Started for Evaluation


### Preparation for docker container
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
After obtaining the number of CPU cores in your machine, you can load the docker image and start the evaluation.

For Linux/ MacOS: 
```bash
docker load < docker/docker-veriqec-image
```
PowerShell: 
```bash
docker load -i docker\docker-veriqec-image
```

Execute the following commands to start the docker container, enter the bash environment and load the directory of the output results:

For Linux/MacOS with bash: 
```bash 
docker run -v `pwd`/eval-Output: /Veri-qec/eval-Output --rm -it docker-veriqec
```
Powershell:
```bash
docker run -v ${PWD}$ /eval-Output: /Veri-qec/eval-Output --rm -it docker-veriqec
```

`-v` options mounts the `eval-Output` folder in the current directory to the corresponding directory within the docker container, while `--rm` creates a container that will be deleted once exit. Through this you can view the evaluation results even when the container is closed. 

We set the default working directory to be `/Veri-qec/` and you can use `pwd` at the initial interface to verify whether the working directory is correct.



### Artifact Usage 

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

To evaluate the results of the first functionality, using the command above and adjust the additional parameter (which is the distance of the surface code) from the set $\{3,5,7,9,11\}$. The typical output for this example will be : 

```bash 
Task generated. Start checking.
total_job: 4018
task generation time: 0.46747398376464844
No counterexample found, all errors can be corrected.

Finish all jobs. Checking time: 3.138540744781494
cond_checker took 3.611sec
```
The second line illustrates the total subtasks we divide and the third line is the time consumed to parsing and generate the logical formulas. If there are no counterexamples (which means all of the subtasks will output `unsat`), then you'll see the fourth line which reports success. The final line displays the time taken by the solver to resolve all subtasks. If it takes a relatively long time ($>10s$, or $>60s$, depending on the estimated time cost in totla) to finish the check, then we present the phased verification results and the current progress in the following way:

```bash 
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
```bash
There exists a counterexample for X error:

rank: 719 | id: 719 | time: 0.053060293197631836 | result: sat

[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]
num_bit: 11 | num_zero: 8 | num_one: 3 | one_pos: [8, 9, 10]
```

It may take a long time ($\approx 19.25$ CPU days or $\approx 24$ hours for a 16-core CPU) to reproduce the result when the code distance equals to $11$, so you may refer to the `/Output/` directory for the experimental results for all of the benchmark codes while waiting for the results.

You can exit the container by typing `exit`. The test outputs will remain available in `pwd/eval-Output`. You can refer to it for evaluation. Once you have finished all evaluation, you can delete the docker image from the Docker environment:

```bash 

```
## Detailed Instructions for Evaluation


### Benchmarks 
During our evaluation of the tool's functionality, we use a total of 14 types of stabilizer codes and their implementations. Based on their properties (primarily code distance), we divided them into two categories: Error Correcting codes and Error Detecting codes. Most of the stabilizer codes can detect and correct errors below certain thresholds; these codes often have odd code distances to saturate the upper bound of correctable errors; typical examples are surface codes (and the variants) and quantum reed-muller code. Error Detecting codes, for example the basic [8,3,2] color code or the campbell-howard code have even code distance (for Z error, it is $2$), indicating that they can only detect a single Pauli $Z$ error but are not capable of determining the locations and correct it. For these codes along with some codes with even code distances, we tend to verify their abilities to detect certain number of errors. 
<!-- There are also some codes whose exact code distances are not straightforward; to advance in identifying and verifying the precise code distances of these codes, we also  -->

We list the benchmarks of codes and properties we aim to verify for them in the table below. For scalable codes with svariable parameters we provide the general forms. 

<!-- - Error Correcting Properties:

| Codes | Surfaces code | 
| ------ | -----------|  -->


<script id="MathJax-script" src="https://cdn.bootcss.com/mathjax/3.0.5/es5/tex-mml-chtml.js"></script>
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
    <td>[$d^2$, 1, d]</td>
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
      <td> [2^r] </td>
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

For Hypergraph product code and quantum Tanner code we fix the clessical 
The default parameters for 
### Updates for the evaluation results in the paper
