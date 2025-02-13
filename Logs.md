# Development Logs 

## Introduction
本文档用于记录工具开发过程中已完成的模块，以及尚未支持的部分，


## Functions for implementing the proof system
记录实现逻辑推理系统时所需用到的自定义变换函数，目前共支持5类
### Assignment

### Unitary
Currently support the inference rules of Pauli operations with conditions, and Hadamard / Phase gates without control. 

Todo: 1. 尝试将pauli string改为01串写法（1. 2-bit描述+1-bit index/2. 2n-bit串描述stabilizers，不需要位置信息，倾向于前一种），并实现带conditional的pauli 规则 （更新：7.15已经全面对程序使用写法1进行修改）
### Measurement
由于measurement rule产生的precondition是subspace，因此需要bigor operator来对此进行记录，measure函数实现了 1；对于一个measure，检查断言中是否已经包含该operator，如是则直接修改对应相位，不含则在断言中加入该operator。2. 考察assertion本身是否为bigor的形式，若是则加入一个新的symbol记录当前测量结果，若否则创建一个Or operator

big and 的应用场景在不再需要指定stabilizer具体值之后可用于简化assertion的形式，会在转化经典逻辑的时候使用到

measurement rule 的实现过程中可能依赖判断2个stabilizer expression是否相等（分成2部分，相位+pauli string）
Todo: 实现big-or的版本 (7.4 已完成) 

### For (syntactic sugar)
针对For循环中存在下标为循环变量的情况编写了loops transformer，将下标逐个进行替换之后按照串行的方案执行程序对应的替换规则

可能存在的提升空间：目前所有的inference都是串行执行，是否能找到并行执行的操作方法以及判定某个循环内的程序是否可以并行执行。

---------------------

## Roadmap for SMT encoding

### Step1: Checking the commuting properties of assertions (intra)
Finished 7.17: Checking by the indexes and zx number for each Pauli operator
### Step2: Find the equations for phases by find the multiplication of generators
Finished 7.19: Greedy search for the multiplicative representations of stabilizers in generated preconditions, using the stabilizers in provided preconditions. 
### Step3: Encode the generated conditions into SMT-LIB files. 
Finished 7.29. 
Technical details: 
1. Construct all of the variables as bitvectors with width = $\log_2 n$ to avoid type incompatibility and add constraints to limit the variables in \{0,1\}
2. Divide the decoding condition $P_f$ into 2 parts: integer and boolean parts, to deal with '+' respectively. In boolean part '+' is treated as xor since all the variables are 01 bit vectors
3. 
## Problems and possible solutions 
1. 目前不支持类似 s_1 := meas g_1 的写法， 需要具体指定stabilizer的值。solution: 

2. 目前不支持在Clifford（非Pauli）的门操作中加入conditional gates （已经解决）

## Development Targets and Plans

目前按照优先级，任务大小从高到低排列：
1. Try to optimize the z3 smt encoding, variable's bitwidth should = 1 and reconstruct the integer addition (maybe full adder is prefered)
2. Find benchmarks of stabilizer codes and convert to programs and assertions 
3. Implement the cnot rules for substituting pauli operators
4. Try 01 integer programming tools, like Gurobi







## 10.24 Update 

### Current methods that are not good enough in codes
1. VCgeneration, include measurement error


## 2025.1.26 Update:

### Verifier
1. Build the algorithm in Section 5.1 by first generating matrix representations of pre and postconditions.
2. Find the linear transformation between two matrices by Gaussian elimination on the augmented matrices.
3. Operate the linear transformation matrix on the phases of precondition, thus obtaining the classical assertion. 

This avoids using greedy search and multiply the stabilizer generators many times and match one by one. 

### Logical T gate Implementation (1.26)
1. Prove that the circuit (first CNOT $q_1q_i$ and CNOT $q_iq_1$ then physical T $q_1$, at last CNOT $q_iq_1$ and CNOT $q_1q_i$ for all i > 1) indeed makes a logical T gate under Steane and surface codes
2. Build the grammar for additive Pauli predicates. To avoid ambiguity, all of the terms are expanded using law of distribution, making the predicate in the form of (P1+P2+P3), in which Pis are all Pauli string with phases. 

3. Established the transformation rules for physical T gate. 


Update in code:
1. Grammar. Define additive Pauli predicates and reduce the predicates to canonical form using law of distribution. Moreover, use QR2[a,b,c] to denote a number in $\mathbb{Z}[\frac{1}{\sqrt{2}}]$, that is $\frac{1}{2^a}(b + c\sqrt{2})$
2. Transformer: Implemented the physical T gate (fault-free version) using the notation for QR2.