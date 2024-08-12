# Development Logs 

## Introduction
本文档用于记录工具开发过程中已完成的模块，以及尚未支持的部分，


## Functions and todo lists 
记录实现逻辑推理系统时所需用到的自定义变换函数，目前共支持5类
### Assignment

### Unitary
Currently support the inference rules of Pauli operations with conditions, and Hadamard / Phase gates without control. 

Todo: 1. 尝试将pauli string改为01串写法（1. 2-bit描述+1-bit index/2. 2n-bit串描述stabilizers，不需要位置信息，倾向于前一种），并实现带conditional的pauli 规则
### Measurement
需要处理big operators (目前主要是big or) 

big and 的应用场景在不再需要指定stabilizer具体值之后可用于简化assertion的形式

measurement rule 的实现过程中可能依赖判断2个stabilizer expression是否相等（分成2部分，相位+pauli string）
Todo: 实现big-or的版本 (7.4 已完成)

### For (syntactic sugar)
针对For循环中存在下标为循环变量的情况编写了loops transformer，将下标逐个进行替换之后按照串行的方案执行程序对应的替换规则

可能存在的提升空间：目前所有的inference都是串行执行，是否能找到并行执行的操作方法以及判定某个循环内的程序是否可以并行执行。

---------------------


## Problems and possible solutions 
1. 目前不支持类似 s_1 := meas g_1 的写法， 需要具体指定stabilizer的值。solution: 

2. 目前不支持在Clifford（非Pauli）的门操作中加入conditional gates

## Development Targets and Plans