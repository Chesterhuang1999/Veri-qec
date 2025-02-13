import numpy as np
import time
import math
from collections import defaultdict
import sys

# from ..parser_qec import get_parser

import re
from ..Dataset import special_codes, qldpc_codes
##
# from encoder import *

class Program:
    def __init__(self, code, circuit, Np, Nlog, iserr, rounds = 1):
        self.code = code
        self.codetype = 'surface'
        self.Np = Np ## Number of physical qubits
        self.isLogical = True
        self.Nlog = Nlog ## Number of logical qubits
        
        self.isError = iserr 
        self.isProp = False
        self.round = rounds ## Rounds of each qec cycle, default 1
        
        self.circuit = circuit ## Logical circuit to be implemented
        k = code.shape[0] - Np
        assert Nlog % k == 0, f"Number of logical qubits should be divided by logical qubits in a single code"


    ### decompose the logical circuit layer by layer
    def decompose_circuit(self):
        circ = self.circuit
        layers = []

        return layers

    ### generate the physical implementation of logical circuit (a single layer)
    def gen_logical_prog(self, gateinfo):
        prog_parts_log = []
        # prog_parts_x, prog_parts_z = [], []
        numq = self.Np
        for i in range(len(gateinfo)):
            gate, inds = gateinfo[i]
            if gate == 'CNOT':
                assert len(inds) == 2, f"Error: Invalid target qubits for S gate"
                k, l = inds[0], inds[1]
                if self.codetype in ('surface', 'steane'):
                    for i in range(numq):
                        q1 = (k - 1) * numq + i + 1
                        q2 = (l - 1) * numq + i + 1
                        prog_parts_log.append(f"q_({q1}), q_({q2}) *= CNOT")
                # elif code == '':
            elif gate == 'H':
                assert len(inds) == 1
                k = inds[0]
                if self.codetype in ('surface', 'steane'):
                    for i in range(numq):
                        q = (k - 1) * numq + i + 1
                        prog_parts_log.append(f"q_({q}) *= H")
            elif gate == 'S':
                assert len(inds) == 1, f"Error: Invalid target qubits for S gate"
                k = inds[0]
                for i in range(numq):
                    q = (k - 1) * numq + i + 1
                    prog_parts_log.append(f"q_({q}) *= Z")
                    prog_parts_log.append(f"q_({q}) *= S")
        prog_log =  ';'.join(prog_parts_log)
        return prog_log
        # layers = self.decompose_circuit()
        # circ = self.circuit


    ### Generate the QEC program after each logical operation
    def gen_qec_prog(self):
        # if rnd is not None:
        #     self.round = rnd
        rnd = self.round
        prog_parts_z = []
        prog_parts_x = []
        # start = rnd * N * n 
        n = self.Np
        k = self.code.shape[0] - self.Np
        
        spx = defaultdict(list)
        spz = defaultdict(list)
        for ind in range(n):
            qbase = n * ind
            sbase = (n - k) * ind
            for i in range(n - k):
                if (np.all(self.code[i,:n] == 0) == False):
                    for j in range(n):
                        if self.code[i][j] == 1:
                            spx[i + sbase].append(f"(0,1,{j + 1 + qbase})")
                if (np.all(self.code[i,n:] == 0) == False):
                    for j in range(n):
                        if self.code[i][j + n] == 1:
                            spz[i + sbase].append(f"(1,0,{j + 1 + qbase})")
        
        err_ind_start = rnd * self.Nlog * n
        corr_ind_start = rnd * self.Nlog * n
        meas_ind_start = rnd * self.Nlog * (n-k)
        prog_parts_z.append(f"for i in 1 to {n * self.Nlog} do q_(i) *= ex_(i + {err_ind_start}) X end;")
        prog_parts_x.append(f"for i in 1 to {n * self.Nlog} do q_(i) *= ez_(i + {err_ind_start}) Z end;")
        for cnt, sinfo in spx.items():
            smeas_x = f"s_({cnt + 1 + meas_ind_start}) := meas" + ''.join(sinfo) + ";"
            prog_parts_x.append(smeas_x)
            prog_parts_z.append(smeas_x)
        for cnt, sinfo in spz.items():
            smeas_z = f"s_({cnt + 1 + meas_ind_start}) := meas" + ''.join(sinfo) + ";"
            prog_parts_x.append(smeas_z)
            prog_parts_z.append(smeas_z)
        prog_parts_z.append(f"for i in 1 to {n * self.Nlog} do q_(i) *= cx_(i + {corr_ind_start}) X end")
        prog_parts_x.append(f"for i in 1 to {n * self.Nlog} do q_(i) *= cz_(i + {corr_ind_start}) Z end")
        
        return ''.join(prog_parts_x), ''.join(prog_parts_z)
    
    def output(self):
        gates = self.decompose_circuit()
        prog_log_parts = []
        ## Fault-free implementation of the logical circuit
        if self.isError == False:
            
            for ind, gateinfo in gates.items():
                prog_log = self.gen_logical_prog(gateinfo)
                prog_log_parts.append(prog_log)
            
            prog_logical = ';'.join(prog_log_parts)
            return prog_logical
            
        else:
            prog_parts_x = []
            prog_parts_z = []
            err_gt_x = []
            err_gt_z = []
            # print(len(gates))
            for ind, gateinfo in gates.items():
                totq = self.Nlog * self.Np
                if ind >= 0:
                    
                    prog_parts_z.append(f"for i in 1 to {self.Np} do q_(i) *= px_(i) X end")
                    prog_parts_x.append(f"for i in 1 to {self.Np} do q_(i) *= pz_(i) Z end")
                    err_gt_x.append(f"sum i 1 {self.Np} (pz_(i)) <= 1")
                    err_gt_z.append(f"sum i 1 {self.Np} (px_(i)) <= 1")
                prog_parts_x.append(prog_log)
                prog_parts_z.append(prog_log)
                prog_qec_x, prog_qec_z = self.gen_qec_prog()
                prog_parts_z.append(prog_qec_z)
                prog_parts_x.append(prog_qec_x)


            self.xprog, self.zprog = ';'.join(prog_parts_x), ';'.join(prog_parts_z)
            err_gt_x = ' && '.join(err_gt_x)
            err_gt_z = ' && '.join(err_gt_z)
        return self.xprog, self.zprog, err_gt_x, err_gt_z


class Assertion:
    ### Pre and post condition generations
    def __init__(self, code, Np, Nlog, rounds = 1):
        self.code = code
        self.Np = Np
        self.Nlog = Nlog

        self.isError = True

    def stab_cond_gen(self):