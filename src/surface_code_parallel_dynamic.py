import os
import time
from timebudget import timebudget

import subprocess

from parallel_tree import NodeStatus, ParallelNode, ParallelTree
import json

class ParallelSolver:
    def __init__(self, distance, max_proc_num) -> None:
        self.start_time = time.time()
        self.result = NodeStatus.solving
        
        self.distance = distance
        self.max_proc_num = max_proc_num
        
        self.num_qubits = distance ** 2
        
        script_path = os.path.abspath(__file__)
        script_dir = os.path.dirname(script_path)
        
        self.seq_checker_path = f'{script_dir}/surface_code_partition.py'
    
    def check_subprocess_status(self, p: subprocess.Popen):
        rc = p.poll()
        if rc == None:
            return NodeStatus.solving
        
        # if rc != 0:
        #     return NodeStatus.error
        out_data, err_data = p.communicate()
        if rc != 0:
            print(f'out_data: {out_data}')
            print(f'err_data: {err_data}')
            assert(False)
        
        return NodeStatus.solved
        
    def is_done(self):
        if self.result.is_solved():
            return True
        if self.tree.is_done():
            self.result = NodeStatus.solved
            return True
        return False
    
    # True for still running
    def check_solving_status(self, node: ParallelNode):
        if not node.status.is_solving():
            return False
        # print(f'check node-{node.id}, {node.err_vals}')
        sta: NodeStatus = self.check_subprocess_status(node.assign_to)
        if sta.is_solving():
            return True
            ### TBD ###
            # if self.need_terminate(t):
            #     self.update_task_status(t, 'terminated')
            #     self.terminate_task(t)
            #     self.sync_ended_to_partitioner()
            #     return False
            # else:
            #     return True
        node.assign_to = None
        print(f'{self.tree.get_node_solving_time(node)}, node-{node.id} solved, {node.err_vals}')
        self.tree.node_solved(node)
        if self.is_done():
            return False
        return False
    
    def check_solvings_status(self):
        still_solvings = [] 
        for node in self.tree.solvings:
            node: ParallelNode
            if not node.status.is_solving():
                continue
            if self.check_solving_status(node):
                still_solvings.append(node)
            else:
                if self.is_done():
                    return True
        self.tree.solvings = still_solvings
        return False
    
    def solve_node(self, node: ParallelNode):
        # instance_path = f'{self.solving_folder_path}/task-{node.pid}.smt2'
        # cmd_paras = [f'python3 {self.seq_checker_path}',
        #         f'--distance {self.distance}',
        #         f'--err-vals "{json.dumps(node.err_vals)}"'
        #     ]
        # cmd = ' '.join(cmd_paras)
        # print(cmd)
        cmd_paras = ['python3', f'{self.seq_checker_path}',
                '--distance', f'{self.distance}',
                '--err-vals', f'{json.dumps(node.err_vals)}'
            ]
        p = subprocess.Popen(
                cmd_paras,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
        self.tree.assign_node(node, p)
        print(f'solve-node {node.id}, {node.err_vals}')
    
    def process_waiting_tasks(self):
        # cnt = 0
        while len(self.tree.solvings) < self.max_proc_num:
            node = self.tree.get_next_waiting_node()
            if node == None:
                break
            self.solve_node(node)
            # print(f'solvings: {len(self.tree.solvings)}')
            # cnt += 1
            # if cnt >= self.max_proc_num // 2:
            #     break
    
    def init_parallel_tree(self):
        self.tree = ParallelTree(self.distance, self.num_qubits, self.start_time)
        self.tree.make_node(None, self.num_qubits, self.distance - 1, [])
        self.tree.root = self.tree.nodes[0]
    
    @timebudget
    def __call__(self):
        self.init_parallel_tree()
        while True:
            if self.check_solvings_status():
                break
            self.process_waiting_tasks()

def analysis_task(task_id: int, task: list):
    num_bit = 0
    num_one = 0
    one_pos = []
    for i, bit in enumerate(task):
        if bit == 1:
            num_one += 1
            one_pos.append(i)
        num_bit += 1
    num_zero = num_bit - num_one
    info = [f'num_bit: {num_bit}', f'num_zero: {num_zero}', f'num_one: {num_one}', f'one_pos: {one_pos}']
    return [task_id, task, info]

if __name__ == "__main__":
    distance = 7
    max_proc_num = 100
    ps = ParallelSolver(distance, max_proc_num)
    ps()
