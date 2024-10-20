import time
import subprocess
from enum import Enum, auto
from collections import deque

def linxi_debug(func):
    def wrapper(*args, **kwargs):
        print("Function started: ", func.__name__)
        result = func(*args, **kwargs)
        print("Function ended: ", func.__name__)
        return result
    return wrapper


class NodeStatus(Enum):
    unsolved = auto()
    solving = auto()
    solved = auto()
    terminated = auto()
    error = auto()
    
    def is_unsolved(self):
        return self == NodeStatus.unsolved
    
    def is_solving(self):
        return self == NodeStatus.solving
    
    def is_solved(self):
        return self == NodeStatus.solved
    
    def is_terminated(self):
        return self == NodeStatus.terminated
    
    def is_ended(self):
        return self.is_solved() or self.is_terminated()

class NodeSolvedReason(Enum):
    # by
    itself = auto()
    ancester = auto()
    children = auto()

class ParallelNode:
    def __init__(self, id, parent, remained_qubit_num, remained_one_num, err_vals, make_time):
        self.assign_to = None
        self.time_infos = {}
        self.children = []
        self.status: NodeStatus
        
        self.id = id
        self.parent = parent
        self.remained_qubit_num = remained_qubit_num
        self.remained_one_num = remained_one_num
        self.err_vals = err_vals
        
        if parent != None:
            parent: ParallelNode
            parent.children.append(self)
        
        self.update_status(NodeStatus.unsolved, 
                           NodeSolvedReason.itself, 
                           make_time)

    def update_status(self, status, reason, current_time):
        self.time_infos[status] = current_time
        self.status = status
        self.reason = reason
        # logging.debug(f'node-{self.id} is {status} by {reason}')
    
    def __str__(self) -> str:
        if self.parent == None:
            parent_id = -1
        else:
            parent_id = self.parent.id
        ret = f'id: {self.id}'
        ret += f', parent: {parent_id}'
        ret += f', status: {self.status}'
        ret += f', reason: {self.reason}\n'
        ret += f'children: {[child.id for child in self.children]}\n'
        ret += f'time-infos: {self.time_infos}\n'
        ret += f'err_vals: {self.err_vals}\n'
        return ret
    
    def get_solve_start_time(self):
        return self.time_infos.get(NodeStatus.solving, None)
    
    def can_reason_solved(self):
        if len(self.children) == 0:
            return False
        for child in self.children:
            child: ParallelNode
            if not child.status.is_solved():
                return False
        return True

class ParallelTree:
    def __init__(self, distance, num_qubits, start_time):
        self.nodes = []
        self.result = NodeStatus.unsolved
        self.root = None
        
        self.start_time = start_time
        self.distance = distance
        self.num_qubits = num_qubits
        
        self.solvings = []
        self.waitings = deque()
        self.unpartitions = deque()
        self.solved_number = 0
        self.total_solve_time = 0.0
        self.average_solve_time = 0.0

    def get_current_time(self):
        return time.time() - self.start_time
    
    def is_done(self):
        return self.result.is_solved()
    
    def get_result(self):
        return self.result
    
    def update_node_status(self, node: ParallelNode,
                           status: NodeStatus,
                           reason: NodeSolvedReason):
        current_time = self.get_current_time()
        node.update_status(status, reason, current_time)
    
    def make_node(self, parent, remained_qubit_num, remained_one_num, err_vals):
        id = len(self.nodes)
        node = ParallelNode(id, parent, remained_qubit_num,
                            remained_one_num, err_vals, self.get_current_time())
        self.nodes.append(node)
        self.waitings.append(node)
        self.unpartitions.append(node)
    
    # def is_easy_enough(self, node: ParallelNode, is_solve: True):
    # hard enough to partition
    def is_worth_partition(self, node: ParallelNode):
        remained_qubit_num, remained_one_num = node.remained_qubit_num, node.remained_one_num
        if remained_qubit_num == 1:
            return False
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num
        # k is greater and the task is harder
        # solve begin harder and partition begin
        # if is_solve:
        #     k = 2.0
        # else:
        #     # is partition
        #     k = 1.5
        # if k * assigned_one_num * self.distance + assigned_bit_num < self.num_qubits:
        estimate_assigned = 2 * assigned_one_num * self.distance + assigned_bit_num
        if estimate_assigned > self.num_qubits:
            # too easy
            return False
        return True
    
    def is_easy_to_solve(self, node: ParallelNode):
        remained_qubit_num, remained_one_num = node.remained_qubit_num, node.remained_one_num
        if remained_qubit_num == 1:
            return True
        assigned_one_num = (self.distance - 1) - remained_one_num
        assigned_bit_num = self.num_qubits - remained_qubit_num
        estimate_assigned = 3 * assigned_one_num * self.distance + assigned_bit_num
        if estimate_assigned > self.num_qubits:
            return True
        return False
    
    def is_too_easy(self, node: ParallelNode):
        return node.remained_qubit_num == 1 or node.remained_one_num == 0
    
    def get_next_unpartitioned(self):
        while len(self.unpartitions) > 0:
            node: ParallelNode = self.unpartitions[0]
            if node.status.is_solved():
                self.unpartitions.popleft()
                continue
            if self.is_too_easy(node):
                self.unpartitions.popleft()
                continue
            # if not self.is_easy_enough(node, False):
            if self.is_worth_partition(node):
                self.unpartitions.popleft()
                return node
            # return None
            solving_time = self.get_node_solving_time(node)
            if solving_time == None or solving_time < 5.0:
                return None
            else:
                # print(f'solving_time: {solving_time}')
                self.unpartitions.popleft()
                return node
        return None
    
    def partition_node(self, node: ParallelNode):
        if node.remained_qubit_num > 1:
            self.make_node(node, node.remained_qubit_num - 1, node.remained_one_num, node.err_vals + [0])
            if node.remained_one_num > 0:
                self.make_node(node, node.remained_qubit_num - 1, node.remained_one_num - 1, node.err_vals + [1])
    
    # @linxi_debug
    def get_next_waiting_node(self):
        while True:
            if len(self.waitings) == 0:
                node = self.get_next_unpartitioned()
                if node == None:
                    return None
                self.partition_node(node)
            else:
                node: ParallelNode = self.waitings.popleft()
                if node.status.is_solved():
                    continue
                # if self.is_easy_enough(node, True):
                # if self.is_easy_enough(node):
                #     return node
                if self.is_easy_to_solve(node):
                    return node
        # return None
    
    def get_solving_number(self):
        return len(self.solvings)
    
    def get_node_number(self):
        return len(self.nodes)
    
    # # precond: node is solving
    # # terminate: unsolved or solving
    def terminate_node(self, node: ParallelNode):
        print(f'terminate node-{node.id}, {node.err_vals}')
        self.update_node_status(node, 
                    NodeStatus.terminated, 
                    NodeSolvedReason.itself)
        if node.assign_to != None:
            node.assign_to.terminate()
            node.assign_to = None
    
    def get_node_solving_time(self, node: ParallelNode):
        solve_start_time = node.get_solve_start_time()
        if solve_start_time == None:
            return None
        return self.get_current_time() - solve_start_time
    
    def propagate_node_solved(self,
            node: ParallelNode,
            reason: NodeSolvedReason):
        self.update_node_status(node, 
                                NodeStatus.solved, 
                                reason)
        if node.assign_to != None:
            node.assign_to.terminate()
            node.assign_to = None
    
    # @linxi_debug
    def solved_push_up(self, node: ParallelNode):
        if node.status.is_solved():
            return
        if node.can_reason_solved():
            self.propagate_node_solved(node, NodeSolvedReason.children)
            if node.parent != None:
                self.solved_push_up(node.parent)
    
    # @linxi_debug
    def solved_push_down(self, node: ParallelNode):
        if node.status.is_solved():
            return
        self.propagate_node_solved(node, NodeSolvedReason.ancester)
        for child in node.children:
            self.solved_push_down(child)
    
    def node_solved(self,
            node: ParallelNode):
        self.update_node_status(node,
                NodeStatus.solved,
                NodeSolvedReason.itself)
        
        solve_time = self.get_node_solving_time(node)
        self.total_solve_time += solve_time
        self.solved_number += 1
        self.average_solve_time = self.total_solve_time / self.solved_number
        
        if node.parent != None:
            self.solved_push_up(node.parent)
        if self.root.status.is_solved():
            self.result = NodeStatus.solved
            return
        for child in node.children:
            self.solved_push_down(child)
    
    def assign_node(self, node: ParallelNode, p: subprocess.Popen):
        assert(node.assign_to == None)
        node.assign_to = p
        node.update_status(NodeStatus.solving,
                           NodeSolvedReason.itself,
                           self.get_current_time())
        self.solvings.append(node)
    
    def _output_tree(self, node: ParallelNode):
        print(node)
        for child in node.children:
            self._output_tree(child)
        
    def output_tree(self):
        self._output_tree(self.root)
        
