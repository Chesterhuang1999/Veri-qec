from verifier import *
from parser_qec import *
from condition_multiq import *
import numpy as np
from copy import deepcopy
from lark import Transformer, Token, Tree
# from transformer import precond_generator, recon_string
import sys
import time
sys.setrecursionlimit(10**7)


class add_comparison(Transformer):
    def __init__(self, base, stabs):
        self.child = base.children[0].children
        self.stabs = stabs
    def eq_sexpr(self, sexp1, sexp2):
        for i in range(len(sexp1.children)):
            if sexp1.children[i] != sexp2.children[i]:
                return False
        return True
      
    def row_xor(self, row1, row2):
        return [row1[i] ^ row2[i] for i in range(len(row1))]
    def exist_match(self, E, F):
        k1, k2 = E.shape[0], F.shape[0]
        assert k1 == k2
        candidate_g = [self.row_xor(E[0], F[i]) for i in range(k2)]    
        F_counts = {}
        for i in range(k2):
            row_tuple = tuple(F[i,:])
            F_counts[row_tuple] = F_counts.get(row_tuple, 0) + 1
        for i in range(k2):
            candidate_g = self.row_xor(E[0], F[i]) 
            valid = True
            F_counts_copy = F_counts.copy()
            for j in range(k1):
                f_trial = tuple(self.row_xor(E[j], candidate_g))
                if F_counts_copy.get(f_trial, 0) > 0:
                    F_counts_copy[f_trial] -= 1
                else:
                    valid = False 
                    break
            if valid:
                return candidate_g
        return []
    def pterm(self, args):
        if len(args) != len(self.child):
            return Tree('false', [])
        elif len(args) == 1:
            if eq_pexpr(args[0], self.child[0]):
                return Tree('true', [])
            else:
                return Tree('false', [])
            
        else:
            ### Judge whether base = g * args
            stab_mat_rep = canonical_form(self.stabs)[0]
            n1 = stab_mat_rep.shape[1]
            rank_stab = np.linalg.matrix_rank(stab_mat_rep)
            pexp_set1 = [args[2*i + 1] for i in range(len(args)//2)]
            pexp_set2 = [self.child[2*i + 1] for i in range(len(args)//2)]
            log_mat_rep1 = canonical_form(pexp_set1)[0]
            log_mat_rep2 = canonical_form(pexp_set2)[0]
            k, n = log_mat_rep1.shape
            log_mat_rep1 = np.concatenate((log_mat_rep1, np.zeros((k, n1 - n), dtype = int)), axis = 1)
            log_mat_rep2 = np.concatenate((log_mat_rep2, np.zeros((k, n1 - n), dtype = int)), axis = 1)
            result_stab = np.array(self.exist_match(log_mat_rep1, log_mat_rep2)).reshape(1, n1)
            stab_mat_trial = np.concatenate((stab_mat_rep, result_stab), axis = 0)
            rank_stab_trial = np.linalg.matrix_rank(stab_mat_trial)
            # print(result_stab)
            if len(result_stab) == 0 or rank_stab_trial != rank_stab:
                return Tree('false', [])
            else:
                log_mat_trans = (result_stab + log_mat_rep1) % 2
                perm = np.zeros(k, dtype = int)
                for i in range(k):

                   elem1 = log_mat_trans[i, :]
                   for j in range(k):
                    elem2 = log_mat_rep2[j, :]
                    if all(elem1 == elem2):
                        perm[i] = j
                        break
                # print(perm)
                
                sexp_set1 = [args[2*i] for i in range(len(args)//2)]
                sexp_set2 = [self.child[2*i] for i in range(len(args)//2)]

                for i in range(len(args) // 2):
                    if not self.eq_sexpr(sexp_set1[i], sexp_set2[perm[i]]):
                        return Tree('false', [])
        
            return Tree('true', [])
            # eq_sexp = [self.eq_sexpr(sexp_set1[i], sexp_set2[i]) for i in range(len(sexp_set1))]
            # if all(eq_sexp == True) == False:
            #     return False
            # else: ##Judge whether base = g * args

class eval_and(Transformer): ##Pruning for And conjunctions 
    def cap(self, args):
        if args[0] == Tree('false', []) or args[1] == Tree('false', []):
            return Tree('false', [])
        elif args[0] == Tree('true', []) and args[1] == Tree('true', []):
            return Tree('true', [])
        elif args[0] == Tree('true', []):
            return args[1]
        elif args[1] == Tree('true', []):
            return args[0]
        else:
            return Tree('cap', [args[0], args[1]])

        
## Const logical S gate program generation for surface code (fault-free)

## Const logical T gate program generation for surface code (fault-free)
def program_T(matrix, distance):
    # matrix = surface_matrix_gen(distance)
    numq = matrix.shape[1] // 2
    prog_part = []
    for i in range(1, numq):
        if (matrix[numq-1][i] == 1):
            prog_part.append(f"q_(1), q_({i + 1}) *= CNOT;")
    for i in range(1, numq):
        if(matrix[numq][i + numq] == 1):
            prog_part.append(f"q_({i + 1}), q_(1) *= CNOT;")
    # prog_part.append(f"q_(1) *= T;")
    prog_T = "q_(1) *= T;"
    prog_part_rev = prog_part[::-1]
    
    prog_op = " ".join(prog_part)
    prog_rev = " ".join(prog_part_rev)[:-1]
    prog = prog_op + prog_T + prog_rev
    return prog, prog_op[:-1]

def construct_precond(gate, pc_x, pc_z, d):
    pcx_part = pc_x.split('&&')
    pcz_part = pc_z.split('&&')
    stab_cond = "&&".join(pcx_part[:-1] + pcz_part[:-1])

    sur_mat = surface_matrix_gen(d)
    numq = d**2
    log_X, log_Y, log_Z = "(-1)^(b_(1))", "", "(-1)^(b_(1))"
    imag_count = -1
    vec_y = sur_mat[numq-1] + sur_mat[numq]

    for i in range(numq):
        # vec_y  = sur_mat[numq-1] + sur_mat[]
        if (sur_mat[numq-1][i] == 1):
            log_X = log_X + f"(0,1,{i + 1})"
        if (sur_mat[numq][i + numq] == 1):
            log_Z = log_Z + f"(1,0,{i + 1})"
        if (vec_y[i] == 1 or vec_y[i + numq] == 1):
            log_Y = log_Y + f"({vec_y[i + numq]},{vec_y[i]},{i + 1})"
            imag_count += 1
    
    assert (imag_count % 2) == 0
    if (imag_count % 4) != 0:
        log_Y = f"(-1)^(b_(1) + 1)" + log_Y
    else:
        log_Y = f"(-1)^(b_(1))" + log_Y
    if gate == 'T':
        coeff, coeff_neg = "QR2[0,0,1]", "QR2[0,0,-1]" 
        log_Z_pre = log_Z
        log_X_pre = coeff + log_X + "+" + coeff_neg + log_Y
        log_Y_pre = coeff + log_X + "+" + coeff + log_Y
        # if log_id == 'X':
        #     precond = 
    # if gate == 'T':
    #     precond_x = 
    precond_x = stab_cond + "&&" + log_X_pre
    precond_z = stab_cond + "&&" + log_Z_pre
    return log_X_pre, log_Z_pre
def sur_cond_gen_logical(d, N):
    numq = d**2
    sur_mat = surface_matrix_gen(d)
    pcx, pcz = stab_cond_gen_multiq(sur_mat, numq, N)
    # precond_x, precond_z = construct_precond('T', pcx, pcz, d)
    log_X_pre, log_Z_pre = construct_precond('T', pcx, pcz, d)
    # print(precond_x)
    stab_x_part = pcx.split('&&')[:-1]
    stab_z_part = pcz.split('&&')[:-1]
    stab_part = stab_x_part + stab_z_part 
    stab_tree_part = [get_parser().parse(stab_part[i]).children[0] for i in range(len(stab_part))]
    
    stab_cond = "&&".join(stab_part)

    log_X, log_Z = pcx.split('&&')[-1], pcz.split('&&')[-1]
    
    program = program_T(sur_mat, d)[0]
    # print(program)
    ##Stabilizer evaluation
    pre_tree, _, post_tree = precond_generator(program, stab_cond, stab_cond)
    cass_transformer = qassertion2c(pre_tree)
    stab_eval_tree = cass_transformer.transform(post_tree)
    stab_eval_tree = eval_and().transform(simplifyeq().transform(stab_eval_tree))

    stab_eval = recon_string(stab_eval_tree)

    ##Logical X evaluation
    log_X_pre_tree, _, log_X_tree = precond_generator(program, log_X_pre, log_X)
    add_transformer = add_comparison(log_X_pre_tree, stab_tree_part)
    # print(log_X_pre_tree)
    # print(log_X_tree)
    log_X = recon_string(log_X_tree)
    logX_eval = recon_string(add_transformer.transform(log_X_tree))
   
    log_Z_pre_tree, _, log_Z_tree = precond_generator(program, log_Z_pre, log_Z)
    cass_transformer = qassertion2c(log_Z_pre_tree)
    logZ_eval = recon_string(simplifyeq().transform(cass_transformer.transform(log_Z_tree)))
    
    return stab_eval, logX_eval, logZ_eval

if __name__ == "__main__":
    matrix = special_codes.stabs_Reed_Muller(4)
    # print(matrix)
    # print(program_T(matrix, 3)[0])
    # for i in range(1, 3):
    #    stab_eval, logX_eval, logZ_eval = sur_cond_gen_logical(2 * i + 1, 1) 
    #    print(stab_eval)
    #    print(logX_eval)
    #    print(logZ_eval)
