import numpy as np

def gf2_matrix_rank(A):
    # Ensure the matrix consists of binary entries
    A = np.mod(A, 2)
    num_rows, num_cols = A.shape
    rank = 0

    for col in range(num_cols):
        # Find the pivot row
        pivot_row = None
        for row in range(rank, num_rows):
            if A[row, col] == 1:
                pivot_row = row
                break

        if pivot_row is None:
            continue

        # Swap the pivot row to the current rank row
        if pivot_row != rank:
            A[[rank, pivot_row]] = A[[pivot_row, rank]]

        # Eliminate all rows below pivot
        for row in range(rank + 1, num_rows):
            if A[row, col] == 1:
                A[row] = np.logical_xor(A[row], A[rank]).astype(int)

        # Move to the next row in the reduced matrix
        rank += 1

    return rank

# Example usage
classical734 = np.array([[1, 1, 0, 1, 0, 0, 0],
                        [0, 1, 1 ,0, 1, 0, 0],
                        [0, 0, 1, 1, 0, 1, 0],
                        [0, 0, 0, 1, 1, 0, 1],
                        [1, 0, 0, 0, 1, 1, 0],
                        [0, 1, 0, 0, 0, 1, 1],
                        [1, 0, 1, 0, 0, 0, 1]], dtype = int)
rank = gf2_matrix_rank(classical734)
print("Rank of matrix over GF(2):", rank)
