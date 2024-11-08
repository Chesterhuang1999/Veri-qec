import numpy as np

# Example usage
num = 9

numq = 20

select = np.random.choice(numq, num, replace = False)
select = np.sort(select)
temp = np.array([1,1,0,0,0,1,1,0,1])
print(select)
P = np.zeros(numq, dtype = np.int32)
P[select] = temp
print(P.tolist())
