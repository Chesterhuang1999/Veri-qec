import matplotlib.pyplot as plt

x = [3, 5, 7, 9, 11, 13, 15, 17]

enc = [0.1394, 0.8414, 3.7439, 10.1006, 21.8405, 44.418, 107.71, 131.16]

che = [0.1773, 9.7739, 30.7577, 85.6068, 191.5960, 386.84, 1088.64, 1800.32]

plt.plot(x, enc, label = 'encode time')
plt.plot(x, che, label = 'check time')
plt.legend()
plt.savefig('Lark/Fig/t_surface_17_z3.png')