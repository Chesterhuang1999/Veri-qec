import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import curve_fit
from mpl_toolkits.axes_grid1.inset_locator import inset_axes, mark_inset

# # Data
### Data I: testing using err conditions ###
# code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 35, 45, 51, 55]  # X-axis values
# verification_time = [1.185, 2.096, 5.605, 11.210, 45.996, 132.587, 362.086, 740.03, 3868.49, 14184.05, 33467.36, 49102.39]  # Y-axis values
# generation_time = [0.137, 0.411, 1.049,2.337, 8.6077,25.087,61.502, 132.96, 493.361, 1922.99, 3832.43, 5855.62]

### Data II: testing using surface code ### 
code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 31, 35]
generation_time = [0.159, 0.473, 1.977, 3.037, 10.857, 31.863, 76.491, 165.436, 327.126, 592.042]
verification_time = [1.978, 2.976, 12.187, 36.402, 97.913, 217.215, 657.429, 1914.706, 5108.013, 19346.465]
# smt_time = np.array(verification_time) - np.array(generation_time)
# log_verification_time = np.log(verification_time)
# # Define a model function for fitting (e.g., a * sqrt(x) + b)
# def sqrt_model(x, a, b):
#     return a * np.sqrt(x) + b
# # def linear_model(x, a, b):
# #     return a * x + b
# # Perform the curve fitting
# params, covariance = curve_fit(sqrt_model, code_distance, log_verification_time)

# # Extract fitted parameters
# a, b = params
# print(covariance)
# # print(a)
# # Generate points for plotting the fit
# x_fit = np.linspace(min(code_distance), max(code_distance), 100)
# y_fit = sqrt_model(x_fit, a, b)
# plt.figure(figsize=(8, 5))
# plt.scatter(code_distance, log_verification_time, label='Log of Verification Time', color='red')
# plt.plot(x_fit, y_fit, label=f'Fit: $y = {a:.2f} \sqrt{{x}} - {-b:.2f}$', color='blue')
# plt.xlabel('Code Distance')
# plt.ylabel('Log(Verification Time)')
# plt.title('Log(Verification Time) vs Code Distance')
# plt.legend()
# plt.grid(True)
# plt.show()

# # Create the plot
# plt.figure(figsize=(10, 6))
# plt.plot(code_distance, verification_time, marker='o', linestyle='-', color='b')
# plt.plot(code_distance, generation_time, marker = '*', linestyle='-', color='#A52A2A' )
# # Set the scale to logarithmic for better visualization
# # plt.yscale('log')

# # Add labels and title
# plt.xlabel('Code Distance', fontsize = 16)
# plt.ylabel('Time (s)', fontsize = 16)
# plt.title('Testing Time vs AST Generation Time', fontsize = 20)
# plt.grid(which='both', linestyle='--', linewidth=1)
# plt.xticks(code_distance)  # Set x-ticks to code distances
# plt.yticks([1, 10, 100, 1000, 10000], ['1s', '10s', '100s', '1000s', '10000s'])  # Custom y-ticks for readability


# for i, txt in enumerate(verification_time):
#     if i >= 8:
#         plt.annotate(f'{txt}', 
#                 (code_distance[i],verification_time[i]), 
#                  textcoords="offset points", 
#                  xytext=(0,10), 
#                  ha='center', 
#                  fontsize=13)
# for i, txt in enumerate(generation_time):
#     if i >= 8: 
#         plt.annotate(f'{txt}', 
#                 (code_distance[i],generation_time[i]), 
#                  textcoords="offset points", 
#                  xytext=(0,10), 
#                  ha='center', 
#                  fontsize=13)

# # Create main plot
# fig, ax = plt.subplots(figsize=(10, 6))
# ax.plot(code_distance, verification_time, marker='o', label='Verification Time', color='b')
# ax.plot(code_distance, generation_time, marker='s', label='Generation Time', color='#A52A2A')
# ax.set_xlabel('Code Distance', fontsize = 13)
# ax.set_ylabel('Time (s)', fontsize = 13)
# ax.set_title('Code Distance vs Time with Detail Inset', fontsize = 16)
# ax.legend()
# ax.grid(True)

# # Create inset plot
# axins = inset_axes(ax, width="40%", height="40%", loc='upper left', borderpad=5)
# axins.plot(code_distance[:7], verification_time[:7], marker='o', color='b')  # First 7 points
# axins.plot(code_distance[:7], generation_time[:7], marker='s', color='#A52A2A')  # First 7 points

# # Set limits for the inset
# axins.set_xlim(min(code_distance[:7]), max(code_distance[:7]))
# axins.set_ylim(min(min(verification_time[:7]), min(generation_time[:7])) - 1, 
#                max(max(verification_time[:7]), max(generation_time[:7])) + 1)

# for x, y in zip(code_distance[4:7], verification_time[4:7]):
#     axins.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, 5), ha='center', fontsize=9, color='b')

# for x, y in zip(code_distance[4:7], generation_time[4:7]):
#     axins.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, -10), ha='center', fontsize=9, color='#A52A2A')

# for x, y in zip(code_distance[7:], verification_time[7:]):
#     ax.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, 10), ha='center', fontsize=11, color='b')

# for x, y in zip(code_distance[7:], generation_time[7:]):
#     ax.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, -12), ha='center', fontsize=11, color='#A52A2A')
# # Optionally remove tick labels for clarity
# axins.set_xticks(code_distance[:7])
# axins.set_yticks(np.linspace(min(axins.get_ylim()), max(axins.get_ylim()), num=5))
# axins.set_xticklabels(code_distance[:7], rotation=45)  # Optional: Rotate x-axis labels
# axins.set_yticklabels(["{:.1f}".format(i) for i in np.linspace(min(axins.get_ylim()), max(axins.get_ylim()), num=5)])

# # Connect the main plot and inset
# mark_inset(ax, axins, loc1=2, loc2=4, fc="none", ec="0.5")

# # Display the plot
# plt.show()
# plt.savefig('Figures/Test_gen_time_surface_code_45.eps')

# code_distance = [3, 5, 7, 9, 11]  # X-axis values
# sequential_time = [0.325, 2.064, 629.3]
# parallel_time = [0.625, 0.646, 3.607, 117.0, 12799]  # Y-axis values

# # Create the plot
# plt.figure(figsize=(10, 6))
# plt.plot(code_distance[:3], sequential_time, marker='o', linestyle='-', color='r', label='Sequential')
# plt.plot(code_distance, parallel_time, marker='o', linestyle='-', color='g', label = 'Parallel')
# plt.legend()
# # Set the scale to logarithmic for better visualization
# plt.yscale('log')

# # Add labels and title
# plt.xlabel('Code Distance', fontsize = 16)
# plt.ylabel('Verification Time (s)', fontsize = 16)
# plt.title('Verification Time vs Code Distance', fontsize = 20)
# plt.grid(which='both', linestyle='--', linewidth=1)
# plt.xticks(code_distance)  # Set x-ticks to code distances
# plt.yticks([1, 10, 100, 1000, 10000], ['1s', '10s', '100s', '1000s', '10000s'])  # Custom y-ticks for readability

# for i, txt in enumerate(sequential_time):
#     plt.annotate(f'{txt}', 
#                 (code_distance[i],sequential_time[i]), 
#                  textcoords="offset points", 
#                  xytext=(0,10), 
#                  ha='center', 
#                  fontsize=13)
# for i, txt in enumerate(parallel_time):
#     plt.annotate(f'{txt}', 
#                 (code_distance[i],parallel_time[i]), 
#                  textcoords="offset points", 
#                  xytext=(0,10), 
#                  ha='center', 
#                  fontsize=13)

# # Show the plot
# plt.show()
# plt.savefig('Figures/Verify_time_surface_code_11.png')



##### Log for testing-opt.py #####

code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 31, 35]
gen_time = [0.159, 0.473, 1.977, 3.037, 10.857, 31.863, 76.491, 165.436, 327.126, 592.042]
tol_time = [1.978, 2.976, 12.187, 36.402, 97.913, 217.215, 657.429, 1914.706, 5108.013, 19346.465]

