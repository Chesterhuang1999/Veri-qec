import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import curve_fit
from mpl_toolkits.axes_grid1.inset_locator import inset_axes, mark_inset

# # Data
# ### Data I: testing using err conditions ###
# code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 31, 35, 45, 51, 55]  # X-axis values
# verification_time = [1.185, 2.096, 5.605, 11.210, 45.996, 132.587, 362.086, 740.03, 1621.76, 3868.49, 14184.05, 33467.36, 49102.39]  # Y-axis values
# generation_time = [0.137, 0.411, 1.049,2.337, 8.6077,25.087,61.502, 132.96, 263.72, 493.361, 1922.99, 3832.43, 5855.62]

# ### Data II: testing using surface code ### 
# # code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 31, 35]
# # generation_time = [0.159, 0.473, 1.977, 3.037, 10.857, 31.863, 76.491, 165.436, 327.126, 592.042]
# testopt_time = [1.978, 2.976, 12.187, 36.402, 97.913, 217.215, 657.429, 1914.706, 5108.013, 19346.465]
# testopt_time = [1.978, 2.976, 12.187, 36.402, 97.913, 217.215, 657.429, 1914.706, 19346.465]
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
# ax.plot(code_distance, verification_time, marker='o', label='Testing Time-Condition', color='b')
# ax.plot(code_distance[:10], testopt_time, marker = 'o', label = 'Testing Time-Opt', color = 'g')
# ax.plot(code_distance, generation_time, marker='s', label='VC Generation Time', color='#A52A2A')
# ax.set_xlabel('Code Distance', fontsize = 13)
# ax.set_ylabel('Time (s)', fontsize = 13)
# ax.set_title('Code Distance vs Test Time', fontsize = 16)
# ax.legend()
# ax.grid(True)
# ax.set_yscale('log')
# Create inset plot
# axins = inset_axes(ax, width="30%", height="30%", loc='upper left', borderpad=7)
# axins.plot(code_distance[:7], verification_time[:7], marker='o', color='b')  # First 7 points
# axins.plot(code_distance[:7], generation_time[:7], marker='s', color='#A52A2A')  # First 7 points
# axins.plot(code_distance[:7], testopt_time[:7], marker='o', color='g')  # First 7 points

# # Set limits for the inset
# axins.set_xlim(min(code_distance[:7]), max(code_distance[:7]))
# axins.set_ylim(min(min(verification_time[:7]), min(generation_time[:7])) - 1, 
#                max(max(testopt_time[:7]), max(generation_time[:7])) + 1)

# for x, y in zip(code_distance[4:7], verification_time[4:7]):
#     axins.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, 5), ha='center', fontsize=9, color='b')

# for x, y in zip(code_distance[4:7], generation_time[4:7]):
#     axins.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, -10), ha='center', fontsize=9, color='#A52A2A')

# for x, y in zip(code_distance[7:], verification_time[7:]):
#     ax.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, -15), ha='center', fontsize=11, color='b')

# for x, y in zip(code_distance[9:], generation_time[9:]):
#     ax.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, -15), ha='center', fontsize=11, color='#A52A2A')

# for x, y in zip(code_distance[7:10], testopt_time[7:10]):
#     ax.annotate(f"{y:.2f}", (x, y), textcoords="offset points", xytext=(0, 10), ha='center', fontsize=11, color='g')
# Optionally remove tick labels for clarity
# axins.set_xticks(code_distance[:7])
# axins.set_yticks(np.linspace(min(axins.get_ylim()), max(axins.get_ylim()), num=5))
# axins.set_xticklabels(code_distance[:7], rotation=45)  # Optional: Rotate x-axis labels
# axins.set_yticklabels(["{:.1f}".format(i) for i in np.linspace(min(axins.get_ylim()), max(axins.get_ylim()), num=5)])

# # Connect the main plot and inset
# mark_inset(ax, axins, loc1=2, loc2=4, fc="none", ec="0.5")

# Display the plot
# plt.savefig('Figures/Test_gen_time_surface_code_55.svg')
# plt.show()


##### Verify decoding correctness #####
# code_distance = [3, 5, 7, 9, 11]  # X-axis values
# sequential_time = [0.325, 2.064, 629.3]
# parallel_time = [0.625, 0.646, 3.607, 117.0, 12799]  # Y-axis values

# # Create the plot
# plt.figure(figsize=(10, 6))
# plt.plot(code_distance[:3], sequential_time, marker='o', linestyle='-', linewidth = 3, color='r', label='Sequential')
# plt.plot(code_distance, parallel_time, marker='o', linestyle='-', linewidth = 3, color='g', label = 'Parallel')
# plt.legend()
# # Set the scale to logarithmic for better visualization
# plt.yscale('log')

# # Add labels and title
# plt.xlabel('Code Distance', fontsize = 20)
# plt.ylabel('Verification Time (s)', fontsize = 20)
# plt.title('Verification Time vs Code Distance', fontsize = 25)
# plt.grid(which='both', linestyle='--', linewidth=1)
# plt.xticks(code_distance)  # Set x-ticks to code distances
# plt.yticks([1, 10, 100, 1000, 10000], ['1s', '10s', '100s', '1000s', '10000s'])  # Custom y-ticks for readability

# for i, txt in enumerate(sequential_time):
#     plt.annotate(f'{txt}', 
#                 (code_distance[i],sequential_time[i]), 
#                  textcoords="offset points", 
#                  xytext=(0,10), 
#                  ha='center', 
#                  fontsize=15)
# for i, txt in enumerate(parallel_time):
#     plt.annotate(f'{txt}', 
#                 (code_distance[i],parallel_time[i]), 
#                  textcoords="offset points", 
#                  xytext=(0,10), 
#                  ha='center', 
#                  fontsize=15)

# # Show the plot
# # plt.show()
# plt.savefig('Figures/verify_time_surface_code_11.svg')



##### Log for testing-opt.py #####

# code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 31, 35]
# gen_time = [0.159, 0.473, 1.977, 3.037, 10.857, 31.863, 76.491, 165.436, 327.126, 592.042]
# tol_time = [1.978, 2.976, 12.187, 36.402, 97.913, 217.215, 657.429, 1914.706, 5108.013, 19346.465]



##### Log for detect-only task #####

code_distance = [5, 7, 9, 11, 13, 17, 21, 23, 25]
gen_time = [0.44, 0.84, 1.62, 2.88, 5.13, 15.48, 35.13, 53.26, 80.80]
time_x = [0.493, 0.511, 0.657, 0.915, 1.93, 43.66, 1106.89, 808.60, 6087.17]
time_z = [0.533, 0.527, 0.678, 0.974, 1.02, 9.51, 22.55, 40.00, 64.66]
verify_time = [1.003, 1.407, 2.28, 4.06, 12.61, 101.98, 3218.04, 14380.55]
detect_time = [round(x + z, 3) for x, z in zip(time_x, time_z)]
total_task = [20, 66, 238, 852, 3460, 67600, 1436494, 384560, 1338440]

plt.rcParams['font.family'] = 'Arial'
# Create the plot
fig, axs = plt.subplots(1, 2, figsize = (20, 7), sharex = True)
axs[0].set_yscale('log')

axs[0].plot(code_distance, gen_time, marker = '*', linestyle='-', color='#c44e52', label = 'Condition generation time', linewidth = 3)
axs[0].plot(code_distance, detect_time, marker= 'o', linestyle='-', color='#8172b2', label = 'Verify time for dt = d+1', linewidth = 3)
axs[0].plot(code_distance[:8], verify_time, marker = 'o', linestyle='-', color='#ff6347', label = 'Verify time for dt = d', linewidth = 3)
# axs[0].plot(code_distance, time_x, marker='o', linestyle='-', color='#4c72b0', label = 'detect Z error', linewidth = 3)
# axs[0].plot(code_distance, time_z, marker='o', linestyle='-', color='#55a868', label = 'detect X error', linewidth = 3)
axs[0].set_xlabel('Code Distance', fontsize = 20)
axs[0].set_ylabel('Time (s)', fontsize = 20)
axs[0].set_title('Verify vs Condition Generation Time', fontsize = 25)  
axs[0].legend()
axs[0].grid(True)
# axs[1].set_ylabel('Time (s)', fontsize = 16)
axs[1].set_yscale('log')
axs[1].plot(code_distance, time_x, marker='o', linestyle='-', color='#4c72b0', label = 'detect Z error', linewidth = 3)
axs[1].plot(code_distance, time_z, marker='o', linestyle='-', color='#55a868', label = 'detect X error', linewidth = 3)
axs[1].set_xlabel('Code Distance', fontsize = 20)

axs[1].set_title('Time to detect logical X and Z errors', fontsize = 25)  
axs[1].legend()
axs[1].grid(True)

# Create inset plot
axins = inset_axes(axs[1], width="30%", height="30%", loc='upper left', borderpad=5)
axins.plot(code_distance[:4], time_x[:4], marker='o', color='#4c72b0', linewidth = 3)  # First 4 points
axins.plot(code_distance[:4], time_z[:4], marker='o', color='#55a868', linewidth = 3)  # First 4 points

# Set limits for the inset
axins.set_xlim(min(code_distance[:4]) - 1, max(code_distance[:4]) + 1)
axins.set_ylim(min(min(detect_time[:4]), min(gen_time[:4])) - 0.1, 
               max(max(detect_time[:4]), max(gen_time[:4])) - 1.8 )

# Optionally remove tick labels for clarity
axins.set_xticks(code_distance[:4])
axins.set_yticks(np.linspace(min(axins.get_ylim()), max(axins.get_ylim()), num=5))
axins.set_xticklabels(code_distance[:4], rotation=45)  # Optional: Rotate x-axis labels
axins.set_yticklabels(["{:.1f}".format(i) for i in np.linspace(min(axins.get_ylim()), max(axins.get_ylim()), num=5)])

# Connect the main plot and inset
# mark_inset(axs[1], axins, loc1=3, loc2=4, fc="none", ec="0.5")
for i, txt in enumerate(detect_time):
    if i > 4:
        axs[0].annotate(f'{txt}', 
                (code_distance[i],detect_time[i]), 
                textcoords="offset points", 
                xytext=(0,-20), 
                ha='center', 
                fontsize=14, color = '#8172b2')
for i, txt in enumerate(verify_time):
    loc = 8 if i <= 4 else 10
    axs[0].annotate(f'{txt}',
            (code_distance[i],verify_time[i]), 
            textcoords="offset points", 
            xytext=(0,loc), 
            ha='center', 
            fontsize=14, color = '#ff6347')
for i, txt in enumerate(gen_time):
    if i > 4:
        axs[0].annotate(f'{txt}', 
                (code_distance[i],gen_time[i]), 
                    textcoords="offset points", 
                    xytext=(0,-15), 
                    ha='center', 
                    fontsize=14, color = '#c44e52')
for i, txt in enumerate(time_x):
    if i < 4:
        axins.annotate(f'{txt}',
                       (code_distance[i],time_x[i]), 
                textcoords="offset points", 
                xytext=(0,-10), 
                ha='center', 
                fontsize=11, color = '#4c72b0')
    if i >= 4:
        axs[1].annotate(f'{txt}', 
                (code_distance[i],time_x[i]), 
                textcoords="offset points", 
                xytext=(0,10), 
                ha='center', 
                fontsize=14, color = '#4c72b0')
for i, txt in enumerate(time_z):
    if i < 4:
        axins.annotate(f'{txt}', 
                (code_distance[i],time_z[i]), 
                textcoords="offset points", 
                xytext=(0,10), 
                ha='center', 
                fontsize=11, color = '#55a868')
    if i >= 4:
        axs[1].annotate(f'{txt}', 
                (code_distance[i],time_z[i]), 
                textcoords="offset points", 
                xytext=(0,-20), 
                ha='center', 
                fontsize=14, color = '#55a868')
        
plt.tight_layout()
plt.savefig('Figures/Verification_time_detect.svg')
# plt.show()


