import matplotlib.pyplot as plt

# Data
code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 35, 45]  # X-axis values
verification_time = [1.185, 2.096, 5.605, 11.210, 45.996, 132.587, 362.086, 740.03, 3868.49, 14184.05]  # Y-axis values

# Create the plot
plt.figure(figsize=(10, 6))
plt.plot(code_distance, verification_time, marker='o', linestyle='-', color='b')

# Set the scale to logarithmic for better visualization
plt.yscale('log')

# Add labels and title
plt.xlabel('Code Distance', fontsize = 16)
plt.ylabel('Testing Time (s)', fontsize = 16)
plt.title('Testing Time vs Code Distance', fontsize = 20)
plt.grid(which='both', linestyle='--', linewidth=1)
plt.xticks(code_distance)  # Set x-ticks to code distances
plt.yticks([1, 10, 100, 1000, 10000], ['1s', '10s', '100s', '1000s', '10000s'])  # Custom y-ticks for readability


for i, txt in enumerate(verification_time):
    plt.annotate(f'{txt}', 
                (code_distance[i],verification_time[i]), 
                 textcoords="offset points", 
                 xytext=(0,10), 
                 ha='center', 
                 fontsize=13)

# Show the plot
plt.savefig('Figures/Testing_time_surface_code_45.png')

# code_distance = [3, 5, 7, 9, 11]  # X-axis values
# sequential_time = [0.325, 2.064, 629.3]
# parallel_time = [0.625, 0.646, 3.607, 117.0, 12799]  # Y-axis values

# # Create the plot
# plt.figure(figsize=(10, 6))
# plt.plot(code_distance[:3], sequential_time, marker='o', linestyle='-', color='r', label='Sequential')
# plt.plot(code_distance, parallel_time, marker='o', linestyle='-', color='g', label = 'Parallel')

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
# # plt.show()
# plt.savefig('Figures/Verify_time_surface_code_11.png')
