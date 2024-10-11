import matplotlib.pyplot as plt

# Data
# code_distance = [5, 7, 9, 11, 15, 19, 23, 27, 35, 45]  # X-axis values
# verification_time = [1.185, 2.096, 5.605, 11.210, 45.996, 132.587, 362.086, 740.03, 3868.49, 14184.05]  # Y-axis values

# # Create the plot
# plt.figure(figsize=(10, 6))
# plt.plot(code_distance, verification_time, marker='o', linestyle='-', color='b')

# # Set the scale to logarithmic for better visualization
# plt.yscale('log')

# # Add labels and title
# plt.xlabel('Code Distance')
# plt.ylabel('Verification Time (s)')
# plt.title('Verification Time vs Code Distance')
# plt.grid(which='both', linestyle='--', linewidth=0.5)
# plt.xticks(code_distance)  # Set x-ticks to code distances
# plt.yticks([1, 10, 100, 1000, 10000], ['1s', '10s', '100s', '1000s', '10000s'])  # Custom y-ticks for readability


# for i, txt in enumerate(verification_time):
#     plt.annotate(f'{txt}', 
#                 (code_distance[i],verification_time[i]), 
#                  textcoords="offset points", 
#                  xytext=(0,10), 
#                  ha='center', 
#                  fontsize=9)

# # Show the plot
# plt.savefig('Figures/Testing_time_surface_code_45.png')
