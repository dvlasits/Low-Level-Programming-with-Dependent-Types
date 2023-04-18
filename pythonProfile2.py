import subprocess

import matplotlib.pyplot as plt


#sizes = [i * (10**6) for i in range(1,)]
sizes = [i * (10 ** 6) for i in [1,2,3,4,5,6,7,8,9,10,11,12]]
sizes = [10 ** i for i in [1,2,3,4,5,6,7,8]]
sizes = [[x * (10 ** i) for x in range(1,11)] for i in range (1,9)]
sizes2 = []
for ele in sizes:
    for ele2 in ele:
        sizes2.append(ele2)
sizes = sizes2
arr = []
for size in sizes:
    result = [subprocess.run(['./build/exec/bintest', str(size)], stdout=subprocess.PIPE) for x in range(13)]
    results = [int(res.stdout.decode('ascii')) for res in result]
    maxs = max(results)
    out = (sum(results) - max(results) - min(results)) / 11
    
    arr.append(out)
    print(out)

labels = {"haskell" : "IO Monad Array in Haskell", "myArray" : "Low-Level-Library Array", "idrisVec" : "Inbuilt Idris Vector", "bintest" : "Binary Search Function"}




plt.plot(sizes, arr, label="Binary Search")

plt.legend()

plt.xlabel('Size of Array')
plt.ylabel('Time Taken (s)')
plt.title("Performance of Binary Search")
plt.show()