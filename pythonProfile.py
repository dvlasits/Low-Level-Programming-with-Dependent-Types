import subprocess
import os
import timeit
import matplotlib.pyplot as plt

binaries = ["bintest"]#["haskell", "myArray", "idrisVec"]

def runScript(binary, arraySize):
    if binary == "haskell":
        subprocess.run(["cabal", "run", "main", str(arraySize)], stdout=subprocess.PIPE)
    else:
        subprocess.run([f"./build/exec/{binary}", str(arraySize)], stdout=subprocess.PIPE)


"""
t = timeit.Timer("subprocess.run(['./build/exec/testFFI'], stdout=subprocess.PIPE)",  setup="import subprocess")

print(t.timeit(1))

t = timeit.Timer("subprocess.run(['cabal', 'run', 'main'], stdout=subprocess.PIPE)",  setup="import subprocess")

print(t.timeit(1))
quit()"""



times = [[],[],[]]

sizes = [10**4, 10**5,  10**6, (10**6) * 2,  (10**6) * 6,  10**7]

#sizes = [i * (10**4) for i in [1,2,3,4,5,6,7,8,9]]

sizes = [i * (10**6) for i in [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]]

print("here")

for index,binary in enumerate(binaries):
    for arraySize in sizes:
        if binary == "idrisVec" and arraySize > 10**5:
            continue
        t = timeit.Timer(f"runScript('{binary}', {arraySize})", setup="from __main__ import runScript")

        times[index].append(t.timeit(1))
        print(times[index][-1])


for index, arr in enumerate(times):
    if not arr:
        times.pop(index)

print("finished")

labels = {"haskell" : "IO Monad Array in Haskell", "myArray" : "Low-Level-Library Array", "idrisVec" : "Inbuilt Idris Vector", "bintest" : "Binary Search Function"}

for index,name in enumerate(binaries):
    arr = times[index]
    length = len(arr)
    sizes1 = sizes[:length]
    plt.plot(sizes1, arr, label=labels[name])

plt.legend()

plt.xlabel('Size of Array')
plt.ylabel('Time Taken (s)')
plt.title("Comparing performance of varying array datastructures")
plt.show()