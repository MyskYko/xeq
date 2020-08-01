# xeq

## Build

After cloning this repository, run the following commands
```
git submodule update -i
mkdir build
cd build
cmake ..
make
```

The pure program will just read circuits and give EQ. Please notice that this doesn't mean the circuits are acutally equivalent.

If you want to run tests, please add a line in main.cpp to call the function you will test.

## Develop 

 - Please implement your method in src/include. It is good if it is written in the format "void your_func_name(nodecircuit::Circuit gf, nodecircuit::Circuit rf, std::vector<bool> result)".
 - You can add external programs, like SAT solver, in lib directory using git submodule.
 - When you make commit, please create a branch, but do not add main.cpp, which may cause conflicts later. Ofcource you can run tests by modifying main.cpp.
 - Create pull request from your branch to master.
 
This enables us to compare methods easily.

### BDD

I implemented a method with BDD. It creates 2 BDDs, f and g, for each node. (f,g)=(0,0) is 0, (1,0) is 1, (0,1) and (1,1) are x.

You can test the method with a modification in main.cpp as follows
 - Include "bddsolve.h"
 - Call BddSolve(gf, rf, result) at the line "//Solve(gf,rf,result)".

### Minimization

During minimization, original Verilog file is at first converted into BLIF file, minimized by resynthesis, written back into verilog file, and at last read by the new function of ReadVerilogNew.

To use the new function:
 - Include "minimize.h" in main function.
 - Call Minimize(filename), taking "gf1.v" as an example, a file named "minimized_gf1.v" would be established, as well as intermediate files "Verilog2BLIF.blif", "twmp.blif" and "temp.blif".
 - Use ReadVerilogNew(minimized_filename), e.g. minimized_gf1.v, to generate Nodecircuit.
 - Since the format of the re-written verilog is different from the original one, like upmost 2 inputs for each gate and new gate types "SHARP(A&~B)" and "SHARP(~A&B)", all the current methods have to be modified.
