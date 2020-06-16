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
 
### SAT

Principle:

Descriptions for gates, other than dc gates, are in a common way.
For dc gates, when the signal of D is 0, O is equal to C, while O becomes x when D is 1.
So, when D is 1, we divided the discussion into two cases: D->O and D->~O.
Therefore, to traverse all the potential cases, we are creating 2^dc ("dc" represents the number of dc gates in that circuit) sat problems for one circuit.

Application:

For the class of Circuit in "node.h", a data member called "dc", which is of data type NodeVector, is added, it covers all the nodes representing dc gates in the circuit. For the same reason, "node.cpp" is modified correspondingly as well.
And a fuction called "GetNodeIndex" is added as a funtion member of the class Circuit, it is used for attaining the index of a node in the vector of "all_nodes".
To test the sat-based method, "satsolve.h" is supposed to be included, and use the command of "SatSolve(gf, rf, result)" for operation.

