# xeq

 - Please implement your method in src/include. It is good if it is written in the format "void your_func_name(nodecircuit::Circuit gf, nodecircuit::Circuit rf, std::vector<bool> result)".
 - You can add external programs, like SAT solver, in lib directory using git submodule.
 - When you make commit, please create a branch, but do not add main.cpp, which may cause conflicts later. Ofcource you can run tests by modifying main.cpp.
 - Create pull request from your branch to master.
 
This enables us to compare methods easily.

## BDD

I implemented a method with BDD. It creates 2 BDDs, f and g, for each node. (f,g)=(0,0) is 0, (1,0) is 1, (0,1) and (1,1) are x.

You can test the method with a modification in main.cpp as follows
 - Include "bddsolve.h"
 - Call BddSolve(gf, rf, result) at the line "//Solve(gf,rf,result)".
