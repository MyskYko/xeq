#pragma once

#include "node.h"

// satsolve.cpp
extern void SatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, int out_encoding = 0);
extern int SatSolve4(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, bool fEach = 0);
extern void SatTest();

// satexp2.cpp
extern const char *dimacsname;
extern void SatExp2(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, std::vector<int> *dumpdimacs = NULL);

// satsolve2.cpp
extern int CadicalSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0);
extern int KissatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, int target = 0);
extern int CadicalExp(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0);
extern int KissatExp(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, int target = 0);

