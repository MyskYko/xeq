#pragma once

#include "node.h"

extern void SatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, int out_encoding = 0);
extern int CadicalSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0);
extern int KissatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, int target = 0);
extern int SatSolve4(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, bool fEach = 0);
extern void SatTest();
