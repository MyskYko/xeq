#pragma once

#include "node.h"

extern void SatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, int out_encoding = 0);
extern void SatSolve3(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result);
extern void SatSolveNode(nodecircuit::Circuit &gf, nodecircuit::Node *gp, nodecircuit::Circuit &rf, nodecircuit::Node *rp, std::vector<bool> &result, bool fexact);
extern int SatSolve4(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0, bool fEach = 0);
extern void SatTest();
