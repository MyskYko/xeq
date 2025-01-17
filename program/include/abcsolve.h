#pragma once

#include "node.h"

int AbcSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding = 0);
int AbcSolve2(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, bool fzero = 0);
void DumpMiterAiger(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::string filename, bool fzero = 0);
