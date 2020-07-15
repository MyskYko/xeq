#pragma once

#include "node.h"

int AbcSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, bool fzero = 0);
void DumpMiterAiger(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::string filename, bool fzero = 0);
void AbcSolveBdd(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result);
