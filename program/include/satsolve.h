#pragma once

#include "node.h"

extern void SatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result);
extern void SatTest();
