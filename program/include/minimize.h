#pragma once

#include <string>
#include <vector>
#include <assert.h>

extern void Verilog2BLIF(std::string filename, std::vector<std::string> &inputs, std::vector<std::string> &outputs, std::vector<std::string> &dc);
extern void BLIF2Verilog(std::string blifname, std::string verilogname, std::vector<std::string> inputs, std::vector<std::string> outputs, std::vector<std::string> dc);
extern void Minimize(std::string filename)
