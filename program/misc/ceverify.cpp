#include <iostream>
#include <fstream>
#include <algorithm>

#include "node.h"

int main(int argc, char **argv) {
  if(argc < 4) {
    std::cout << "./ceverify <golden.v> <revised.v> <counter example>" << std::endl;
    return 1;
  }
  std::string gname(argv[1]);
  std::string rname(argv[2]);
  std::string oname(argv[3]);
  std::vector<std::string> input_names;
  std::vector<bool> result;

  nodecircuit::Circuit g;
  g.ReadVerilog(gname);
  nodecircuit::Circuit r;
  r.ReadVerilog(rname);

  if(g.inputs.size() != r.inputs.size()) {
    std::cout << "different primary inputs number" << std::endl;
    return 1;
  }
  std::sort(g.inputs.begin(), g.inputs.end(), [](auto const &x, auto const &y) { return ( x->name < y->name ); } );
  std::sort(r.inputs.begin(), r.inputs.end(), [](auto const &x, auto const &y) { return ( x->name < y->name ); } );
  for(int i = 0; i < g.inputs.size(); i++) {
    if(g.inputs[i]->name != r.inputs[i]->name) {
      std::cout << "different input names" << std::endl;
      return 1;
    }
    input_names.push_back(g.inputs[i]->name);
  }
  if(g.outputs.size() != r.outputs.size()) {
    std::cout << "different primary outputs number" << std::endl;
    return 1;
  }
  std::sort(g.outputs.begin(), g.outputs.end(), [](auto const &x, auto const &y) { return ( x->name < y->name ); } );
  std::sort(r.outputs.begin(), r.outputs.end(), [](auto const &x, auto const &y) { return ( x->name < y->name ); } );
  for(int i = 0; i < g.outputs.size(); i++) {
    if(g.outputs[i]->name != r.outputs[i]->name) {
      std::cout << "different output names" << std::endl;
    }
  }

  std::ifstream f(oname);
  if(!f) {
    std::cout << "cannot open " << oname << std::endl;
    return 1;
  }
  {
    std::string s;
    std::getline(f, s);
    if(s == "EQ") {
      std::cout << "EQ cannot be verified" << std::endl;
      return 1;
    }
    if(s != "NEQ") {
      std::cout << "malformed input" << std::endl;
      return 1;
    }
    std::vector<int> pat(g.inputs.size());
    while(std::getline(f, s)) {
      auto pos = s.find(" ");
      std::string name = s.substr(0, pos);
      int value = std::stoi(s.substr(pos + 1));
      for(int i = 0; i < g.inputs.size(); i++) {
	if(g.inputs[i]->name == name) {
	  pat[i] = value;
	  break;
	}
	if(i == g.inputs.size() - 1) {
	  std::cout << "malformed input" << std::endl;
	  return 1;
	}
      }
    }
    std::vector<int> gfs, ggs, rfs, rgs;
    g.Simulate(pat, gfs, ggs);
    r.Simulate(pat, rfs, rgs);
    for(int i = 0; i < g.outputs.size(); i++) {
      if(ggs[i] & 1) {
	continue;
      }
      if((rgs[i] & 1) || (gfs[i] & 1) != (rfs[i] & 1)) {
	std::cout << "Correct counter example" << std::endl;
	return 0;
      }
    }
    std::cout << "Wrong counter example" << std::endl;
    std::cout << "output values" << std::endl;
    for(int i = 0; i < g.outputs.size(); i++) {
      if(ggs[i] & 1) {
	std::cout << "x";
      }
      else {
	std::cout << (gfs[i] & 1);
      }
      std::cout << " ";
      if(rgs[i] & 1) {
	std::cout << "x";
      }
      else {
	std::cout << (rfs[i] & 1);
      }
      std::cout << std::endl;
    }
  }
  
  return 0;
}
