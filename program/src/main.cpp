#include <iostream>
#include <fstream>
#include <algorithm>

#include "node.h"

int main(int argc, char **argv) {
  if(argc < 4) {
    std::cout << "./xeq <golden.v> <revised.v> <output>" << std::endl;
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
  
  // Solve(g, r, result);

  std::ofstream f(oname);
  if(!f) {
    std::cout << "cannot open " << oname << std::endl;
    return 1;
  }
  if(result.empty()) {
    f << "EQ" << std::endl;
  }
  else {
    f << "NEQ" << std::endl;
    for(int i = 0; i < result.size(); i++) {
      f << input_names[i] << " " << result[i] << std::endl;
    }
  }
  
  return 0;
}
