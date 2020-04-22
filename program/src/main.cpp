#include <iostream>
#include "node.h"


int main(int argc, char **argv) {
  if(argc < 2) return 0;
  std::string fname(argv[1]);
  nodecircuit::Circuit c;
  try {
    c.ReadVerilog(fname);
    nodecircuit::NodeVector gates;
    c.GetGates(gates);
    
  }
  catch(std::string e) {
    std::cout << "error : " << e << std::endl;
  }
  catch(const char *e) {
    std::cout << "error : " << e << std::endl;
  }
  catch(...) {
    std::cout << "error" << std::endl;
  }
  
  return 0;
}
