#include <iostream>
#include <functional>
#include <cstring>
#include <cassert>

#include <cadical.hpp>
extern "C" {
#include <kissat.h>
#include <application.h>
}

#include "satsolve.h"

void Add(CaDiCaL::Solver &S, int i) {
  S.add(i);
}
int Solve(CaDiCaL::Solver &S) {
  return S.solve();
}
bool Value(CaDiCaL::Solver &S, int i) {
  return S.val(i) > 0;
}

void Add(kissat *S, int i) {
  kissat_add(S, i);
}
int Solve(kissat *S) {
  return kissat_solve(S);
}
bool Value(kissat *S, int i) {
  return kissat_value(S, i) > 0;
}

template <typename solver>
void AddClause(solver &S, std::vector<int> const &v) {
  for(int e : v) {
    Add(S, e);
  }
  Add(S, 0);
}

template <typename solver>
void And2(solver &S, int a, int b, int c) {
  Add(S, a), Add(S, -c), Add(S, 0);
  Add(S, b), Add(S, -c), Add(S, 0);
  Add(S, -a), Add(S, -b), Add(S, c), Add(S, 0);
}
template <typename solver>
void Or2(solver &S, int a, int b, int c) {
  And2(S, -a, -b, -c);
}
template <typename solver>
void Xor2(solver &S, int a, int b, int c) {
  Add(S, a), Add(S, b), Add(S, -c), Add(S, 0);
  Add(S, -a), Add(S, -b), Add(S, -c), Add(S, 0);
  Add(S, -a), Add(S, b), Add(S, c), Add(S, 0);
  Add(S, a), Add(S, -b), Add(S, c), Add(S, 0);
}
template <typename solver>
void OrN(solver &S, std::vector<int> &v, int r) {
  for(int i = 0; i < v.size(); i++) {
    Add(S, -v[i]), Add(S, r), Add(S, 0);
  }
  v.push_back(-r);
  AddClause(S, v);
  v.pop_back();
}
template <typename solver>
void Ite(solver &S, int c, int t, int e, int r) {
  Add(S, -c), Add(S, -t), Add(S, r), Add(S, 0);
  Add(S, -c), Add(S, t), Add(S, -r), Add(S, 0);
  Add(S, c), Add(S, -e), Add(S, r), Add(S, 0);
  Add(S, c), Add(S, e), Add(S, -r), Add(S, 0);
  Add(S, -t), Add(S, -e), Add(S, r), Add(S, 0);
  Add(S, t), Add(S, e), Add(S, -r), Add(S, 0);
}

template <typename solver>
int SatSolve2(solver &S, nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding) {
  // create miter circuit
  nodecircuit::Circuit miter;
  nodecircuit::Miter(gf, rf, miter);
  // prepare node2index map
  std::vector<int> clause;
  std::map<nodecircuit::Node *, int> f;
  std::map<nodecircuit::Node *, int> g;
  int nVars = 0;
  int c0 = ++nVars;
  Add(S, -c0), Add(S, 0);
  // inputs
  for(auto p : miter.inputs) {
    f[p] = ++nVars;
    g[p] = c0;
  }
  // gates
  nodecircuit::NodeVector gates;
  miter.GetGates(gates);
  for(auto p: gates) {
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if (p->name == "1'b0") {
	f[p] = c0;
	g[p] = c0;
      }
      else if(p->name == "1'b1") {
	f[p] = -c0;
	g[p] = c0;
      }
      else if(p->name == "1'bx") {
	switch(gate_encoding) {
	case 0:
	case 1:
	case 3:
	  f[p] = c0;
	  break;
	case 2:
	case 4:
	  f[p] = ++nVars;
	  break;
	default:
	  throw "undefined gate type";
	}
	g[p] = -c0;
      }
      else {
	throw "invalid constant";
      }
      break;
    case nodecircuit::NODE_BUF:
    case nodecircuit::NODE_NOT:
      assert(p->inputs.size() == 1);
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	f[p] = isNot? -f[p->inputs[0]]: f[p->inputs[0]];
	g[p] = g[p->inputs[0]];
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
        bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	int in0 = isOr? -f[p->inputs[0]]: f[p->inputs[0]];
	int in0x = g[p->inputs[0]];
	for(int i = 1; i < p->inputs.size(); i++) {
	  int in1 = isOr? -f[p->inputs[i]]: f[p->inputs[i]];
	  int in1x = g[p->inputs[i]];
	  int out = ++nVars;
	  int outx = ++nVars;
	  switch(gate_encoding) {
	  case 0:
	  case 1:
	  case 2:
	    And2(S, in0, in1, out);
	    break;
	  case 3:
	    Add(S, -outx), Add(S, -out), Add(S, 0);
	  case 4:
	    clause.clear();
	    clause.push_back(outx);
	    clause.push_back(-in0);
	    clause.push_back(-in1);
	    clause.push_back(out);
	    AddClause(S, clause);
	    Add(S, outx), Add(S, in0), Add(S, -out), Add(S, 0);
	    Add(S, outx), Add(S, in1), Add(S, -out), Add(S, 0);
	    break;
	  default:
	    throw "undefined gate type";
	  }
	  int t0 = ++nVars;
	  int t1 = ++nVars;
	  int t2 = ++nVars;
	  And2(S, in0x, in1x, t0);
	  And2(S, in0, in1x, t1);
	  And2(S, in0x, in1, t2);
	  clause.clear();
	  clause.push_back(t0);
	  clause.push_back(t1);
	  clause.push_back(t2);
	  OrN(S, clause, outx);
	  in0 = out;
	  in0x = outx;
	}
	g[p] = in0x;
	in0 = isNot ^ isOr? -in0: in0;
	switch(gate_encoding) {
	  case 0:
	  case 3:
	  case 4:
	    f[p] = in0;
	    break;
	  case 1:
	  case 2:
	    f[p] = ++nVars;
	    Add(S, g[p]), Add(S, -in0), Add(S, f[p]), Add(S, 0);
	    Add(S, g[p]), Add(S, in0), Add(S, -f[p]), Add(S, 0);
	    if(gate_encoding == 1) {
	      Add(S, -g[p]), Add(S, -f[p]), Add(S, 0);
	    }
	    break;
	  default:
	    throw "undefined gate type";
	}
	break;
      }
    case nodecircuit::NODE_XOR:
    case nodecircuit::NODE_XNOR:
      {
	bool isNot = p->type == nodecircuit::NODE_XNOR;
	int in0 = f[p->inputs[0]];
	for(int i = 1; i < p->inputs.size(); i++) {
	  int in1 = f[p->inputs[i]];
	  int out = ++nVars;
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push_back(g[q]);
	}
	g[p] = ++nVars;
	OrN(S, clause, g[p]);
	in0 = isNot? -in0: in0;
	switch(gate_encoding) {
	  case 0:
	    f[p] = in0;
	    break;
	  case 1:
	  case 2:
	  case 3:
	  case 4:
	    f[p] = ++nVars;
	    Add(S, g[p]), Add(S, -in0), Add(S, f[p]), Add(S, 0);
	    Add(S, g[p]), Add(S, in0), Add(S, -f[p]), Add(S, 0);
	    if(gate_encoding == 1 || gate_encoding == 3) {
	      Add(S, -g[p]), Add(S, -f[p]), Add(S, 0);
	    }
	    break;
	  default:
	    throw "undefined gate type";
	}
	break;
      }
    case nodecircuit::NODE_DC:
      assert(p->inputs.size() == 2);
      clause.clear();
      clause.push_back(g[p->inputs[0]]);
      clause.push_back(f[p->inputs[1]]);
      clause.push_back(g[p->inputs[1]]);
      g[p] = ++nVars;
      OrN(S, clause, g[p]);
      switch(gate_encoding) {
      case 0:
	f[p] = f[p->inputs[0]];
	break;
      case 1:
      case 2:
	f[p] = ++nVars;
	Add(S, g[p]), Add(S, -f[p->inputs[0]]), Add(S, f[p]), Add(S, 0);
	Add(S, g[p]), Add(S, f[p->inputs[0]]), Add(S, -f[p]), Add(S, 0);
	if(gate_encoding == 1) {
	  Add(S, -g[p]), Add(S, -f[p]), Add(S, 0);
	}
	break;
      case 3:
      case 4:
	f[p] = ++nVars;
	clause.clear();
	clause.push_back(g[p->inputs[0]]);
	clause.push_back(f[p->inputs[1]]);
	clause.push_back(g[p->inputs[1]]);
	clause.push_back(-f[p->inputs[0]]);
	clause.push_back(f[p]);
	AddClause(S, clause);
	clause.pop_back();clause.pop_back();
	clause.push_back(f[p->inputs[0]]);
	clause.push_back(-f[p]);
	AddClause(S, clause);
	if(gate_encoding == 3) {
	  Add(S, -g[p->inputs[0]]), Add(S, -f[p]), Add(S, 0);
	  Add(S, -f[p->inputs[1]]), Add(S, -f[p]), Add(S, 0);
	  Add(S, -g[p->inputs[1]]), Add(S, -f[p]), Add(S, 0);
	}
	break;
      default:
	throw "undefined gate type";
      }
      break;
    case nodecircuit::NODE_MUX:
      assert(p->inputs.size() == 3);
      {
	int in0 = f[p->inputs[0]];
	int in0x = g[p->inputs[0]];
	int in1 = f[p->inputs[1]];
	int in1x = g[p->inputs[1]];
	int in2 = f[p->inputs[2]];
	int in2x = g[p->inputs[2]];
	g[p] = ++nVars;
	// S = 0
	clause.clear();
	clause.push_back(in2);
	clause.push_back(in2x);
	clause.push_back(-in0x);
	clause.push_back(g[p]);
	AddClause(S, clause);
	clause.pop_back();clause.pop_back();
	clause.push_back(in0x);
	clause.push_back(-g[p]);
	AddClause(S, clause);
	// S = 1
	clause.clear();
	clause.push_back(-in2);
	clause.push_back(in2x);
	clause.push_back(-in1x);
	clause.push_back(g[p]);
	AddClause(S, clause);
	clause.pop_back();clause.pop_back();
	clause.push_back(in1x);
	clause.push_back(-g[p]);
	AddClause(S, clause);
	// S = x
	clause.clear();
	clause.push_back(-in2x);
	clause.push_back(g[p]);
	clause.push_back(in0);
	clause.push_back(-in1);
	AddClause(S, clause);
	clause.pop_back();clause.pop_back();
	clause.push_back(-in0);
	clause.push_back(in1);
	AddClause(S, clause);
	Add(S, -in2x), Add(S, -in0x), Add(S, g[p]), Add(S, 0);
	Add(S, -in2x), Add(S, -in1x), Add(S, g[p]), Add(S, 0);
	// regardless S (necessary)
	clause.clear();
	clause.push_back(in0x);
	clause.push_back(in1x);
	clause.push_back(-g[p]);
	clause.push_back(-in0);
	clause.push_back(-in1);
	AddClause(S, clause);
	clause.pop_back();clause.pop_back();
	clause.push_back(in0);
	clause.push_back(in1);
	AddClause(S, clause);
	// regardless S (unnecessary but maybe helpful)
	Add(S, -in0x), Add(S, -in1x), Add(S, g[p]), Add(S, 0);
	f[p] = ++nVars;
	switch(gate_encoding) {
	case 0:
	  Ite(S, in2, in1, in0, f[p]);
	  break;
	case 1:
	case 2:
	  {
	    int t = ++nVars;
	    Ite(S, in2, in1, in0, t);
	    Add(S, g[p]), Add(S, -t), Add(S, f[p]), Add(S, 0);
	    Add(S, g[p]), Add(S, t), Add(S, -f[p]), Add(S, 0);
	    if(gate_encoding == 1) {
	      Add(S, -g[p]), Add(S, -f[p]), Add(S, 0);
	    }
	    break;
	  }
	case 3:
	case 4:
	  // S = 0
	  clause.clear();
	  clause.push_back(in2);
	  clause.push_back(in2x);
	  clause.push_back(in0x);
	  clause.push_back(-in0);
	  clause.push_back(f[p]);
	  AddClause(S, clause);
	  clause.pop_back();clause.pop_back();
	  clause.push_back(in0);
	  clause.push_back(-f[p]);
	  AddClause(S, clause);
	  // S = 1
	  clause.clear();
	  clause.push_back(-in2);
	  clause.push_back(in2x);
	  clause.push_back(in1x);
	  clause.push_back(-in1);
	  clause.push_back(f[p]);
	  AddClause(S, clause);
	  clause.pop_back();	clause.pop_back();
	  clause.push_back(in1);
	  clause.push_back(-f[p]);
	  AddClause(S, clause);
	  // S = x
	  if(gate_encoding == 3) {
	    clause.clear();
	    clause.push_back(-in2x);
	    clause.push_back(-f[p]);
	    clause.push_back(in0);
	    clause.push_back(-in1);
	    AddClause(S, clause);
	    clause.pop_back();clause.pop_back();
	    clause.push_back(-in0);
	    clause.push_back(in1);
	    AddClause(S, clause);
	    Add(S, -in2x), Add(S, -in0x), Add(S, -f[p]), Add(S, 0);
	    Add(S, -in2x), Add(S, -in1x), Add(S, -f[p]), Add(S, 0);
	  }
	  // regardless S (necessary)
	  clause.clear();
	  clause.push_back(in0x);
	  clause.push_back(in1x);
	  clause.push_back(-in0);
	  clause.push_back(-in1);
	  clause.push_back(f[p]);
	  AddClause(S, clause);
	  clause.pop_back();clause.pop_back();clause.pop_back();
	  clause.push_back(in0);
	  clause.push_back(in1);
	  clause.push_back(-f[p]);
	  AddClause(S, clause);
	  // regardless S (unnecessary but maybe helpful)
	  if(gate_encoding == 3) {
	    Add(S, -in0x), Add(S, -in1x), Add(S, -f[p]), Add(S, 0);
	  }
	  break;
	default:
	  throw "undefined gate type";
	}
	break;
      }
    case nodecircuit::NODE_ISX:
      assert(p->inputs.size() == 1);
      f[p] = g[p->inputs[0]];
      g[p] = c0;
      break;
    default:
      throw "unknown gate type";
      break;
    }
  }
  // outputs
  clause.clear();
  for(int i = 0; i < miter.outputs.size(); i++) {
    auto p = miter.outputs[i++];
    auto q = miter.outputs[i];
    int o = ++nVars;
    Xor2(S, f[p], f[q], o);
    clause.push_back(o);
  }
  AddClause(S, clause);
  // solve
  int r = Solve(S);
  if(r == 10) {
    for(auto p : miter.inputs) {
      if(Value(S, f[p])) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
    return 0;
  }
  if(r == 20) {
    return 0;
  }
  return 1;
}

int CadicalSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding) {
  CaDiCaL::Solver S;
  return SatSolve2(S, gf, rf, result, gate_encoding);
}

int KissatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding, int target) {
  kissat *S = kissat_init();
  if(target == 1) {
    kissat_set_configuration(S, "sat");
  }
  else if(target == 2) {
    kissat_set_configuration(S, "unsat");
  }
  return SatSolve2(S, gf, rf, result, gate_encoding);
}

int CadicalExp(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding) {
  std::vector<int> inputs;
  SatExp2(gf, rf, result, gate_encoding, &inputs);
  CaDiCaL::Solver S;
  int vars;
  S.read_dimacs(dimacsname, vars);
  int r = Solve(S);
  if(r == 10) {
    for(int v : inputs) {
      if(v == -1) {
	result.push_back(1);
      }
      else if(v == -2) {
	result.push_back(0);
      }
      else if(Value(S, v + 1)) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
    return 0;
  }
  if(r == 20) {
    return 0;
  }
  return 1;
}

int KissatExp(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding, int target) {
  std::vector<int> inputs;
  SatExp2(gf, rf, result, gate_encoding, &inputs);
  kissat *S = kissat_init();
  if(target == 1) {
    kissat_set_configuration(S, "sat");
  }
  else if(target == 2) {
    kissat_set_configuration(S, "unsat");
  }
  char *argv[2];
  argv[0] = (char*)malloc(20);
  argv[1] = (char*)malloc(20);
  strcpy(argv[0], "hoge");
  strcpy(argv[1], dimacsname);
  int r = kissat_application(S, 2, argv);
  free(argv[0]);
  free(argv[1]);
  if(r == 10) {
    for(int v : inputs) {
      if(v == -1) {
	result.push_back(1);
      }
      else if(v == -2) {
	result.push_back(0);
      }
      else if(Value(S, v + 1)) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
    kissat_release(S);
    return 0;
  }
  if(r == 20) {
    kissat_release(S);
    return 0;
  }
  kissat_release(S);
  return 1;
}

