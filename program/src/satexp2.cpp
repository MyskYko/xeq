#include <iostream>
#include <functional>
#include <cassert>

#include <simp/SimpSolver.h>

#include "satsolve.h"

std::vector<int> inputvariables;

extern void And2(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c);
extern void Or2(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c);
extern void Xor2(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c);
extern void OrN(Glucose::SimpSolver &S, Glucose::vec<Glucose::Lit> &v, Glucose::Lit r);

void Ite(Glucose::SimpSolver &S, Glucose::Lit c, Glucose::Lit t, Glucose::Lit e, Glucose::Lit r) {
  S.addClause(~c, ~t, r);
  S.addClause(~c, t, ~r);
  S.addClause(c, ~e, r);
  S.addClause(c, e, ~r);
  S.addClause(~t, ~e, r);
  S.addClause(t, e, ~r);
}

void SatExp2(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding, FILE *dumpdimacs) {
  // create miter circuit
  nodecircuit::Circuit miter;
  nodecircuit::Miter(gf, rf, miter);
  // prepare sat solver and node2index map
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;
  std::map<nodecircuit::Node *, Glucose::Lit> f;
  std::map<nodecircuit::Node *, Glucose::Lit> g;
  Glucose::Lit c0 = Glucose::mkLit(S.newVar());
  S.addClause(~c0);
  // inputs
  for(auto p : miter.inputs) {
    f[p] = Glucose::mkLit(S.newVar());
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
	f[p] = ~c0;
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
	  f[p] = Glucose::mkLit(S.newVar());
	  break;
	default:
	  throw "undefined gate type";
	}
	g[p] = ~c0;
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
	f[p] = f[p->inputs[0]] ^ isNot;
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
	Glucose::Lit in0 = f[p->inputs[0]] ^ isOr;
	Glucose::Lit in0x = g[p->inputs[0]];
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = f[p->inputs[i]] ^ isOr;
	  Glucose::Lit in1x = g[p->inputs[i]];
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Glucose::Lit outx = Glucose::mkLit(S.newVar());
	  switch(gate_encoding) {
	  case 0:
	  case 1:
	  case 2:
	    And2(S, in0, in1, out);
	    break;
	  case 3:
	    S.addClause(~outx, ~out);
	  case 4:
	    clause.clear();
	    clause.push(outx);
	    clause.push(~in0);
	    clause.push(~in1);
	    clause.push(out);
	    S.addClause(clause);
	    S.addClause(outx, in0, ~out);
	    S.addClause(outx, in1, ~out);
	    break;
	  default:
	    throw "undefined gate type";
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  And2(S, in0x, in1x, t0);
	  And2(S, in0, in1x, t1);
	  And2(S, in0x, in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  OrN(S, clause, outx);
	  in0 = out;
	  in0x = outx;
	}
	g[p] = in0x;
	in0 = in0 ^ isNot ^ isOr;
	switch(gate_encoding) {
	  case 0:
	  case 3:
	  case 4:
	    f[p] = in0;
	    break;
	  case 1:
	  case 2:
	    f[p] = Glucose::mkLit(S.newVar());
	    S.addClause(g[p], ~in0, f[p]);
	    S.addClause(g[p], in0, ~f[p]);
	    if(gate_encoding == 1) {
	      S.addClause(~g[p], ~f[p]);
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
	Glucose::Lit in0 = f[p->inputs[0]];
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = f[p->inputs[i]];
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(g[q]);
	}
	g[p] = Glucose::mkLit(S.newVar());
	OrN(S, clause, g[p]);
	in0 = in0 ^ isNot;
	switch(gate_encoding) {
	  case 0:
	    f[p] = in0;
	    break;
	  case 1:
	  case 2:
	  case 3:
	  case 4:
	    f[p] = Glucose::mkLit(S.newVar());
	    S.addClause(g[p], ~in0, f[p]);
	    S.addClause(g[p], in0, ~f[p]);
	    if(gate_encoding == 1 || gate_encoding == 3) {
	      S.addClause(~g[p], ~f[p]);
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
      clause.push(g[p->inputs[0]]);
      clause.push(f[p->inputs[1]]);
      clause.push(g[p->inputs[1]]);
      g[p] = Glucose::mkLit(S.newVar());
      OrN(S, clause, g[p]);
      switch(gate_encoding) {
      case 0:
	f[p] = f[p->inputs[0]];
	break;
      case 1:
      case 2:
	f[p] = Glucose::mkLit(S.newVar());
	S.addClause(g[p], ~f[p->inputs[0]], f[p]);
	S.addClause(g[p], f[p->inputs[0]], ~f[p]);
	if(gate_encoding == 1) {
	  S.addClause(~g[p], ~f[p]);
	}
	break;
      case 3:
      case 4:
	f[p] = Glucose::mkLit(S.newVar());
	clause.clear();
	clause.push(g[p->inputs[0]]);
	clause.push(f[p->inputs[1]]);
	clause.push(g[p->inputs[1]]);
	clause.push(~f[p->inputs[0]]);
	clause.push(f[p]);
	S.addClause(clause);
	clause.pop();clause.pop();
	clause.push(f[p->inputs[0]]);
	clause.push(~f[p]);
	S.addClause(clause);
	if(gate_encoding == 3) {
	  S.addClause(~g[p->inputs[0]], ~f[p]);
	  S.addClause(~f[p->inputs[1]], ~f[p]);
	  S.addClause(~g[p->inputs[1]], ~f[p]);
	}
	break;
      default:
	throw "undefined gate type";
      }
      break;
    case nodecircuit::NODE_MUX:
      assert(p->inputs.size() == 3);
      {
	Glucose::Lit in0 = f[p->inputs[0]];
	Glucose::Lit in0x = g[p->inputs[0]];
	Glucose::Lit in1 = f[p->inputs[1]];
	Glucose::Lit in1x = g[p->inputs[1]];
	Glucose::Lit in2 = f[p->inputs[2]];
	Glucose::Lit in2x = g[p->inputs[2]];
	g[p] = Glucose::mkLit(S.newVar());
	// S = 0
	clause.clear();
	clause.push(in2);
	clause.push(in2x);
	clause.push(~in0x);
	clause.push(g[p]);
	S.addClause(clause);
	clause.pop();clause.pop();
	clause.push(in0x);
	clause.push(~g[p]);
	S.addClause(clause);
	// S = 1
	clause.clear();
	clause.push(~in2);
	clause.push(in2x);
	clause.push(~in1x);
	clause.push(g[p]);
	S.addClause(clause);
	clause.pop();clause.pop();
	clause.push(in1x);
	clause.push(~g[p]);
	S.addClause(clause);
	// S = x
	clause.clear();
	clause.push(~in2x);
	clause.push(g[p]);
	clause.push(in0);
	clause.push(~in1);
	S.addClause(clause);
	clause.pop();clause.pop();
	clause.push(~in0);
	clause.push(in1);
	S.addClause(clause);
	S.addClause(~in2x, ~in0x, g[p]);
	S.addClause(~in2x, ~in1x, g[p]);
	// regardless S (necessary)
	clause.clear();
	clause.push(in0x);
	clause.push(in1x);
	clause.push(~g[p]);
	clause.push(~in0);
	clause.push(~in1);
	S.addClause(clause);
	clause.pop();clause.pop();
	clause.push(in0);
	clause.push(in1);
	S.addClause(clause);
	// regardless S (unnecessary but maybe helpful)
	S.addClause(~in0x, ~in1x, g[p]);
	f[p] = Glucose::mkLit(S.newVar());
	switch(gate_encoding) {
	case 0:
	  Ite(S, in2, in1, in0, f[p]);
	  break;
	case 1:
	case 2:
	  {
	    Glucose::Lit t = Glucose::mkLit(S.newVar());
	    Ite(S, in2, in1, in0, t);
	    S.addClause(g[p], ~t, f[p]);
	    S.addClause(g[p], t, ~f[p]);
	    if(gate_encoding == 1) {
	      S.addClause(~g[p], ~f[p]);
	    }
	    break;
	  }
	case 3:
	case 4:
	  // S = 0
	  clause.clear();
	  clause.push(in2);
	  clause.push(in2x);
	  clause.push(in0x);
	  clause.push(~in0);
	  clause.push(f[p]);
	  S.addClause(clause);
	  clause.pop();clause.pop();
	  clause.push(in0);
	  clause.push(~f[p]);
	  S.addClause(clause);
	  // S = 1
	  clause.clear();
	  clause.push(~in2);
	  clause.push(in2x);
	  clause.push(in1x);
	  clause.push(~in1);
	  clause.push(f[p]);
	  S.addClause(clause);
	  clause.pop();	clause.pop();
	  clause.push(in1);
	  clause.push(~f[p]);
	  S.addClause(clause);
	  // S = x
	  if(gate_encoding == 3) {
	    clause.clear();
	    clause.push(~in2x);
	    clause.push(~f[p]);
	    clause.push(in0);
	    clause.push(~in1);
	    S.addClause(clause);
	    clause.pop();clause.pop();
	    clause.push(~in0);
	    clause.push(in1);
	    S.addClause(clause);
	    S.addClause(~in2x, ~in0x, ~f[p]);
	    S.addClause(~in2x, ~in1x, ~f[p]);
	  }
	  // regardless S (necessary)
	  clause.clear();
	  clause.push(in0x);
	  clause.push(in1x);
	  clause.push(~in0);
	  clause.push(~in1);
	  clause.push(f[p]);
	  S.addClause(clause);
	  clause.pop();clause.pop();clause.pop();
	  clause.push(in0);
	  clause.push(in1);
	  clause.push(~f[p]);
	  S.addClause(clause);
	  // regardless S (unnecessary but maybe helpful)
	  if(gate_encoding == 3) {
	    S.addClause(~in0x, ~in1x, ~f[p]);
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
    Glucose::Lit o = Glucose::mkLit(S.newVar());
    Xor2(S, f[p], f[q], o);
    clause.push(o);
  }
  S.addClause(clause);
  if(dumpdimacs) {
    inputvariables.clear();
    Glucose::vec<Glucose::Lit> as;
    Glucose::vec<Glucose::Var> vmap;
    S.toDimacs(dumpdimacs, as, vmap);
    for(auto p : miter.inputs) {
      Glucose::Var v = Glucose::var(f[p]);
      if(vmap.size() > v && vmap[v] != -1) {
	inputvariables.push_back(vmap[v]);
      }
      else {
	if(S.value(v) == l_True) {
	  inputvariables.push_back(-1);
	}
	else {
	  assert(S.value(v) == l_False);
	  inputvariables.push_back(-2);
	}
      }
    }
    return;
  }
  // solve
  bool r = S.solve();
  if(r) {
    for(auto p : miter.inputs) {
      if(S.model[Glucose::var(f[p])] == l_True) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
  }
}
