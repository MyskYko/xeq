#pragma once

#include <iostream>
#include <optional>
#include <algorithm>

#include "node.h"
#include "AtBddMan.hpp"

template <typename node>
void Build(nodecircuit::Circuit &c, Bdd::BddMan<node> &bdd, std::vector<node> &fs, std::vector<node> &gs) {
  nodecircuit::NodeVector gates;
  c.GetGates(gates);
  std::map<nodecircuit::Node *, int > nfanout;
  for(auto p : c.inputs) {
    nfanout[p] = p->outputs.size();
  }
  for(auto p : gates) {
    nfanout[p] = p->outputs.size();
  }
  for(auto p : c.outputs) {
    nfanout[p]++;
  }
  std::map<nodecircuit::Node *, std::optional<node> > f;
  std::map<nodecircuit::Node *, std::optional<node> > g;
  for(int i = 0; i < c.inputs.size(); i++) {
    f[c.inputs[i]] = bdd.IthVar(i);
    g[c.inputs[i]] = bdd.Const0();
  }
  int count = gates.size();
  for(auto p : gates) {
    //std::cout << "processing gate " << count-- << std::endl;
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if(p->name == "1'b1") {
	f[p] = bdd.Const1();
	g[p] = bdd.Const0();
      }
      else if(p->name == "1'b0") {
	f[p] = bdd.Const0();
	g[p] = bdd.Const0();
      }
      else if(p->name == "1'bx") {
	f[p] = bdd.Const0();
	g[p] = bdd.Const1();
      }
      break;
    case nodecircuit::NODE_BUF:
      f[p] = f[p->inputs[0]];
      g[p] = g[p->inputs[0]];
      break;
    case nodecircuit::NODE_NOT:
      f[p] = bdd.Not(*f[p->inputs[0]]);
      g[p] = g[p->inputs[0]];
      break;
    case nodecircuit::NODE_AND:
      f[p] = bdd.Const1();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(*f[p], *g[q]),
			     bdd.And(*f[q], *g[p])),
		      bdd.And(*g[p], *g[q]));
	f[p] = bdd.And(*f[p], *f[q]);
      }
      break;
    case nodecircuit::NODE_NAND:
      f[p] = bdd.Const1();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(*f[p], *g[q]),
			     bdd.And(*f[q], *g[p])),
		      bdd.And(*g[p], *g[q]));
	f[p] = bdd.And(*f[p], *f[q]);
      }
      f[p] = bdd.Not(*f[p]);
      break;
    case nodecircuit::NODE_OR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(bdd.Not(*f[p]), *g[q]),
			     bdd.And(bdd.Not(*f[q]), *g[p])),
		      bdd.And(*g[p], *g[q]));
	f[p] = bdd.Or(*f[p], *f[q]);
      }
      break;
    case nodecircuit::NODE_NOR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(bdd.Not(*f[p]), *g[q]),
			     bdd.And(bdd.Not(*f[q]), *g[p])),
		      bdd.And(*g[p], *g[q]));
	f[p] = bdd.Or(*f[p], *f[q]);
      }
      f[p] = bdd.Not(*f[p]);
      break;
    case nodecircuit::NODE_XOR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	f[p] = bdd.Xor(*f[p], *f[q]);
	g[p] = bdd.Or(*g[p], *g[q]);
      }
      break;
    case nodecircuit::NODE_XNOR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	f[p] = bdd.Xor(*f[p], *f[q]);
	g[p] = bdd.Or(*g[p], *g[q]);
      }
      f[p] = bdd.Not(*f[p]);
      break;
    case nodecircuit::NODE_DC:
      f[p] = *f[p->inputs[0]];
      g[p] = bdd.Or(bdd.Or(*g[p->inputs[0]],
			   *f[p->inputs[1]]),
		    *g[p->inputs[1]]);
      break;
    case nodecircuit::NODE_MUX:
      // Xthen=1, Yelse=0, C=2
      f[p] = bdd.Ite(*f[p->inputs[2]], *f[p->inputs[1]], *f[p->inputs[0]]);
      g[p] = bdd.Or(bdd.Ite(*f[p->inputs[2]],
			    *g[p->inputs[1]],
			    *g[p->inputs[0]]),
		    bdd.And(*g[p->inputs[2]],
			    bdd.Or(bdd.Or(*g[p->inputs[1]],
					  *g[p->inputs[0]]),
				   bdd.Xor(*f[p->inputs[1]],
					   *f[p->inputs[0]]))));
      break;
    default:
      throw "unkown gate type";
      break;
    }
    for(auto q : p->inputs) {
      nfanout[q]--;
      if(nfanout[q] == 0) {
	f[q] = std::nullopt;
	g[q] = std::nullopt;
      }
    }
  }
  fs.clear();
  gs.clear();
  for(auto p : c.outputs) {
    fs.push_back(*f[p]);
    gs.push_back(*g[p]);
  }
}

template <typename node>
bool get_cex(Bdd::BddMan<node> &bdd, node x, std::vector<bool> &v) {
  if(x == bdd.Const0()) return 1;
  if(x == bdd.Const1()) return 0;
  v[bdd.Var(x)] = 1;
  if(get_cex(bdd, bdd.Then(x), v)) return 1;
  v[bdd.Var(x)] = 0;
  if(get_cex(bdd, bdd.Else(x), v)) return 1;
  return 0;
}

void BddSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result) {
  Bdd::AtBddParam p;
  p.nNodes = 8192;
  p.nUnique = 2097152;
  p.nCache = 16384;
  p.nUniqueMinRate = 11;
  p.nCallThold = 33382;
  p.fRealloc = 1;
  p.fGC = 1;
  p.nGC = 744068;
  p.nReo = 1000;
  p.nMaxGrowth = 59;
  Bdd::AtBddMan bdd(gf.inputs.size(), p);
  bdd.Dvr();
  using node = Bdd::AtBddNode;

  std::vector<node> gffs;
  std::vector<node> gfgs;
  Build(gf, bdd, gffs, gfgs);
  std::vector<node> rffs;
  std::vector<node> rfgs;
  Build(rf, bdd, rffs, rfgs);
  
  for(int i = 0; i < gf.outputs.size(); i++) {
    auto eq = bdd.Or(gfgs[i],
		     bdd.And(bdd.Not(rfgs[i]),
			     bdd.Or(bdd.And(gffs[i],
					    rffs[i]),
				    bdd.And(bdd.Not(gffs[i]),
					    bdd.Not(rffs[i])))));
    if(!(eq == bdd.Const1())) {
      result.resize(gf.inputs.size());
      if(!get_cex(bdd, eq, result)) {
	throw "No counter example";
      }
      break;
    }
  }
}
