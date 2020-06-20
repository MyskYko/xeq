#pragma once

#include <iostream>
#include <algorithm>

#include "node.h"
#include "AtBddMan.hpp"
  
template <typename node>
void Build(nodecircuit::NodeVector const &gates, Bdd::BddMan<node> &bdd, std::map<nodecircuit::Node *, int> &nfanout, std::map<nodecircuit::Node *, node> &f, std::map<nodecircuit::Node *, node> &g) {
  int count = gates.size();
  for(auto p : gates) {
    std::cout << "processing gate " << count-- << std::endl;
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
      f[p] = bdd.Not(f[p->inputs[0]]);
      g[p] = g[p->inputs[0]];
      break;
    case nodecircuit::NODE_AND:
      f[p] = bdd.Const1();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(f[p], g[q]),
			     bdd.And(f[q], g[p])),
		      bdd.And(g[p], g[q]));
	f[p] = bdd.And(f[p], f[q]);
      }
      break;
    case nodecircuit::NODE_NAND:
      f[p] = bdd.Const1();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(f[p], g[q]),
			     bdd.And(f[q], g[p])),
		      bdd.And(g[p], g[q]));
	f[p] = bdd.And(f[p], f[q]);
      }
      f[p] = bdd.Not(f[p]);
      break;
    case nodecircuit::NODE_OR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(bdd.Not(f[p]), g[q]),
			     bdd.And(bdd.Not(f[q]), g[p])),
		      bdd.And(g[p], g[q]));
	f[p] = bdd.Or(f[p], f[q]);
      }
      break;
    case nodecircuit::NODE_NOR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	g[p] = bdd.Or(bdd.Or(bdd.And(bdd.Not(f[p]), g[q]),
			     bdd.And(bdd.Not(f[q]), g[p])),
		      bdd.And(g[p], g[q]));
	f[p] = bdd.Or(f[p], f[q]);
      }
      f[p] = bdd.Not(f[p]);
      break;
    case nodecircuit::NODE_XOR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	f[p] = bdd.Xor(f[p], f[q]);
	g[p] = bdd.Or(g[p], g[q]);
      }
      break;
    case nodecircuit::NODE_XNOR:
      f[p] = bdd.Const0();
      g[p] = bdd.Const0();
      for(auto q : p->inputs) {
	f[p] = bdd.Xor(f[p], f[q]);
	g[p] = bdd.Or(g[p], g[q]);
      }
      f[p] = bdd.Not(f[p]);
      break;
    case nodecircuit::NODE_DC:
      f[p] = f[p->inputs[0]];
      g[p] = bdd.Or(bdd.Or(g[p->inputs[0]],
			   f[p->inputs[1]]),
		    g[p->inputs[1]]);
      break;
    case nodecircuit::NODE_MUX:
      // Xthen=1, Yelse=0, C=2
      f[p] = bdd.Ite(f[p->inputs[2]], f[p->inputs[1]], f[p->inputs[0]]);
      g[p] = bdd.Or(bdd.Ite(f[p->inputs[2]],
			    g[p->inputs[1]],
			    g[p->inputs[0]]),
		    bdd.And(g[p->inputs[2]],
			    bdd.Or(bdd.Or(g[p->inputs[1]],
					  g[p->inputs[0]]),
				   bdd.Xor(f[p->inputs[1]],
					   f[p->inputs[0]]))));
      break;
    default:
      throw "unkown gate type";
      break;
    }
    for(auto q : p->inputs) {
      nfanout[q]--;
      if(nfanout[q] == 0) {
	f.erase(q);
	g.erase(q);
      }
    }
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
  
  nodecircuit::NodeVector ggates;
  gf.GetGates(ggates);
  std::map<nodecircuit::Node *, int> gnfanout;
  for(auto p : gf.inputs) {
    gnfanout[p] = p->outputs.size();
  }
  for(auto p : ggates) {
    gnfanout[p] = p->outputs.size();
  }
  for(auto p : gf.outputs) {
    gnfanout[p]++;
  }
  nodecircuit::NodeVector rgates;
  rf.GetGates(rgates);
  std::map<nodecircuit::Node *, int> rnfanout;
  for(auto p : rf.inputs) {
    rnfanout[p] = p->outputs.size();
  }
  for(auto p : rgates) {
    rnfanout[p] = p->outputs.size();
  }
  for(auto p : rf.outputs) {
    rnfanout[p]++;
  }

  std::map<nodecircuit::Node *, node> gmf;
  std::map<nodecircuit::Node *, node> gmg;
  std::map<nodecircuit::Node *, node> rmf;
  std::map<nodecircuit::Node *, node> rmg;
  for(int i = 0; i < gf.inputs.size(); i++) {
    gmf[gf.inputs[i]] = bdd.IthVar(i);
    gmg[gf.inputs[i]] = bdd.Const0();
    rmf[rf.inputs[i]] = bdd.IthVar(i);
    rmg[rf.inputs[i]] = bdd.Const0();
  }

  Build(ggates, bdd, gnfanout, gmf, gmg);
  Build(rgates, bdd, rnfanout, rmf, rmg);
  
  for(int i = 0; i < gf.outputs.size(); i++) {
    auto gff = gmf[gf.outputs[i]];
    auto gfg = gmg[gf.outputs[i]];
    auto rff = rmf[rf.outputs[i]];
    auto rfg = rmg[rf.outputs[i]];
    auto eq = bdd.Or(gfg,
		     bdd.And(bdd.Not(rfg),
			     bdd.Xnor(gff, rff)));
    if(!(eq == bdd.Const1())) {
      result.resize(gf.inputs.size());
      if(!get_cex(bdd, eq, result)) {
	throw "No counter example";
      }
      break;
    }
  }
}
