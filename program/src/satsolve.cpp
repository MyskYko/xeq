#include <iostream>
#include <functional>
#include <cassert>

#include <simp/SimpSolver.h>

#include "satsolve.h"

void recursive_comb(int *indices, int s, int rest, std::function<void(int *)> f) {
  if(rest == 0) {
    f(indices);
  }
  else{
    if(s < 0) {
      return;
    }
    recursive_comb(indices, s - 1, rest, f);
    indices[rest - 1] = s;
    recursive_comb(indices, s - 1, rest - 1, f);
  }
}

inline void foreach_comb(int n, int k, std::function<void(int *)> f) {
  int indices[k];
  recursive_comb(indices, n - 1, k, f);
}

void XConstraints(nodecircuit::Circuit &f, Glucose::SimpSolver &S, int bias, nodecircuit::Node *p) {
  Glucose::vec<Glucose::Lit> clause;
  Glucose::vec<Glucose::Lit> clauseback;
  bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
  assert(isOr || p->type == nodecircuit::NODE_AND || p->type == nodecircuit::NODE_NAND);
  
  clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
  for (auto q: p->inputs) {
    clauseback.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)), isOr));
    clauseback.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)) + 1));
    clauseback.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
    S.addClause(clauseback);
    clauseback.clear();
    clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)) + 1));
  }	
  S.addClause(clause);
  clause.clear();
      
  for (auto q: p->inputs) {
    for (int i = 0; i <= p->inputs.size(); i++) {
      foreach_comb(p->inputs.size(), i, [&](int *indices) {
	  clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
	  clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)) + 1, 1));
	  int j = 0;
	  for (int k = 0; k < i; k++) {
	    while(j != indices[k]) {
	      assert(j < indices[k]);
	      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[j])->name)), !isOr));
	      j++;
	    }
	    assert(j == indices[k]);
	    clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[j])->name)) + 1, 1));
	    j++;
	  }
	  while(j < p->inputs.size()) {
	    clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[j])->name)), !isOr));
	    j++;
	  }
	  S.addClause(clause);
	  clause.clear();
	});
    }
  }
}

void Ckt2Cnf(nodecircuit::Circuit &f, Glucose::SimpSolver &S, int bias) {
  Glucose::vec<Glucose::Lit> clause;
  for (auto p: f.all_nodes) {
    if (p->is_input)
      continue;
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if (p->name == "1'b0") {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      }
      else if (p->name == "1'b1") {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      }
      else if (p->name == "1'bx") {	  
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
      assert(p->inputs.size() == 1);	
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)), 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));	
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1, 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name))), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      break;
    case nodecircuit::NODE_NOT:
      assert(p->inputs.size() == 1);
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)), 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));	
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1, 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name))), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      break;
    case nodecircuit::NODE_AND:
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name))), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));		 
	clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)), 1));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(f, S, bias, p);
      break;
    case nodecircuit::NODE_NAND:
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name))), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));		 
	clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)), 1));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(f, S, bias, p);
      break;
    case nodecircuit::NODE_OR:
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)), 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));		 
	clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name))));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(f, S, bias, p);
      break;
    case nodecircuit::NODE_NOR:
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)), 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));		 
	clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name))));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(f, S, bias, p);
      break;	
    case nodecircuit::NODE_XOR: {
      for (int i = 0; i <= p->inputs.size(); i++) {
	foreach_comb(p->inputs.size(), i, [&](int *indices) {
	    clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), !(i % 2)));
	    int j = 0;
	    for (int k = 0; k < i; k++) {
	      while(j != indices[k]) {
		assert(j < indices[k]);
		clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->inputs[j]->name))));
		j++;
	      }
	      assert(j == indices[k]);
	      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->inputs[j]->name)), 1));
	      j++;
	    }
	    while(j < p->inputs.size()) {
	      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->inputs[j]->name))));
	      j++;
	    }
	    S.addClause(clause);
	    clause.clear();
	  });
      }
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)) + 1, 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));		 
	clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)) + 1));
      }	
      S.addClause(clause);
      clause.clear();
      break;
    }
    case nodecircuit::NODE_XNOR: {
      for (int i = 0; i <= p->inputs.size(); i++) {
	foreach_comb(p->inputs.size(), i, [&](int *indices) {
	    clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), i % 2));
	    int j = 0;
	    for (int k = 0; k < i; k++) {
	      while(j != indices[k]) {
		assert(j < indices[k]);
		clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->inputs[j]->name))));
		j++;
	      }
	      assert(j == indices[k]);
	      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->inputs[j]->name)), 1));
	      j++;
	    }
	    while(j < p->inputs.size()) {
	      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->inputs[j]->name))));
	      j++;
	    }
	    S.addClause(clause);
	    clause.clear();
	  });
      }
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)) + 1, 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));		 
	clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(q->name)) + 1));
      }	
      S.addClause(clause);
      clause.clear();
      break;
    }
    case nodecircuit::NODE_DC:
      assert(p->inputs.size() == 2);
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1, 1));	
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)), 1));
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1, 1));	
      break;
    case nodecircuit::NODE_MUX:
      assert(p->inputs.size() == 3);
      // S = 0
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1)); 
      S.addClause(clause);
      clause.clear();
	
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1));       
      S.addClause(clause);
      clause.clear();

      // S = 1
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1));
      S.addClause(clause);
      clause.clear();

	
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1));
      S.addClause(clause);
      clause.clear();

      // S = x
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name))));	
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name))));	
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1, 1));	
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1, 1));	
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)), 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name))));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name))));	
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[1])->name)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[2])->name)) + 1, 1));       
      S.addClause(clause);
      clause.clear();
      break;
    case nodecircuit::NODE_ISX:
      assert(p->inputs.size() == 1);
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1, 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name))));	
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex((p->inputs[0])->name)) + 1), Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)), 1));
      S.addClause(Glucose::mkLit(2 * (bias + f.GetNodeIndex(p->name)) + 1, 1));
      break;
    default:
      assert(0);
      break;
    }
  }            
}

void SatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result) {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;
  
  // establish variables
  // each signal(before milter circuit) consists of two bits, if the second bit is 1, the value of the signal is x, despite the first bit 
  for (int i = 0; i < gf.all_nodes.size(); i++) { 
    S.newVar();
    S.newVar();
  }
  for (int i = 0; i < rf.all_nodes.size(); i++) {
    S.newVar();
    S.newVar();
  }
  // variables representing xor-ed results
  for (int i = 0; i < gf.outputs.size(); i++) 
    S.newVar();
    // variable representing mitered results
  S.newVar();
  
  // correlate inputs of the two circuits
  for (auto p: gf.inputs) {
    S.addClause(Glucose::mkLit(2 * gf.GetNodeIndex(p->name), 1), Glucose::mkLit(2 * (gf.all_nodes.size() + rf.GetNodeIndex(p->name))));    
    S.addClause(Glucose::mkLit(2 * gf.GetNodeIndex(p->name)), Glucose::mkLit(2 * (gf.all_nodes.size() + rf.GetNodeIndex(p->name)), 1));

    // for PIs, the values of the second bits are always 0
    S.addClause(Glucose::mkLit(2 * gf.GetNodeIndex(p->name) + 1, 1));
    S.addClause(Glucose::mkLit(2 * (gf.all_nodes.size() + rf.GetNodeIndex(p->name)) + 1, 1));
  }

  Ckt2Cnf(gf, S, 0);
  Ckt2Cnf(rf, S, gf.all_nodes.size());
  
  // milter outputs of the two circuits
  for (int i = 0; i < gf.outputs.size(); i++) {
    nodecircuit::Node *p = gf.outputs[i];
    // if one output of gf is x, that output is compatible equivalent to the corresponding output of rf
    S.addClause(Glucose::mkLit(i + 2 * (gf.all_nodes.size() + rf.all_nodes.size()), 1), Glucose::mkLit(2 * gf.GetNodeIndex(p->name) + 1, 1));

    // if one output of gf is not x, while the corresponding output of rf is x, then gf is not compatible equivalent to rf
    clause.push(Glucose::mkLit(i + 2 * (gf.all_nodes.size() + rf.all_nodes.size())));
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name) + 1));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name)) + 1, 1));
    S.addClause(clause);
    clause.clear();

    // if neither of the outputs of gf and rf is x, standard xor logic is adopted
    clause.push(Glucose::mkLit(i + 2 * (gf.all_nodes.size() + rf.all_nodes.size())));
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name) + 1));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name)) + 1));  
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name), 1));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name))));
    S.addClause(clause);
    clause.clear();
    
    clause.push(Glucose::mkLit(i + 2 * (gf.all_nodes.size() + rf.all_nodes.size())));
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name) + 1));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name)) + 1));  
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name)));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name)), 1));
    S.addClause(clause);
    clause.clear();

    clause.push(Glucose::mkLit(i + 2 * (gf.all_nodes.size() + rf.all_nodes.size()), 1));
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name) + 1));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name)) + 1));  
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name)));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name))));
    S.addClause(clause);
    clause.clear();

    clause.push(Glucose::mkLit(i + 2 * (gf.all_nodes.size() + rf.all_nodes.size()), 1));
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name) + 1));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name)) + 1));  
    clause.push(Glucose::mkLit(2 * gf.GetNodeIndex(p->name), 1));
    clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + gf.GetNodeIndex(p->name)), 1));
    S.addClause(clause);
    clause.clear();    
  }
  clause.push(Glucose::mkLit(2 * (gf.all_nodes.size() + rf.all_nodes.size()) + gf.outputs.size(), 1));
  for (int i = 0; i < gf.outputs.size(); i++) {
    S.addClause(Glucose::mkLit((i + 2 * (gf.all_nodes.size() + rf.all_nodes.size())), 1), Glucose::mkLit(2 * (gf.all_nodes.size() + rf.all_nodes.size()) + gf.outputs.size()));
    clause.push(Glucose::mkLit(i + 2 * (gf.all_nodes.size() + rf.all_nodes.size())));    
  }
  S.addClause(clause);
  clause.clear();
  S.addClause(Glucose::mkLit(2 * (gf.all_nodes.size() + rf.all_nodes.size()) + gf.outputs.size()));

  // solve the sat problem
  bool r = S.solve();
  if (r)
    for (auto p: gf.inputs) { 
      int i;
      i = gf.GetNodeIndex(p->name);      
      if(S.model[2 * i] == l_True) 
	result.push_back(1);
      else
	result.push_back(0);      
    }
}

void And2(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c) {
  S.addClause(a, ~c);
  S.addClause(b, ~c);
  S.addClause(~a, ~b, c);
}
void Or2(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c) {
  And2(S, ~a, ~b, ~c);
}
void Xor2(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c) {
  S.addClause(a, b, ~c);
  S.addClause(~a, ~b, ~c);
  S.addClause(~a, b, c);
  S.addClause(a, ~b, c);
}

void Ckt2Cnf2(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S, int bias) {
  Glucose::vec<Glucose::Lit> clause;
  for (auto p: gates) {
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if (p->name == "1'b0") {
	S.addClause(Glucose::mkLit(2 * (bias + m.at(p)), 1));
	S.addClause(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      }
      else if (p->name == "1'b1") {
	S.addClause(Glucose::mkLit(2 * (bias + m.at(p))));
	S.addClause(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      }
      else if (p->name == "1'bx") {	  
	S.addClause(Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
      assert(p->inputs.size() == 1);	
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])), 1), Glucose::mkLit(2 * (bias + m.at(p))));	
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1, 1), Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0]))), Glucose::mkLit(2 * (bias + m.at(p)), 1));
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1), Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      break;
    case nodecircuit::NODE_NOT:
      assert(p->inputs.size() == 1);
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])), 1), Glucose::mkLit(2 * (bias + m.at(p)), 1));	
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1, 1), Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0]))), Glucose::mkLit(2 * (bias + m.at(p))));
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1), Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      break;
    case nodecircuit::NODE_AND:
      {
	Glucose::Lit in0 = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])));
	Glucose::Lit in0x = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])));
	  Glucose::Lit in1x = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(2 * (bias + m.at(p)));
	    outx = Glucose::mkLit(2 * (bias + m.at(p)) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	  And2(S, in0, in1, out);
	  And2(S, in0x, in1x, t0);
	  And2(S, in0, in1x, t1);
	  And2(S, in0x, in1, t2);
	  Or2(S, t0, t1, t3);
	  Or2(S, t2, t3, outx);
	  in0 = out;
	  in0x = outx;
	}
	break;
      }
    case nodecircuit::NODE_NAND:
      {
	Glucose::Lit in0 = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])));
	Glucose::Lit in0x = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])));
	  Glucose::Lit in1x = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(2 * (bias + m.at(p)), 1);
	    outx = Glucose::mkLit(2 * (bias + m.at(p)) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	  And2(S, in0, in1, out);
	  And2(S, in0x, in1x, t0);
	  And2(S, in0, in1x, t1);
	  And2(S, in0x, in1, t2);
	  Or2(S, t0, t1, t3);
	  Or2(S, t2, t3, outx);
	  in0 = out;
	  in0x = outx;
	}
	break;
      }      
    case nodecircuit::NODE_OR:
      {
	Glucose::Lit in0 = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])));
	Glucose::Lit in0x = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])));
	  Glucose::Lit in1x = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(2 * (bias + m.at(p)));
	    outx = Glucose::mkLit(2 * (bias + m.at(p)) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	  Or2(S, in0, in1, out);
	  And2(S, in0x, in1x, t0);
	  And2(S, ~in0, in1x, t1);
	  And2(S, in0x, ~in1, t2);
	  Or2(S, t0, t1, t3);
	  Or2(S, t2, t3, outx);
	  in0 = out;
	  in0x = outx;
	}
	break;
      }
    case nodecircuit::NODE_NOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])));
	Glucose::Lit in0x = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])));
	  Glucose::Lit in1x = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(2 * (bias + m.at(p)), 1);
	    outx = Glucose::mkLit(2 * (bias + m.at(p)) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	  Or2(S, in0, in1, out);
	  And2(S, in0x, in1x, t0);
	  And2(S, ~in0, in1x, t1);
	  And2(S, in0x, ~in1, t2);
	  Or2(S, t0, t1, t3);
	  Or2(S, t2, t3, outx);
	  in0 = out;
	  in0x = outx;
	}
	break;
      }
    case nodecircuit::NODE_XOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])));
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])));
	  Glucose::Lit out;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(2 * (bias + m.at(p)));
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	  }
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(2 * (bias + m.at(q)) + 1, 1), Glucose::mkLit(2 * (bias + m.at(p)) + 1));		 
	  clause.push(Glucose::mkLit(2 * (bias + m.at(q)) + 1));
	}	
	S.addClause(clause);
	clause.clear();
	break;
      }
    case nodecircuit::NODE_XNOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(2 * (bias + m.at(p->inputs[0])));
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(2 * (bias + m.at(p->inputs[i])));
	  Glucose::Lit out;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(2 * (bias + m.at(p)), 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	  }
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(2 * (bias + m.at(q)) + 1, 1), Glucose::mkLit(2 * (bias + m.at(p)) + 1));		 
	  clause.push(Glucose::mkLit(2 * (bias + m.at(q)) + 1));
	}
	S.addClause(clause);
	clause.clear();
	break;
      }
    case nodecircuit::NODE_DC:
      assert(p->inputs.size() == 2);
      clause.push(Glucose::mkLit(2 * (bias + m.at(p))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      S.addClause(clause);
      clause.clear();

      S.addClause(Glucose::mkLit(2 * (bias + m.at(p)) + 1), Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1, 1));	
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p)) + 1), Glucose::mkLit(2 * (bias + m.at(p->inputs[1])), 1));
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p)) + 1), Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1, 1));	
      break;
    case nodecircuit::NODE_MUX:
      assert(p->inputs.size() == 3);
      // S = 0
      clause.push(Glucose::mkLit(2 * (bias + m.at(p))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1)); 
      S.addClause(clause);
      clause.clear();
	
      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1));       
      S.addClause(clause);
      clause.clear();

      // S = 1
      clause.push(Glucose::mkLit(2 * (bias + m.at(p))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1));
      S.addClause(clause);
      clause.clear();

	
      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1));
      S.addClause(clause);
      clause.clear();

      // S = x
      clause.push(Glucose::mkLit(2 * (bias + m.at(p))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1]))));	
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1]))));	
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1, 1));	
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1, 1));	
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])), 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0]))));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1]))));	
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[1])) + 1));
      clause.push(Glucose::mkLit(2 * (bias + m.at(p->inputs[2])) + 1, 1));       
      S.addClause(clause);
      clause.clear();
      break;
    case nodecircuit::NODE_ISX:
      assert(p->inputs.size() == 1);
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1, 1), Glucose::mkLit(2 * (bias + m.at(p))));	
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p->inputs[0])) + 1), Glucose::mkLit(2 * (bias + m.at(p)), 1));
      S.addClause(Glucose::mkLit(2 * (bias + m.at(p)) + 1, 1));
      break;
    default:
      assert(0);
      break;
    }
  }            
}

void SatSolve2(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result) {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;

  std::map<nodecircuit::Node *, int> gm;
  std::map<nodecircuit::Node *, int> rm;
  
  // inputs
  for (int i = 0; i < gf.inputs.size(); i++) {
    gm[gf.inputs[i]] = rm[rf.inputs[i]] = S.newVar() >> 1;
    S.addClause(Glucose::mkLit(S.newVar(), 1));
  }
  
  // gates in g
  nodecircuit::NodeVector gates;
  gf.GetGates(gates);
  for (int i = 0; i < gates.size(); i++) {
    gm[gates[i]] = S.newVar() >> 1;
    S.newVar();
  }
  Ckt2Cnf2(gates, gm, S, 0);

  // gates in r
  gates.clear();
  rf.GetGates(gates);
  for (int i = 0; i < gates.size(); i++) {
    rm[gates[i]] = S.newVar() >> 1;
    S.newVar();
  }
  Ckt2Cnf2(gates, rm, S, 0);
  
  // miter outputs of the two circuits
  std::vector<int> mos;
  for (int i = 0; i < gf.outputs.size(); i++) {
    int go = 2 * gm[gf.outputs[i]];
    int ro = 2 * rm[rf.outputs[i]];
    int mo = S.newVar();
    mos.push_back(mo);
    // if one output of gf is x, that output is compatible equivalent to the corresponding output of rf
    S.addClause(Glucose::mkLit(mo, 1), Glucose::mkLit(go + 1, 1));

    // if one output of gf is not x, while the corresponding output of rf is x, then gf is not compatible equivalent to rf
    clause.push(Glucose::mkLit(mo));
    clause.push(Glucose::mkLit(go + 1));
    clause.push(Glucose::mkLit(ro + 1, 1));
    S.addClause(clause);
    clause.clear();

    // if neither of the outputs of gf and rf is x, standard xor logic is adopted
    clause.push(Glucose::mkLit(mo));
    clause.push(Glucose::mkLit(go + 1));
    clause.push(Glucose::mkLit(ro + 1));  
    clause.push(Glucose::mkLit(go, 1));
    clause.push(Glucose::mkLit(ro));
    S.addClause(clause);
    clause.clear();
    
    clause.push(Glucose::mkLit(mo));
    clause.push(Glucose::mkLit(go + 1));
    clause.push(Glucose::mkLit(ro + 1));  
    clause.push(Glucose::mkLit(go));
    clause.push(Glucose::mkLit(ro, 1));
    S.addClause(clause);
    clause.clear();

    clause.push(Glucose::mkLit(mo, 1));
    clause.push(Glucose::mkLit(go + 1));
    clause.push(Glucose::mkLit(ro + 1));  
    clause.push(Glucose::mkLit(go));
    clause.push(Glucose::mkLit(ro));
    S.addClause(clause);
    clause.clear();

    clause.push(Glucose::mkLit(mo, 1));
    clause.push(Glucose::mkLit(go + 1));
    clause.push(Glucose::mkLit(ro + 1));  
    clause.push(Glucose::mkLit(go, 1));
    clause.push(Glucose::mkLit(ro, 1));
    S.addClause(clause);
    clause.clear();    
  }
  int o = S.newVar();
  clause.push(Glucose::mkLit(o, 1));
  for (int mo : mos) {
    S.addClause(Glucose::mkLit(mo, 1), Glucose::mkLit(o));
    clause.push(Glucose::mkLit(mo));
  }
  S.addClause(clause);
  clause.clear();
  S.addClause(Glucose::mkLit(o));

  // solve the sat problem
  bool r = S.solve();
  if (r)
    for (int i = 0; i < gf.inputs.size(); i++) { 
      if(S.model[2 * gm[gf.inputs[i]]] == l_True)
	result.push_back(1);
      else
	result.push_back(0);      
    }
}

void SatSolveNode(nodecircuit::Circuit &gf, nodecircuit::Node *gp, nodecircuit::Circuit &rf, nodecircuit::Node *rp, std::vector<bool> &result, bool fexact) {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;

  std::map<nodecircuit::Node *, int> gm;
  std::map<nodecircuit::Node *, int> rm;

  // inputs
  for (int i = 0; i < gf.inputs.size(); i++) {
    gm[gf.inputs[i]] = rm[rf.inputs[i]] = S.newVar() >> 1;
    S.addClause(Glucose::mkLit(S.newVar(), 1));
  }
  
  // gates in g
  nodecircuit::NodeVector gates;
  gf.GetGates(gates, gp);
  for (int i = 0; i < gates.size(); i++) {
    gm[gates[i]] = S.newVar() >> 1;
    S.newVar();
  }
  Ckt2Cnf2(gates, gm, S, 0);

  //gates in r
  gates.clear();
  rf.GetGates(gates, rp);
  for (int i = 0; i < gates.size(); i++) {
    rm[gates[i]] = S.newVar() >> 1;
    S.newVar();
  }
  Ckt2Cnf2(gates, rm, S, 0);

  // miter
  Glucose::Lit gl = Glucose::mkLit(2 * gm[gp]);
  Glucose::Lit glx = Glucose::mkLit(2 * gm[gp] + 1);
  Glucose::Lit rl = Glucose::mkLit(2 * rm[rp]);
  Glucose::Lit rlx = Glucose::mkLit(2 * rm[rp] + 1);
  if(fexact) {
    Glucose::Lit both_x = Glucose::mkLit(S.newVar());
    And2(S, glx, rlx, both_x);
    
    Glucose::Lit both_nox = Glucose::mkLit(S.newVar());
    And2(S, ~glx, ~rlx, both_nox);
    Glucose::Lit eqf = Glucose::mkLit(S.newVar());
    Xor2(S, gl, rl, ~eqf);
    Glucose::Lit eq_nox = Glucose::mkLit(S.newVar());
    And2(S, both_nox, eqf, eq_nox);
    
    Glucose::Lit eq = Glucose::mkLit(S.newVar());
    Or2(S, both_x, eq_nox, eq);
    S.addClause(~eq);
  }
  else {
    Glucose::Lit eqf = Glucose::mkLit(S.newVar());
    Xor2(S, gl, rl, ~eqf);
    Glucose::Lit eq_nox = Glucose::mkLit(S.newVar());
    And2(S, ~rlx, eqf, eq_nox);
    
    Glucose::Lit eq = Glucose::mkLit(S.newVar());
    Or2(S, glx, eq_nox, eq);
    S.addClause(~eq);
  }

  // solve the sat problem
  bool r = S.solve();
  if (r)
    for (int i = 0; i < gf.inputs.size(); i++) { 
      if(S.model[2 * gm[gf.inputs[i]]] == l_True)
	result.push_back(1);
      else
	result.push_back(0);      
    }
}

void SatSolve3(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result) {
  for(int i = 0; i < gf.outputs.size(); i++) {
    SatSolveNode(gf, gf.outputs[i], rf, rf.outputs[i], result, 0);
    if(!result.empty()) {
      return;
    }
  }
}

void SatSolveAll(nodecircuit::Circuit &f, std::vector<bool> &result) {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;
  for(int i = 0; i < f.all_nodes.size(); i++) { 
    S.newVar();
    S.newVar();
  }
  for(auto p: f.inputs) {
    S.addClause(Glucose::mkLit(2 * f.GetNodeIndex(p->name) + 1, 1));
  }
  Ckt2Cnf(f, S, 0);
  for(int i = 0; i < f.outputs.size(); i++) {
    clause.push(Glucose::mkLit(2 * f.GetNodeIndex(f.outputs[i]->name)));
  }
  S.addClause(clause);
  bool r = S.solve();
  if(r) {
    for (int i = 0; i < f.inputs.size(); i++) { 
      if(S.model[2 * i] == l_True) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
  }
}


void SatTest() {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;
  
  // test for 3 variable satisfiability
  S.newVar();
  S.newVar();
  S.newVar();
  // !a
  S.addClause(Glucose::mkLit(0, 1));
  // a + !b
  S.addClause(Glucose::mkLit(0), Glucose::mkLit(1, 1));
  // a + b + c
  clause.push(Glucose::mkLit(0));
  clause.push(Glucose::mkLit(1));
  clause.push(Glucose::mkLit(2));
  S.addClause(clause);
  clause.clear();
  
  // solve ... only (!a, !b, c) satisfies the constraints
  {
    bool r = S.solve();
    assert(r);
    std::vector<bool> results(3);
    for(int i = 0; i < 3; i++) {
      if(S.model[i] == l_True) {
	results[i] = 1;
      }
    }
    std::cout << results[0] << " " << results[1] << " " << results[2] << std::endl;
    assert(!results[0] && !results[1] && results[2]);
  }

  // add another clause a + b + !c
  clause.push(Glucose::mkLit(0));
  clause.push(Glucose::mkLit(1));
  clause.push(Glucose::mkLit(2, 1));
  S.addClause(clause);
  clause.clear();
  // solve ... unsatisfiable
  {
    bool r = S.solve();
    assert(!r);
  }
}
