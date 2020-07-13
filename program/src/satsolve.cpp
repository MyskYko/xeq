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

void XConstraints(std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S, nodecircuit::Node *p) {
  Glucose::vec<Glucose::Lit> clause;
  Glucose::vec<Glucose::Lit> clauseback;
  bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
  assert(isOr || p->type == nodecircuit::NODE_AND || p->type == nodecircuit::NODE_NAND);
  
  clause.push(Glucose::mkLit(m.at(p) + 1, 1));
  for (auto q: p->inputs) {
    clauseback.push(Glucose::mkLit(m.at(q), isOr));
    clauseback.push(Glucose::mkLit(m.at(q) + 1));
    clauseback.push(Glucose::mkLit(m.at(p) + 1, 1));
    S.addClause(clauseback);
    clauseback.clear();
    clause.push(Glucose::mkLit(m.at(q) + 1));
  }	
  S.addClause(clause);
  clause.clear();
      
  for (auto q: p->inputs) {
    for (int i = 0; i <= p->inputs.size(); i++) {
      foreach_comb(p->inputs.size(), i, [&](int *indices) {
	  clause.push(Glucose::mkLit(m.at(p) + 1));
	  clause.push(Glucose::mkLit(m.at(q) + 1, 1));
	  int j = 0;
	  for (int k = 0; k < i; k++) {
	    while(j != indices[k]) {
	      assert(j < indices[k]);
	      clause.push(Glucose::mkLit(m.at(p->inputs[j]), !isOr));
	      j++;
	    }
	    assert(j == indices[k]);
	    clause.push(Glucose::mkLit(m.at(p->inputs[j]) + 1, 1));
	    j++;
	  }
	  while(j < p->inputs.size()) {
	    clause.push(Glucose::mkLit(m.at(p->inputs[j]), !isOr));
	    j++;
	  }
	  S.addClause(clause);
	  clause.clear();
	});
    }
  }
}

void Ckt2Cnf(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
  Glucose::vec<Glucose::Lit> clause;
  for (auto p: gates) {
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if (p->name == "1'b0") {
	S.addClause(Glucose::mkLit(m.at(p), 1));
	S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      }
      else if (p->name == "1'b1") {
	S.addClause(Glucose::mkLit(m.at(p)));
	S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      }
      else if (p->name == "1'bx") {	  
	S.addClause(Glucose::mkLit(m.at(p) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
      assert(p->inputs.size() == 1);	
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]), 1), Glucose::mkLit(m.at(p)));	
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1, 1), Glucose::mkLit(m.at(p) + 1));
      S.addClause(Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p), 1));
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1, 1));
      break;
    case nodecircuit::NODE_NOT:
      assert(p->inputs.size() == 1);
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]), 1), Glucose::mkLit(m.at(p), 1));	
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1, 1), Glucose::mkLit(m.at(p) + 1));
      S.addClause(Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p)));
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1, 1));
      break;
    case nodecircuit::NODE_AND:
      clause.push(Glucose::mkLit(m.at(p)));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(m.at(q)), Glucose::mkLit(m.at(p), 1));		 
	clause.push(Glucose::mkLit(m.at(q), 1));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(m, S, p);
      break;
    case nodecircuit::NODE_NAND:
      clause.push(Glucose::mkLit(m.at(p), 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(m.at(q)), Glucose::mkLit(m.at(p)));		 
	clause.push(Glucose::mkLit(m.at(q), 1));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(m, S, p);
      break;
    case nodecircuit::NODE_OR:
      clause.push(Glucose::mkLit(m.at(p), 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(m.at(q), 1), Glucose::mkLit(m.at(p)));		 
	clause.push(Glucose::mkLit(m.at(q)));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(m, S, p);
      break;
    case nodecircuit::NODE_NOR:
      clause.push(Glucose::mkLit(m.at(p)));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(m.at(q), 1), Glucose::mkLit(m.at(p), 1));		 
	clause.push(Glucose::mkLit(m.at(q)));
      }	
      S.addClause(clause);
      clause.clear();
      XConstraints(m, S, p);
      break;	
    case nodecircuit::NODE_XOR: {
      for (int i = 0; i <= p->inputs.size(); i++) {
	foreach_comb(p->inputs.size(), i, [&](int *indices) {
	    clause.push(Glucose::mkLit(m.at(p), !(i % 2)));
	    int j = 0;
	    for (int k = 0; k < i; k++) {
	      while(j != indices[k]) {
		assert(j < indices[k]);
		clause.push(Glucose::mkLit(m.at(p->inputs[j])));
		j++;
	      }
	      assert(j == indices[k]);
	      clause.push(Glucose::mkLit(m.at(p->inputs[j]), 1));
	      j++;
	    }
	    while(j < p->inputs.size()) {
	      clause.push(Glucose::mkLit(m.at(p->inputs[j])));
	      j++;
	    }
	    S.addClause(clause);
	    clause.clear();
	  });
      }
      clause.push(Glucose::mkLit(m.at(p) + 1, 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(m.at(q) + 1, 1), Glucose::mkLit(m.at(p) + 1));
	clause.push(Glucose::mkLit(m.at(q) + 1));
      }	
      S.addClause(clause);
      clause.clear();
      break;
    }
    case nodecircuit::NODE_XNOR: {
      for (int i = 0; i <= p->inputs.size(); i++) {
	foreach_comb(p->inputs.size(), i, [&](int *indices) {
	    clause.push(Glucose::mkLit(m.at(p), i % 2));
	    int j = 0;
	    for (int k = 0; k < i; k++) {
	      while(j != indices[k]) {
		assert(j < indices[k]);
		clause.push(Glucose::mkLit(m.at(p->inputs[j])));
		j++;
	      }
	      assert(j == indices[k]);
	      clause.push(Glucose::mkLit(m.at(p->inputs[j]), 1));
	      j++;
	    }
	    while(j < p->inputs.size()) {
	      clause.push(Glucose::mkLit(m.at(p->inputs[j])));
	      j++;
	    }
	    S.addClause(clause);
	    clause.clear();
	  });
      }
      clause.push(Glucose::mkLit(m.at(p) + 1, 1));
      for (auto q: p->inputs) {
	S.addClause(Glucose::mkLit(m.at(q) + 1, 1), Glucose::mkLit(m.at(p) + 1));
	clause.push(Glucose::mkLit(m.at(q) + 1));
      }	
      S.addClause(clause);
      clause.clear();
      break;
    }
    case nodecircuit::NODE_DC:
      assert(p->inputs.size() == 2);
      clause.push(Glucose::mkLit(m.at(p)));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0])));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1, 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      S.addClause(clause);
      clause.clear();

      S.addClause(Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p->inputs[0]) + 1, 1));
      S.addClause(Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p->inputs[1]), 1));
      S.addClause(Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p->inputs[1]) + 1, 1));
      break;
    case nodecircuit::NODE_MUX:
      assert(p->inputs.size() == 3);
      // S = 0
      clause.push(Glucose::mkLit(m.at(p)));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2])));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0])));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2])));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1)); 
      S.addClause(clause);
      clause.clear();
	
      clause.push(Glucose::mkLit(m.at(p) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1, 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2])));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1, 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2])));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1));       
      S.addClause(clause);
      clause.clear();

      // S = 1
      clause.push(Glucose::mkLit(m.at(p)));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1));
      S.addClause(clause);
      clause.clear();

	
      clause.push(Glucose::mkLit(m.at(p) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1, 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1));
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1, 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1));
      S.addClause(clause);
      clause.clear();

      // S = x
      clause.push(Glucose::mkLit(m.at(p)));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0])));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));	
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));	
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1, 1));	
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1, 1));	
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1, 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]), 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();

      clause.push(Glucose::mkLit(m.at(p) + 1, 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0])));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));	
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[2]) + 1, 1));       
      S.addClause(clause);
      clause.clear();
      break;
    case nodecircuit::NODE_ISX:
      assert(p->inputs.size() == 1);
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1, 1), Glucose::mkLit(m.at(p)));	
      S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p), 1));
      S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      break;
    default:
      assert(0);
      break;
    }
  }            
}
/*
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
*/
void Buf(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b) {
  S.addClause(~a, b);
  S.addClause(a, ~b);
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
void Ite2(Glucose::SimpSolver &S, Glucose::Lit c, Glucose::Lit t, Glucose::Lit e, Glucose::Lit r) {
  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
  And2(S, c, t, t0);
  And2(S, ~c, e, t1);
  Or2(S, t0, t1, r);
}
void OrN(Glucose::SimpSolver &S, Glucose::vec<Glucose::Lit> &v, Glucose::Lit r) {
  for(int i = 0; i < v.size(); i++) {
    S.addClause(~v[i], r);
  }
  v.push(~r);
  S.addClause(v);
  v.pop();
}

void Ckt2Cnf2(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
  Glucose::vec<Glucose::Lit> clause;
  for (auto p: gates) {
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if (p->name == "1'b0") {
	S.addClause(Glucose::mkLit(m.at(p), 1));
	S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      }
      else if (p->name == "1'b1") {
	S.addClause(Glucose::mkLit(m.at(p)));
	S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      }
      else if (p->name == "1'bx") {	  
	S.addClause(Glucose::mkLit(m.at(p) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
      assert(p->inputs.size() == 1);
      Buf(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p)));
      Buf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
      break;
    case nodecircuit::NODE_NOT:
      assert(p->inputs.size() == 1);
      Buf(S, Glucose::mkLit(m.at(p->inputs[0]), 1), Glucose::mkLit(m.at(p)));
      Buf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
      break;
    case nodecircuit::NODE_AND:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p));
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  And2(S, in0, in1, out);
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
	break;
      }
    case nodecircuit::NODE_NAND:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), 1);
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  And2(S, in0, in1, out);
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
	break;
      }      
    case nodecircuit::NODE_OR:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p));
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Or2(S, in0, in1, out);
	  And2(S, in0x, in1x, t0);
	  And2(S, ~in0, in1x, t1);
	  And2(S, in0x, ~in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  OrN(S, clause, outx);
	  in0 = out;
	  in0x = outx;
	}
	break;
      }
    case nodecircuit::NODE_NOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), 1);
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Or2(S, in0, in1, out);
	  And2(S, in0x, in1x, t0);
	  And2(S, ~in0, in1x, t1);
	  And2(S, in0x, ~in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  OrN(S, clause, outx);
	  in0 = out;
	  in0x = outx;
	}
	break;
      }
    case nodecircuit::NODE_XOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit out;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p));
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	  }
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	OrN(S, clause, Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_XNOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit out;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	  }
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	OrN(S, clause, Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_DC:
      {
	assert(p->inputs.size() == 2);
	Buf(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p)));
	clause.clear();
	clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
	clause.push(Glucose::mkLit(m.at(p->inputs[1])));
	clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
	OrN(S, clause, Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_MUX:
      {
	assert(p->inputs.size() == 3);
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[1]));
	Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[1]) + 1);
	Glucose::Lit in2 = Glucose::mkLit(m.at(p->inputs[2]));
	Glucose::Lit in2x = Glucose::mkLit(m.at(p->inputs[2]) + 1);
	Glucose::Lit out = Glucose::mkLit(m.at(p));
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	Ite2(S, in2, in1, in0, out);
	Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	Glucose::Lit t4 = Glucose::mkLit(S.newVar());
	Ite2(S, in2, in1x, in0x, t0);
	Or2(S, in0x, in1x, t1);
	Xor2(S, in0, in1, t2);
	Or2(S, t1, t2, t3);
	And2(S, in2x, t3, t4);
	Or2(S, t0, t4, outx);
	break;
      }
    case nodecircuit::NODE_ISX:
      assert(p->inputs.size() == 1);
      Buf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p)));
      S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
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
    gm[gf.inputs[i]] = rm[rf.inputs[i]] = S.newVar();
    S.addClause(Glucose::mkLit(S.newVar(), 1));
  }
  
  // gates in g
  nodecircuit::NodeVector gates;
  gf.GetGates(gates);
  for (int i = 0; i < gates.size(); i++) {
    gm[gates[i]] = S.newVar();
    S.newVar();
  }
  Ckt2Cnf2(gates, gm, S);

  // gates in r
  gates.clear();
  rf.GetGates(gates);
  for (int i = 0; i < gates.size(); i++) {
    rm[gates[i]] = S.newVar();
    S.newVar();
  }
  Ckt2Cnf2(gates, rm, S);
  
  // miter outputs of the two circuits
  clause.clear();
  for (int i = 0; i < gf.outputs.size(); i++) {
    Glucose::Lit gl = Glucose::mkLit(gm[gf.outputs[i]]);
    Glucose::Lit glx = Glucose::mkLit(gm[gf.outputs[i]] + 1);
    Glucose::Lit rl = Glucose::mkLit(rm[rf.outputs[i]]);
    Glucose::Lit rlx = Glucose::mkLit(rm[rf.outputs[i]] + 1);
    Glucose::Lit neq_f = Glucose::mkLit(S.newVar());
    Xor2(S, gl, rl, neq_f);
    Glucose::Lit neq_ngx = Glucose::mkLit(S.newVar());
    Or2(S, rlx, neq_f, neq_ngx);
    Glucose::Lit neq = Glucose::mkLit(S.newVar());
    And2(S, ~glx, neq_ngx, neq);
    clause.push(neq);
  }
  Glucose::Lit o = Glucose::mkLit(S.newVar());
  OrN(S, clause, o);
  S.addClause(o);

  // solve the sat problem
  bool r = S.solve();
  if (r) {
    for (int i = 0; i < gf.inputs.size(); i++) { 
      if(S.model[gm[gf.inputs[i]]] == l_True) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
  }
}

void SatSolveNode(nodecircuit::Circuit &gf, nodecircuit::Node *gp, nodecircuit::Circuit &rf, nodecircuit::Node *rp, std::vector<bool> &result, bool fexact) {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;

  std::map<nodecircuit::Node *, int> gm;
  std::map<nodecircuit::Node *, int> rm;

  // inputs
  for (int i = 0; i < gf.inputs.size(); i++) {
    gm[gf.inputs[i]] = rm[rf.inputs[i]] = S.newVar();
    S.addClause(Glucose::mkLit(S.newVar(), 1));
  }
  
  // gates in g
  nodecircuit::NodeVector gates;
  gf.GetGates(gates, gp);
  for (int i = 0; i < gates.size(); i++) {
    gm[gates[i]] = S.newVar();
    S.newVar();
  }
  Ckt2Cnf2(gates, gm, S);

  //gates in r
  gates.clear();
  rf.GetGates(gates, rp);
  for (int i = 0; i < gates.size(); i++) {
    rm[gates[i]] = S.newVar();
    S.newVar();
  }
  Ckt2Cnf2(gates, rm, S);

  // miter
  Glucose::Lit gl = Glucose::mkLit(gm[gp]);
  Glucose::Lit glx = Glucose::mkLit(gm[gp] + 1);
  Glucose::Lit rl = Glucose::mkLit(rm[rp]);
  Glucose::Lit rlx = Glucose::mkLit(rm[rp] + 1);
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
      if(S.model[gm[gf.inputs[i]]] == l_True)
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
  std::map<nodecircuit::Node *, int> m;
  // inputs
  for (int i = 0; i < f.inputs.size(); i++) {
    m[f.inputs[i]] = S.newVar();
    S.addClause(Glucose::mkLit(S.newVar(), 1));
  }
  // gates
  nodecircuit::NodeVector gates;
  f.GetGates(gates);
  for (int i = 0; i < gates.size(); i++) {
    m[gates[i]] = S.newVar();
    S.newVar();
  }
  Ckt2Cnf2(gates, m, S);
  // outputs
  for(auto p : f.outputs) {
    clause.push(Glucose::mkLit(m[p]));
  }
  S.addClause(clause);
  // solve
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
