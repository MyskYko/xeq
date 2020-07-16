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

void LooseDC(nodecircuit::Node *p, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
  Glucose::vec<Glucose::Lit> clause;
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
}

void LooseMUX(nodecircuit::Node *p, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
  Glucose::vec<Glucose::Lit> clause;
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
}

void Ckt2Cnf(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
  Glucose::vec<Glucose::Lit> clause;
  Glucose::vec<Glucose::Lit> clauseback;
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
    case nodecircuit::NODE_NOT:
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	S.addClause(Glucose::mkLit(m.at(p->inputs[0]), 1), Glucose::mkLit(m.at(p), isNot));	
	S.addClause(Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p), !isNot));
	S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1, 1), Glucose::mkLit(m.at(p) + 1));
	S.addClause(Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1, 1));
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
	bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	clause.push(Glucose::mkLit(m.at(p), isOr ^ isNot));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(m.at(q), isOr), Glucose::mkLit(m.at(p), !isOr ^ isNot));
	  clause.push(Glucose::mkLit(m.at(q), !isOr));
	}	
	S.addClause(clause);
	clause.clear();
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
	break;
      }
    case nodecircuit::NODE_XOR:
    case nodecircuit::NODE_XNOR:
      {
	bool isNot = p->type == nodecircuit::NODE_XNOR;
	for (int i = 0; i <= p->inputs.size(); i++) {
	  foreach_comb(p->inputs.size(), i, [&](int *indices) {
	      clause.push(Glucose::mkLit(m.at(p), !(i % 2) ^ isNot));
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
      LooseDC(p, m, S);
      break;
    case nodecircuit::NODE_MUX:
      LooseMUX(p, m, S);
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

void AddMiterOutput(std::vector<int> &outputs, Glucose::SimpSolver &S) {
  Glucose::vec<Glucose::Lit> clause, os;
  for (int i = 0; i < outputs.size(); i++) {
    Glucose::Lit go = Glucose::mkLit(outputs[i]);
    Glucose::Lit gox = Glucose::mkLit(outputs[i] + 1);
    i++;
    Glucose::Lit ro = Glucose::mkLit(outputs[i]);
    Glucose::Lit rox = Glucose::mkLit(outputs[i] + 1);
    Glucose::Lit o = Glucose::mkLit(S.newVar());
    os.push(o);
    
    // if one output of gf is x, that output is compatible equivalent to the corresponding output of rf
    S.addClause(~o, ~gox);

    // if one output of gf is not x, while the corresponding output of rf is x, then gf is not compatible equivalent to rf
    clause.push(o);
    clause.push(gox);
    clause.push(~rox);
    S.addClause(clause);
    clause.clear();

    // if neither of the outputs of gf nor rf is x, standard xor logic is adopted
    clause.push(o);
    clause.push(gox);
    clause.push(rox);
    clause.push(~go);
    clause.push(ro);
    S.addClause(clause);
    clause.clear();
    
    clause.push(o);
    clause.push(gox);
    clause.push(rox);
    clause.push(go);
    clause.push(~ro);
    S.addClause(clause);
    clause.clear();

    clause.push(~o);
    clause.push(gox);
    clause.push(rox);
    clause.push(go);
    clause.push(ro);
    S.addClause(clause);
    clause.clear();

    clause.push(~o);
    clause.push(gox);
    clause.push(rox);
    clause.push(~go);
    clause.push(~ro);
    S.addClause(clause);
    clause.clear();    
  }
  // add or of all os
  S.addClause(os);
}

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
    case nodecircuit::NODE_NOT:
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	Buf(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p)));
	Buf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
        bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), isNot);
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  if(isOr) {
	    Or2(S, in0, in1, out);
	    And2(S, in0x, in1x, t0);
	    And2(S, ~in0, in1x, t1);
	    And2(S, in0x, ~in1, t2);
	  }
	  else {
	    And2(S, in0, in1, out);
	    And2(S, in0x, in1x, t0);
	    And2(S, in0, in1x, t1);
	    And2(S, in0x, in1, t2);
	  }
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
    case nodecircuit::NODE_XNOR:
      {
	bool isNot = p->type == nodecircuit::NODE_XNOR;
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit out;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), isNot);
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
      LooseDC(p, m, S);
      break;
    case nodecircuit::NODE_MUX:
      LooseMUX(p, m, S);
      break;
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

void AddMiterOutput2(std::vector<int> &outputs, Glucose::SimpSolver &S) {
  Glucose::vec<Glucose::Lit> os;
  for (int i = 0; i < outputs.size(); i++) {
    Glucose::Lit go = Glucose::mkLit(outputs[i]);
    Glucose::Lit gox = Glucose::mkLit(outputs[i] + 1);
    i++;
    Glucose::Lit ro = Glucose::mkLit(outputs[i]);
    Glucose::Lit rox = Glucose::mkLit(outputs[i] + 1);
    Glucose::Lit neq_f = Glucose::mkLit(S.newVar());
    Xor2(S, go, ro, neq_f);
    Glucose::Lit neq_ngx = Glucose::mkLit(S.newVar());
    Or2(S, rox, neq_f, neq_ngx);
    Glucose::Lit neq = Glucose::mkLit(S.newVar());
    And2(S, ~gox, neq_ngx, neq);
    os.push(neq);
  }
  S.addClause(os);
}

void Ckt2Cnf3(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
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
      {
	assert(p->inputs.size() == 1);
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	Glucose::Lit out = Glucose::mkLit(m.at(p));
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	And2(S, ~in0, ~in0x, out);
	Buf(S, in0x, outx);
	break;
      }
    case nodecircuit::NODE_AND:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(S.newVar());
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
	And2(S, in0, ~in0x, Glucose::mkLit(m.at(p)));
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
	    out = Glucose::mkLit(S.newVar());
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
	And2(S, ~in0, ~in0x, Glucose::mkLit(m.at(p)));
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
	    out = Glucose::mkLit(S.newVar());
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
	And2(S, in0, ~in0x, Glucose::mkLit(m.at(p)));
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
	    out = Glucose::mkLit(S.newVar());
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
	And2(S, ~in0, ~in0x, Glucose::mkLit(m.at(p)));
	break;
      }
    case nodecircuit::NODE_XOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	OrN(S, clause, outx);
	And2(S, in0, ~outx, Glucose::mkLit(m.at(p)));
	break;
      }
    case nodecircuit::NODE_XNOR:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]));
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Xor2(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	OrN(S, clause, outx);
	And2(S, ~in0, ~outx, Glucose::mkLit(m.at(p)));
	break;
      }
    case nodecircuit::NODE_DC:
      LooseDC(p, m, S);
      break;
    case nodecircuit::NODE_MUX:
      LooseMUX(p, m, S);
      break;
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

void SatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding, int out_encoding) {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;
  std::map<nodecircuit::Node *, int> m;
  // inputs
  for (int i = 0; i < gf.inputs.size(); i++) {
    m[gf.inputs[i]] = m[rf.inputs[i]] = S.newVar();
    S.addClause(Glucose::mkLit(S.newVar(), 1));
  }
  // gates
  nodecircuit::NodeVector gates;
  gf.GetGates(gates);
  rf.GetGates(gates);
  for (int i = 0; i < gates.size(); i++) {
    m[gates[i]] = S.newVar();
    S.newVar();
  }
  switch (gate_encoding) {
  case 0:
    Ckt2Cnf(gates, m, S);
    break;
  case 1:
    Ckt2Cnf2(gates, m, S);
    break;
  case 2:
    Ckt2Cnf3(gates, m, S);
    break;
  default:
    assert(0);
  }
  // outputs
  std::vector<int> outputs;
  for (int i = 0; i < gf.outputs.size(); i++) {
    outputs.push_back(m[gf.outputs[i]]);
    outputs.push_back(m[rf.outputs[i]]);
  }
  switch (out_encoding) {
  case 0:
    AddMiterOutput(outputs, S);
    break;
  case 1:
    AddMiterOutput2(outputs, S);
    break;
  default:
    assert(0);
  }
  // solve
  bool r = S.solve();
  if (r) {
    for (auto p: gf.inputs) {
      if (S.model[m[p]] == l_True) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
  }
}

int SatSolve4(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding, bool fEach) {
  // create miter circuit
  nodecircuit::Circuit f;
  nodecircuit::Miter(gf, rf, f);
  // prepare sat solver and node2index map
  Glucose::SimpSolver S;
  //S.setIncrementalMode();
  //S.setConfBudget(1000);
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
  for(int i = 0; i < gates.size(); i++) {
    m[gates[i]] = S.newVar();
    S.newVar();
  }
  switch (gate_encoding) {
  case 0:
    Ckt2Cnf(gates, m, S);
    break;
  case 1:
    Ckt2Cnf2(gates, m, S);
    break;
  case 2:
    Ckt2Cnf3(gates, m, S);
    break;
  default:
    assert(0);
  }
  // solve
  bool r = 0;
  int undecided = 0;
  if(!fEach) {
    // outputs
    clause.clear();
    for(int i = 0; i < f.outputs.size(); i++) {
      auto p = f.outputs[i++];
      auto q = f.outputs[i];
      Glucose::Lit o = Glucose::mkLit(S.newVar());
      Xor2(S, Glucose::mkLit(m[p]), Glucose::mkLit(m[q]), o);
      clause.push(o);
    }
    S.addClause(clause);
    r = S.solve();
  }
  else {
    Glucose::lbool res;
    for(int i = 0; i < f.outputs.size(); i++) {
      Glucose::Lit go = Glucose::mkLit(m[f.outputs[i++]]);
      Glucose::Lit ro = Glucose::mkLit(m[f.outputs[i]]);
      clause.clear();
      clause.push(~go);
      clause.push(ro);
      res = S.solveLimited(clause, 0);
      if(res == l_True) {
	r = 1;
	break;
      }
      else if(res != l_False) {
	std::cout << "undecided" << std::endl;
	undecided++;
      }
      clause.clear();
      clause.push(go);
      clause.push(~ro);
      res = S.solveLimited(clause, 0);
      if(res == l_True) {
	r = 1;
	break;
      }
      else if(res != l_False) {
	std::cout << "undecided" << std::endl;
	undecided++;
      }
    }
  }
  if(r) {
    for(auto p : f.inputs) {
      if(S.model[m[p]] == l_True) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
    return 0;
  }
  return undecided;
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
