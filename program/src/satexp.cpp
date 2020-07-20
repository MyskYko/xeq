#include <iostream>
#include <cassert>

#include <simp/SimpSolver.h>

#include "satexp.h"

void AddBuf(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b) {
  S.addClause(~a, b);
  S.addClause(a, ~b);
}
void Add2And(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c) {  
  S.addClause(a, ~c);
  S.addClause(b, ~c);
  S.addClause(~a, ~b, c);
}
void Add2Or(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c) {
  Add2And(S, ~a, ~b, ~c);
}
void Add2Xor(Glucose::SimpSolver &S, Glucose::Lit a, Glucose::Lit b, Glucose::Lit c) {
  S.addClause(a, b, ~c);
  S.addClause(~a, ~b, ~c);
  S.addClause(~a, b, c);
  S.addClause(a, ~b, c);
}
void AddIte(Glucose::SimpSolver &S, Glucose::Lit c, Glucose::Lit t, Glucose::Lit e, Glucose::Lit r) {
  // ITE
  S.addClause(~c, ~t, r);
  S.addClause(~c, t, ~r);
  S.addClause(c, ~e, r);
  S.addClause(c, e, ~r);
  // additional clauses (t & e -> r) and (!t & !e -> !r)
  S.addClause(~t, ~e, r);
  S.addClause(t, e, ~r);
}
void AddNaryOr(Glucose::SimpSolver &S, Glucose::vec<Glucose::Lit> &v, Glucose::Lit r) {
  for(int i = 0; i < v.size(); i++) {
    S.addClause(~v[i], r);
  }
  v.push(~r);
  S.addClause(v);
  v.pop();
}
void AddLoose(Glucose::SimpSolver &S, Glucose::Lit in, Glucose::Lit outx, Glucose::Lit out) {
  S.addClause(~in, outx, out);
  S.addClause(in, outx, ~out);
}

void Ckt2CnfDefault(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
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
	S.addClause(Glucose::mkLit(m.at(p), 1));
	S.addClause(Glucose::mkLit(m.at(p) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
    case nodecircuit::NODE_NOT:
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p)));
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
        bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]), isOr);
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]), isOr);
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), isNot ^ isOr);
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Add2And(S, in0, in1, out);
	  Add2And(S, in0x, in1x, t0);
	  Add2And(S, in0, in1x, t1);
	  Add2And(S, in0x, in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  AddNaryOr(S, clause, outx);
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
	  Add2Xor(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	AddNaryOr(S, clause, Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_DC:
      AddBuf(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p)));
      clause.clear();
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      AddNaryOr(S, clause, Glucose::mkLit(m.at(p) + 1));
      break;
    case nodecircuit::NODE_MUX:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[1]));
	Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[1]) + 1);
	Glucose::Lit in2 = Glucose::mkLit(m.at(p->inputs[2]));
	Glucose::Lit in2x = Glucose::mkLit(m.at(p->inputs[2]) + 1);
	Glucose::Lit out = Glucose::mkLit(m.at(p));
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	AddIte(S, in2, in1, in0, out);
	Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	Glucose::Lit t4 = Glucose::mkLit(S.newVar());
	AddIte(S, in2, in1x, in0x, t0);
	Add2Or(S, in0x, in1x, t1);
	Add2Xor(S, in0, in1, t2);
	Add2Or(S, t1, t2, t3);
	Add2And(S, in2x, t3, t4);
	Add2Or(S, t0, t4, outx);
	break;
      }
    case nodecircuit::NODE_ISX:
      AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p)));
      S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      break;
    default:
      throw "unknown gate type";
      break;
    }
  }
}

void Ckt2CnfDcMux(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S, bool Floating) {
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
	if(!Floating) {
	  S.addClause(Glucose::mkLit(m.at(p), 1));
	}
	S.addClause(Glucose::mkLit(m.at(p) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
    case nodecircuit::NODE_NOT:
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p)));
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
        bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]), isOr);
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]), isOr);
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), isNot ^ isOr);
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Add2And(S, in0, in1, out);
	  Add2And(S, in0x, in1x, t0);
	  Add2And(S, in0, in1x, t1);
	  Add2And(S, in0x, in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  AddNaryOr(S, clause, outx);
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
	  Add2Xor(S, in0, in1, out);
	  in0 = out;
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	AddNaryOr(S, clause, Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_DC:
      if(Floating) {
	AddLoose(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p)));
      }
      else {
	Add2And(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p) + 1, 1), Glucose::mkLit(m.at(p)));
      }
      clause.clear();
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      AddNaryOr(S, clause, Glucose::mkLit(m.at(p) + 1));
      break;
    case nodecircuit::NODE_MUX:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[1]));
	Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[1]) + 1);
	Glucose::Lit in2 = Glucose::mkLit(m.at(p->inputs[2]));
	Glucose::Lit in2x = Glucose::mkLit(m.at(p->inputs[2]) + 1);
	Glucose::Lit tmp = Glucose::mkLit(S.newVar());
	Glucose::Lit out = Glucose::mkLit(m.at(p));
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	AddIte(S, in2, in1, in0, tmp);
	if(Floating) {
	  AddLoose(S, tmp, outx, out);
	}
	else {
	  Add2And(S, tmp, ~outx, out);
	}
	Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	Glucose::Lit t4 = Glucose::mkLit(S.newVar());
	AddIte(S, in2, in1x, in0x, t0);
	Add2Or(S, in0x, in1x, t1);
	Add2Xor(S, in0, in1, t2);
	Add2Or(S, t1, t2, t3);
	Add2And(S, in2x, t3, t4);
	Add2Or(S, t0, t4, outx);
	break;
      }
    case nodecircuit::NODE_ISX:
      AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p)));
      S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      break;
    default:
      throw "unknown gate type";
      break;
    }
  }
}

void Ckt2CnfNaryGate(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S, bool Floating) {
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
	if(!Floating) {
	  S.addClause(Glucose::mkLit(m.at(p), 1));
	}
	S.addClause(Glucose::mkLit(m.at(p) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
    case nodecircuit::NODE_NOT:
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	if(Floating) {
	  AddLoose(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p)));
	}
	else {
	  Add2And(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p) + 1, 1), Glucose::mkLit(m.at(p)));
	}
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
        bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]), isOr);
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]), isOr);
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Glucose::Lit outx;
	  if(i == p->inputs.size() - 1) {
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Add2And(S, in0, in1, out);
	  Add2And(S, in0x, in1x, t0);
	  Add2And(S, in0, in1x, t1);
	  Add2And(S, in0x, in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  AddNaryOr(S, clause, outx);
	  in0 = out;
	  in0x = outx;
	}
	if(Floating) {
	  AddLoose(S, in0, in0x, Glucose::mkLit(m.at(p), isNot ^ isOr));
	}
	else {
	  Add2And(S, in0, ~in0x, Glucose::mkLit(m.at(p), isNot ^ isOr));
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
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Add2Xor(S, in0, in1, out);
	  in0 = out;
	}
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	if(Floating) {
	  AddLoose(S, in0, outx, Glucose::mkLit(m.at(p), isNot));
	}
	else {
	  Add2And(S, in0, ~outx, Glucose::mkLit(m.at(p), isNot));
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	AddNaryOr(S, clause, outx);
	break;
      }
    case nodecircuit::NODE_DC:
      if(Floating) {
	AddLoose(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p)));
      }
      else {
	Add2And(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p) + 1, 1), Glucose::mkLit(m.at(p)));
      }
      clause.clear();
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      AddNaryOr(S, clause, Glucose::mkLit(m.at(p) + 1));
      break;
    case nodecircuit::NODE_MUX:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[1]));
	Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[1]) + 1);
	Glucose::Lit in2 = Glucose::mkLit(m.at(p->inputs[2]));
	Glucose::Lit in2x = Glucose::mkLit(m.at(p->inputs[2]) + 1);
	Glucose::Lit tmp = Glucose::mkLit(S.newVar());
	Glucose::Lit out = Glucose::mkLit(m.at(p));
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	AddIte(S, in2, in1, in0, tmp);
	if(Floating) {
	  AddLoose(S, tmp, outx, out);
	}
	else {
	  Add2And(S, tmp, ~outx, out);
	}
	Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	Glucose::Lit t4 = Glucose::mkLit(S.newVar());
	AddIte(S, in2, in1x, in0x, t0);
	Add2Or(S, in0x, in1x, t1);
	Add2Xor(S, in0, in1, t2);
	Add2Or(S, t1, t2, t3);
	Add2And(S, in2x, t3, t4);
	Add2Or(S, t0, t4, outx);
	break;
      }
    case nodecircuit::NODE_ISX:
      AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p)));
      S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      break;
    default:
      throw "unknown gate type";
      break;
    }
  }
}

void Ckt2Cnf2Gate(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S, bool Floating) {
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
	if(!Floating) {
	  S.addClause(Glucose::mkLit(m.at(p), 1));
	}
	S.addClause(Glucose::mkLit(m.at(p) + 1));
      }
      break;
    case nodecircuit::NODE_BUF:
    case nodecircuit::NODE_NOT:
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	if(Floating) {
	  AddLoose(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p)));
	}
	else {
	  Add2And(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p) + 1, 1), Glucose::mkLit(m.at(p)));
	}
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
        bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]), isOr);
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]), isOr);
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), isNot ^ isOr);
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  Glucose::Lit tmp = Glucose::mkLit(S.newVar());
	  Add2And(S, in0, in1, tmp);
	  if(Floating) {
	    AddLoose(S, tmp, outx, out);
	  }
	  else {
	    Add2And(S, tmp, ~outx, out);
	  }
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Add2And(S, in0x, in1x, t0);
	  Add2And(S, in0, in1x, t1);
	  Add2And(S, in0x, in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  AddNaryOr(S, clause, outx);
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
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Add2Xor(S, in0, in1, out);
	  in0 = out;
	}
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	if(Floating) {
	  AddLoose(S, in0, outx, Glucose::mkLit(m.at(p), isNot));
	}
	else {
	  Add2And(S, in0, ~outx, Glucose::mkLit(m.at(p), isNot));
	}
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	AddNaryOr(S, clause, outx);
	break;
      }
    case nodecircuit::NODE_DC:
      if(Floating) {
	AddLoose(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p) + 1), Glucose::mkLit(m.at(p)));
      }
      else {
	Add2And(S, Glucose::mkLit(m.at(p->inputs[0])), Glucose::mkLit(m.at(p) + 1, 1), Glucose::mkLit(m.at(p)));
      }
      clause.clear();
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      AddNaryOr(S, clause, Glucose::mkLit(m.at(p) + 1));
      break;
    case nodecircuit::NODE_MUX:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[1]));
	Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[1]) + 1);
	Glucose::Lit in2 = Glucose::mkLit(m.at(p->inputs[2]));
	Glucose::Lit in2x = Glucose::mkLit(m.at(p->inputs[2]) + 1);
	Glucose::Lit tmp = Glucose::mkLit(S.newVar());
	Glucose::Lit out = Glucose::mkLit(m.at(p));
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	AddIte(S, in2, in1, in0, tmp);
	if(Floating) {
	  AddLoose(S, tmp, outx, out);
	}
	else {
	  Add2And(S, tmp, ~outx, out);
	}
	Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	Glucose::Lit t3 = Glucose::mkLit(S.newVar());
	Glucose::Lit t4 = Glucose::mkLit(S.newVar());
	AddIte(S, in2, in1x, in0x, t0);
	Add2Or(S, in0x, in1x, t1);
	Add2Xor(S, in0, in1, t2);
	Add2Or(S, t1, t2, t3);
	Add2And(S, in2x, t3, t4);
	Add2Or(S, t0, t4, outx);
	break;
      }
    case nodecircuit::NODE_ISX:
      AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p)));
      S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      break;
    default:
      throw "unknown gate type";
      break;
    }
  }
}

void Ckt2Cnf2GateNew(nodecircuit::NodeVector const &gates, std::map<nodecircuit::Node *, int> const &m, Glucose::SimpSolver &S) {
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
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]), isNot), Glucose::mkLit(m.at(p)));
	AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p) + 1));
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
        bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]), isOr);
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	for(int i = 1; i < p->inputs.size(); i++) {
	  Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[i]), isOr);
	  Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[i]) + 1);
	  Glucose::Lit out, outx;
	  if(i == p->inputs.size() - 1) {
	    out = Glucose::mkLit(m.at(p), isNot ^ isOr);
	    outx = Glucose::mkLit(m.at(p) + 1);
	  }
	  else {
	    out = Glucose::mkLit(S.newVar());
	    outx = Glucose::mkLit(S.newVar());
	  }
	  clause.clear();
	  clause.push(~in0);
	  clause.push(~in1);
	  clause.push(outx);
	  clause.push(out);
	  S.addClause(clause);
	  S.addClause(in0, outx, ~out);
	  S.addClause(in1, outx, ~out);
	  Glucose::Lit t0 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t1 = Glucose::mkLit(S.newVar());
	  Glucose::Lit t2 = Glucose::mkLit(S.newVar());
	  Add2And(S, in0x, in1x, t0);
	  Add2And(S, in0, in1x, t1);
	  Add2And(S, in0x, in1, t2);
	  clause.clear();
	  clause.push(t0);
	  clause.push(t1);
	  clause.push(t2);
	  AddNaryOr(S, clause, outx);
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
	  Glucose::Lit out = Glucose::mkLit(S.newVar());
	  Add2Xor(S, in0, in1, out);
	  in0 = out;
	}
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	AddLoose(S, in0, outx, Glucose::mkLit(m.at(p), isNot));
	clause.clear();
	for (auto q: p->inputs) {
	  clause.push(Glucose::mkLit(m.at(q) + 1));
	}
	AddNaryOr(S, clause, outx);
	break;
      }
    case nodecircuit::NODE_DC:
      clause.clear();
      clause.push(Glucose::mkLit(m.at(p->inputs[0]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[1])));
      clause.push(Glucose::mkLit(m.at(p->inputs[1]) + 1));
      clause.push(Glucose::mkLit(m.at(p->inputs[0]), 1));
      clause.push(Glucose::mkLit(m.at(p)));
      S.addClause(clause);
      clause.pop();
      clause.pop();
      clause.push(Glucose::mkLit(m.at(p->inputs[0])));
      clause.push(Glucose::mkLit(m.at(p), 1));
      S.addClause(clause);
      clause.pop();
      clause.pop();
      AddNaryOr(S, clause, Glucose::mkLit(m.at(p) + 1));
      break;
    case nodecircuit::NODE_MUX:
      {
	Glucose::Lit in0 = Glucose::mkLit(m.at(p->inputs[0]));
	Glucose::Lit in0x = Glucose::mkLit(m.at(p->inputs[0]) + 1);
	Glucose::Lit in1 = Glucose::mkLit(m.at(p->inputs[1]));
	Glucose::Lit in1x = Glucose::mkLit(m.at(p->inputs[1]) + 1);
	Glucose::Lit in2 = Glucose::mkLit(m.at(p->inputs[2]));
	Glucose::Lit in2x = Glucose::mkLit(m.at(p->inputs[2]) + 1);
	Glucose::Lit out = Glucose::mkLit(m.at(p));
	Glucose::Lit outx = Glucose::mkLit(m.at(p) + 1);
	// S = 0
	clause.clear();
	clause.push(in2);
	clause.push(in2x);
	clause.push(in0x);
	clause.push(~in0);
	clause.push(out);
	S.addClause(clause);
	clause.pop();	clause.pop();
	clause.push(in0);
	clause.push(~out);
	S.addClause(clause);
	clause.pop();	clause.pop();	clause.pop();
	clause.push(~in0x);
	clause.push(outx);
	S.addClause(clause);
	clause.pop();	clause.pop();
	clause.push(in0x);
	clause.push(~outx);
	S.addClause(clause);
	// S = 1
	clause.clear();
	clause.push(~in2);
	clause.push(in2x);
	clause.push(in1x);
	clause.push(~in1);
	clause.push(out);
	S.addClause(clause);
	clause.pop();	clause.pop();
	clause.push(in1);
	clause.push(~out);
	S.addClause(clause);
	clause.pop();	clause.pop();	clause.pop();
	clause.push(~in1x);
	clause.push(outx);
	S.addClause(clause);
	clause.pop();	clause.pop();
	clause.push(in1x);
	clause.push(~outx);
	S.addClause(clause);
	// S = x
	clause.clear();
	clause.push(~in2x);
	clause.push(in0x);
	clause.push(in1x);
	clause.push(~in0);
	clause.push(~in1);
	clause.push(out);
	S.addClause(clause);
	clause.pop();
	clause.push(~outx);
	S.addClause(clause);
	clause.pop();	clause.pop();	clause.pop();
	clause.push(in0);
	clause.push(in1);
	clause.push(~out);
	S.addClause(clause);
	clause.pop();
	clause.push(~outx);
	S.addClause(clause);
	clause.clear();
	clause.push(~in2x);
	clause.push(outx);
	clause.push(in0);
	clause.push(~in1);
	S.addClause(clause);
	clause.pop();	clause.pop();
	clause.push(~in0);
	clause.push(in1);
	S.addClause(clause);
	clause.pop();	clause.pop();
	clause.push(~in0x);
	S.addClause(clause);
	clause.pop();
	clause.push(~in1x);
	S.addClause(clause);
	break;
      }
    case nodecircuit::NODE_ISX:
      AddBuf(S, Glucose::mkLit(m.at(p->inputs[0]) + 1), Glucose::mkLit(m.at(p)));
      S.addClause(Glucose::mkLit(m.at(p) + 1, 1));
      break;
    default:
      throw "unknown gate type";
      break;
    }
  }
}

/*
// decomposed xor
      
{
bool isNot = p->type == nodecircuit::NODE_XNOR;
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
Glucose::Lit tmp = Glucose::mkLit(S.newVar());
Add2Xor(S, in0, in1, tmp);
if(Floating) {
AddLoose(S, tmp, outx, out);
}
else {
Add2And(S, tmp, ~outx, out);
}
Add2Or(S, in0x, in1x, outx);
in0 = out;
in0x = outx;
}
break;
}
*/

void SatExp(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding) {
  // create miter circuit
  nodecircuit::Circuit f;
  nodecircuit::Miter(gf, rf, f);
  // prepare sat solver and node2index map
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
  for(int i = 0; i < gates.size(); i++) {
    m[gates[i]] = S.newVar();
    S.newVar();
  }
  switch (gate_encoding) {
  case 0:
    Ckt2CnfDefault(gates, m, S);
    break;
  case 1:
    Ckt2CnfDcMux(gates, m, S, 0);
    break;
  case 2:
    Ckt2CnfDcMux(gates, m, S, 1);
    break;
  case 3:
    Ckt2CnfNaryGate(gates, m, S, 0);
    break;
  case 4:
    Ckt2CnfNaryGate(gates, m, S, 1);
    break;
  case 5:
    Ckt2Cnf2Gate(gates, m, S, 0);
    break;
  case 6:
    Ckt2Cnf2Gate(gates, m, S, 1);
    break;
  case 7:
    Ckt2Cnf2GateNew(gates, m, S);
    break;
  default:
    throw "undefined gate encoding";
  }
  // outputs
  clause.clear();
  for(int i = 0; i < f.outputs.size(); i++) {
    auto p = f.outputs[i++];
    auto q = f.outputs[i];
    Glucose::Lit o = Glucose::mkLit(S.newVar());
    Add2Xor(S, Glucose::mkLit(m[p]), Glucose::mkLit(m[q]), o);
    /* // for xencoding miter
      Glucose::Lit t0 = Glucose::mkLit(S.newVar());
      Glucose::Lit t1 = Glucose::mkLit(S.newVar());
      Add2Xor(S, Glucose::mkLit(m[p]), Glucose::mkLit(m[q]), t0);
      Add2Or(S, t0, Glucose::mkLit(m[q] + 1), t1);
      Add2And(S, t1, Glucose::mkLit(m[p] + 1, 1), o);
    */
    clause.push(o);
  }
  S.addClause(clause);
  // solve
  std::cout << "var : " << S.nVars() << " clause : " << S.nClauses() << std::endl; 
  bool r = S.solve();
  if(r) {
    for(auto p : f.inputs) {
      if(S.model[m[p]] == l_True) {
	result.push_back(1);
      }
      else {
	result.push_back(0);
      }
    }
  }
  
  
  //S.setIncrementalMode();
  //S.setConfBudget(1000);
  /*
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
  return undecided;
  */
}
