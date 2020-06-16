#include <iostream>
#include <cassert>

#include <simp/SimpSolver.h>


#include "satsolve.h"

void SatSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result) {
  Glucose::SimpSolver S;
  Glucose::vec<Glucose::Lit> clause;
  std::vector<Glucose::SimpSolver> S_all;
  int cases_gf = 1 << gf.dc.size();
  int cases_rf = 1 << rf.dc.size();

  // establish variables
  for (int i = 0; i < gf.all_nodes.size(); i++)
    S.newVar();
  for (int i = 0; i < rf.all_nodes.size(); i++)
    S.newVar();
    // variables representing xor-ed results
  for (int i = 0; i < gf.outputs.size(); i++)
    S.newVar();
    // variable representing miltered results
  S.newVar();

  // correlate inputs of the two circuits
  for (auto p: gf.inputs) {
    S.addClause(Glucose::mkLit(gf.GetNodeIndex(p->name), 1), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
    S.addClause(Glucose::mkLit(gf.GetNodeIndex(p->name)), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
  }

    // describe circuit gf
  for (auto p: gf.all_nodes) {
    if (p->is_input)
      continue;
    else
      switch(p->type) {
      case nodecircuit::NODE_OTHER:
	if (p->name == "1'b0") {
	  S.addClause(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	}
	else if (p->name == "1'b1") {
	  S.addClause(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	}
	break;
      case nodecircuit::NODE_BUF:
	assert(p->inputs.size() == 1);
	S.addClause(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name), 1), Glucose::mkLit(gf.GetNodeIndex(p->name)));
	S.addClause(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name)), Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	break;
      case nodecircuit::NODE_NOT:
	assert(p->inputs.size() == 1);
	S.addClause(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name), 1), Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	S.addClause(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name)), Glucose::mkLit(gf.GetNodeIndex(p->name)));
	break;
      case nodecircuit::NODE_AND:
	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.GetNodeIndex(q->name)), Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	  clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name), 1));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_NAND:
	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.GetNodeIndex(q->name)), Glucose::mkLit(gf.GetNodeIndex(p->name)));
	  clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name), 1));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_OR:
	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.GetNodeIndex(q->name), 1), Glucose::mkLit(gf.GetNodeIndex(p->name)));
	  clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name)));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_NOR:
	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.GetNodeIndex(q->name), 1), Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	  clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name)));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_XOR: {
	int k;
	k = (1 << p->inputs.size()) - 1;
	while (k >= 0) {
	  std::vector<bool> temp;
	  int i = k;
	  while (i > 0) {
	    temp.push_back(i % 2);
	    i /= 2;
	  }
	  while (temp.size() < p->inputs.size())
	    temp.push_back(0);
	  int count_one = 0;
	  for (int j = 0; j < p->inputs.size(); j++)
	    if (temp[j])
	      count_one++;
	  if (count_one % 2 == 1) {
	    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  else {
	    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  k--;
	}
	break;
      }
      case nodecircuit::NODE_XNOR: {
	int k;
	k = (1 << p->inputs.size()) - 1;
	while (k >= 0) {
	  std::vector<bool> temp;
	  int i = k;
	  while (i > 0) {
	    temp.push_back(i % 2);
	    i /= 2;
	  }
	  while (temp.size() < p->inputs.size())
	    temp.push_back(0);
	  int count_one = 0;
	  for (int j = 0; j < p->inputs.size(); j++)
	    if (temp[j])
	      count_one++;
	  if (count_one % 2 == 0) {
	    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  else {
	    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  k--;
	}
	break;
      }
      case nodecircuit::NODE_DC:
	assert(p->inputs.size() == 2);
	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name)));
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_MUX:
	assert(p->inputs.size() == 3);
	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name), 1));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[2])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[2])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[2])->name), 1));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[1])->name)));
	clause.push(Glucose::mkLit(gf.GetNodeIndex((p->inputs[2])->name), 1));
	S.addClause(clause);
	clause.clear();
	break;
      default:
	throw "Unknown gate type.";
	break;
      }
  }

    // describe circuit rf
  for (int t = 0; t < rf.all_nodes.size(); t++) {
    nodecircuit::Node *p = rf.all_nodes[t];
    if (p->is_input)
      continue;
    else
      switch(p->type) {
      case nodecircuit::NODE_OTHER:
	if (p->name == "1'b0") {
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	}
	else if (p->name == "1'b1") {
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	}
	break;
      case nodecircuit::NODE_BUF:
	assert(p->inputs.size() == 1);
	S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name), 1), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name)), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	break;
      case nodecircuit::NODE_NOT:
	assert(p->inputs.size() == 1);
	S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name), 1), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name)), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	break;
      case nodecircuit::NODE_AND:
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	  clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_NAND:
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	  clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_OR:
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	  clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_NOR:
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	for (auto q: p->inputs) {
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	  clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)));
	}
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_XOR: {
	int k;
	k = (1 << p->inputs.size()) - 1;
	while (k >= 0) {
	  std::vector<bool> temp;
	  int i = k;
	  while (i > 0) {
	    temp.push_back(i % 2);
	    i /= 2;
	  }
	  while (temp.size() < p->inputs.size())
	    temp.push_back(0);
	  int count_one = 0;
	  for (int j = 0; j < p->inputs.size(); j++)
	    if (temp[j])
	      count_one++;
	  if (count_one % 2 == 1) {
	    clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  else {
	    clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  k--;
	}
	break;
      }
      case nodecircuit::NODE_XNOR: {
	int k;
	k = (1 << p->inputs.size()) - 1;
	while (k >= 0) {
	  std::vector<bool> temp;
	  int i = k;
	  while (i > 0) {
	    temp.push_back(i % 2);
	    i /= 2;
	  }
	  while (temp.size() < p->inputs.size())
	    temp.push_back(0);
	  int count_one = 0;
	  for (int j = 0; j < p->inputs.size(); j++)
	    if (temp[j])
	      count_one++;
	  if (count_one % 2 == 0) {
	    clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  else {
	    clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	    for (int j = 0; j < p->inputs.size(); j++) {
	      nodecircuit::Node *q = p->inputs[j];
	      if (temp[j])
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name), 1));
	      else
		clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(q->name)));
	    }
	    S.addClause(clause);
	    clause.clear();
	  }
	  k--;
	}
	break;
      }
      case nodecircuit::NODE_DC:
	assert(p->inputs.size() == 2);
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name)));
	S.addClause(clause);
	clause.clear();
	break;
      case nodecircuit::NODE_MUX:
	assert(p->inputs.size() == 3);
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name), 1));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[2])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[2])->name)));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[2])->name), 1));
	S.addClause(clause);
	clause.clear();

	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(p->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[0])->name), 1));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[1])->name)));
	clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((p->inputs[2])->name), 1));
	S.addClause(clause);
	clause.clear();
	break;
      default:
	throw "Unknown gate type.";
	break;
      }
  }

  // milter outputs of the two circuits
  for (int i = 0; i < gf.outputs.size(); i++) {
    nodecircuit::Node *p = gf.outputs[i];
    clause.push(Glucose::mkLit(i + gf.all_nodes.size() + rf.all_nodes.size()));
    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
    clause.push(Glucose::mkLit(gf.all_nodes.size() + gf.GetNodeIndex(p->name)));
    S.addClause(clause);
    clause.clear();

    clause.push(Glucose::mkLit(i + gf.all_nodes.size() + rf.all_nodes.size()));
    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
    clause.push(Glucose::mkLit(gf.all_nodes.size() + gf.GetNodeIndex(p->name), 1));
    S.addClause(clause);
    clause.clear();

    clause.push(Glucose::mkLit(i + gf.all_nodes.size() + rf.all_nodes.size(), 1));
    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name)));
    clause.push(Glucose::mkLit(gf.all_nodes.size() + gf.GetNodeIndex(p->name)));
    S.addClause(clause);
    clause.clear();

    clause.push(Glucose::mkLit(i + gf.all_nodes.size() + rf.all_nodes.size(), 1));
    clause.push(Glucose::mkLit(gf.GetNodeIndex(p->name), 1));
    clause.push(Glucose::mkLit(gf.all_nodes.size() + gf.GetNodeIndex(p->name), 1));
    S.addClause(clause);
    clause.clear();
  }
  clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.all_nodes.size() + gf.outputs.size(), 1));
  for (int i = 0; i < gf.outputs.size(); i++) {
    S.addClause(Glucose::mkLit((gf.all_nodes.size() + rf.all_nodes.size() + i), 1), Glucose::mkLit(gf.all_nodes.size() + rf.all_nodes.size() + gf.outputs.size()));
    clause.push(Glucose::mkLit(gf.all_nodes.size() + rf.all_nodes.size() + i));
  }
  S.addClause(clause);
  clause.clear();
  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.all_nodes.size() + gf.outputs.size()));

  // traverse all the potential cases resulted by dc gates
  for (int i = 0; i < cases_gf; i++) {
    Glucose::SimpSolver S_itemp = S;
    std::vector<bool> itemp;
    int i_temp = i;
      while (i_temp > 0) {
	itemp.push_back(i_temp % 2);
	i_temp /= 2;
      }
      while (itemp.size() < gf.dc.size())
	itemp.push_back(0);
      for (int k = 0; k < itemp.size(); k++) {
	// sepecify the description of dc gates in gf
	if (itemp[k])
	  S_itemp.addClause(Glucose::mkLit(gf.GetNodeIndex(gf.dc[k]->name)), Glucose::mkLit(gf.GetNodeIndex((gf.dc[k]->inputs[1])->name), 1));
	else
	  S_itemp.addClause(Glucose::mkLit(gf.GetNodeIndex(gf.dc[k]->name), 1), Glucose::mkLit(gf.GetNodeIndex((gf.dc[k]->inputs[1])->name), 1));
      }
      for (int j = 0; j < cases_rf; j++) {
	Glucose::SimpSolver S_jtemp = S_itemp;
	std::vector<bool> jtemp;
	int j_temp = j;
	while (j_temp > 0) {
	  jtemp.push_back(j_temp % 2);
	  j_temp /= 2;
	}
	while (jtemp.size() < rf.dc.size())
	  jtemp.push_back(0);
	for (int t = 0; t < jtemp.size(); t++) {
	  // sepecify the residual description of dc gates in rf
	  if (jtemp[t])
	    S_jtemp.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(rf.dc[t]->name)), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((rf.dc[t]->inputs[1])->name), 1));
	  else
	    S_jtemp.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(rf.dc[t]->name), 1), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((rf.dc[t]->inputs[1])->name), 1));
	}
	S_all.push_back(S_jtemp);
    }
  }

  // solve established SAT problem
  // for each potential circuits of rf, if there is a equal one in gf, then gf is compatible equivalent to rf
  bool r_temp = 0;
  bool r = 0;
  for (int j = 0; j < cases_rf; j++) {
    for (int i = 0; i < cases_gf; i++) {
      if (!S_all[i * cases_rf + j].solve()) {
	// find an equal circuit in gf for the certain circuit of rf, and start looking for equal circuit in gf for the next circuit of rf
	r_temp = 1;
	break;
      }
    }
    if (!r_temp) {
      // cannot find circuit that equals to the certain circuit of rf, which means gf is not compatible equivalent to rf
      r = 0;
      // as gf is not compatible equivalent to rf, especially when rf is represented by the current circuit, so use the current rf to look for a counter-example
      std::vector<bool> temp;
      int j_temp = j;
      while (j_temp > 0) {
	temp.push_back(j_temp % 2);
	j_temp /= 2;
      }
      while (temp.size() < rf.dc.size())
	temp.push_back(0);
      for (int k = 0; k < temp.size(); k++) {
	if (temp[k])
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(rf.dc[k]->name)), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((rf.dc[k]->inputs[1])->name), 1));
	else
	  S.addClause(Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex(rf.dc[k]->name), 1), Glucose::mkLit(gf.all_nodes.size() + rf.GetNodeIndex((rf.dc[k]->inputs[1])->name), 1));
      }
      S.solve();
      break;
    }
    r_temp = 0;
    if (j == (cases_rf - 1))
      // for every potential circuits of rf, an equal circuit exists in gf, stating gf is compatible equivalent to rf
      r = 1;
  }

  if (!r)
    for(auto p: gf.inputs) {
      int i;
      i = gf.GetNodeIndex(p->name);
      if(S.model[i] == l_True)
	result.push_back(1);
      else
	result.push_back(0);
    }
}
