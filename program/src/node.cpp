#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <cctype>

#include "node.h"

using namespace std;

namespace nodecircuit {

  void removecomment(string &str) {
    auto pos = str.find("//");
    if(pos != string::npos) {
      str = str.substr(0, pos);
    }
  }

  void Circuit::ReadVerilog(string filename) {
    ifstream f(filename);
    if(!f) return;
    string line;
    string::size_type pos;
    //string rest;
    while(getline(f, line)) {
      removecomment(line);
      //line = rest + line;
      while(!line.empty() && isspace(line[0])) {
	line = line.substr(1);
      }
      if(line.empty()) continue;
      pos = line.find(" ");
      string head;
      if(pos == string::npos) {
	head = line;
	line = "";
      }
      else {
	head = line.substr(0, pos);
	line = line.substr(pos);
      }
      pos = line.find(";");
      if(pos == string::npos) {
	string nextline;
	while(getline(f, nextline)) {
	  removecomment(nextline);
	  pos = nextline.find(";");
	  if(pos == string::npos) {
	    line += nextline;
	    continue;
	  }
	  line += nextline.substr(0,pos);
	  //rest = nextline.substr(pos+1);
	  //rest.erase(remove_if(rest.begin(), rest.end(),  [](unsigned char x){return isspace(x);}), rest.end());
	  break;
	}
      }
      else {
	line = line.substr(0, pos);
      }
      line.erase(remove_if(line.begin(), line.end(),  [](unsigned char x){return isspace(x);}), line.end());
      if(head == "module") {
	// redundant
      }
      else if(head == "input") {
	stringstream ss(line);
	string item;
	while(getline(ss, item, ',')) {
	  Node *p = CreateNode(item);
	  p->is_input = true;
	  inputs.push_back(p);
	}
      }
      else if(head == "output") {
	stringstream ss(line);
	string item;
	while(getline(ss, item, ',')) {
	  Node *p = CreateNode(item);
	  p->is_output = true;
	  outputs.push_back(p);
	}
      }
      else if(head == "wire") {
	// redundant
      }
      else if(head == "endmodule") {
	break;
      }
      else { // gates
	pos = line.find("(");
	line = line.substr(pos+1);
	pos = line.find(")");
	line = line.substr(0,pos);
	stringstream ss(line);
	string item;
	getline(ss, item, ',');
	Node *p = GetOrCreateNode(item);
	while(getline(ss, item, ',')) {
	  Node *q = GetOrCreateNode(item);
	  p->inputs.push_back(q);
	  q->outputs.push_back(p);
	}
	if(head == "and") {
	  p->type = NODE_AND;
	}
	else if(head == "or") {
	  p->type = NODE_OR;
	}
	else if(head == "nand") {
	  p->type = NODE_NAND;
	}
	else if(head == "nor") {
	  p->type = NODE_NOR;
	}
	else if(head == "not") {
	  p->type = NODE_NOT;
	}
	else if(head == "buf") {
	  p->type = NODE_BUF;
	}
	else if(head == "xor") {
	  p->type = NODE_XOR;
	}
	else if(head == "xnor") {
	  p->type = NODE_XNOR;
	}
	else if(head == "_DC") {
	  p->type = NODE_DC;
	}
	else if(head == "_HMUX") {
	  p->type = NODE_MUX;
	}
	else {
	  throw "undefined type " + head;
	}
      }
    }
  }

  void Circuit::PrintNodes() {
    for(auto p : all_nodes) {
      cout << "Node " << p->name << " {" << endl;
      cout << "\ttype : " << p->type << endl;
      if(p->is_input) cout << "\tis_input" << endl;
      if(p->is_output) cout << "\tis_output" << endl;
      cout << "\tinputs :" << endl;
      for(auto q : p->inputs) {
	cout << "\t\t" << q->name << endl;
      }
      cout << "\toutputs :" << endl;
      for(auto q : p->outputs) {
	cout << "\t\t" << q->name << endl;
      }
      cout << "}" << endl << endl;
    }
  }

  void GetGatesRec(Node * p, NodeVector &gates) {
    if(p->is_input) return;
    if(p->mark) return;
    for(auto q : p->inputs) {
      GetGatesRec(q, gates);
    }
    gates.push_back(p);
    p->mark = true;
  }
  
  void Circuit::GetGates(NodeVector &gates) const {
    Unmark();
    for(auto p : outputs) {
      GetGatesRec(p, gates);
    }
  }
  
  void Circuit::GetGates(NodeVector &gates, Node *p) const {
    Unmark();
    GetGatesRec(p, gates);
  }

  void Circuit::Simulate(std::vector<int> const &pat, std::vector<int> &fs, std::vector<int> &gs, std::map<Node *, int> *fp,  std::map<Node *, int> *gp) {
    if(pat.size() != inputs.size()) {
      throw "number of inputs mismatch";
    }
    bool fgiven = 1;
    bool ggiven = 1;
    if(!fp) {
      fgiven = 0;
      fp = new std::map<Node *, int>;
    }
    if(!gp) {
      ggiven = 0;
      gp = new std::map<Node *, int>;
    }
    std::map<Node *, int> &f = *fp;
    std::map<Node *, int> &g = *gp;
    for(int i = 0; i < inputs.size(); i++) {
      f[inputs[i]] = pat[i];
      g[inputs[i]] = 0;
    }
    NodeVector gates;
    GetGates(gates);
    for(auto p : gates) {
      switch(p->type) {
      case nodecircuit::NODE_OTHER:
	if(p->name == "1'b1") {
	  f[p] = 0xffffffff;
	  g[p] = 0;
	}
	else if(p->name == "1'b0") {
	  f[p] = 0;
	  g[p] = 0;
	}
	else if(p->name == "1'bx") {
	  f[p] = 0;
	  g[p] = 0xffffffff;
	}
	break;
      case nodecircuit::NODE_BUF:
	f[p] = f[p->inputs[0]];
	g[p] = g[p->inputs[0]];
	break;
      case nodecircuit::NODE_NOT:
	f[p] = ~f[p->inputs[0]];
	g[p] = g[p->inputs[0]];
	break;
      case nodecircuit::NODE_AND:
	f[p] = 0xffffffff;
	g[p] = 0;
	for(auto q : p->inputs) {
	  g[p] = (f[p] & g[q]) | (f[q] & g[p]) | (g[p] & g[q]);
	  f[p] = f[p] & f[q];
	}
	break;
      case nodecircuit::NODE_NAND:
	f[p] = 0xffffffff;
	g[p] = 0;
	for(auto q : p->inputs) {
	  g[p] = (f[p] & g[q]) | (f[q] & g[p]) | (g[p] & g[q]);
	  f[p] = f[p] & f[q];
	}
	f[p] = ~f[p];
	break;
      case nodecircuit::NODE_OR:
	f[p] = 0;
	g[p] = 0;
	for(auto q : p->inputs) {
	  g[p] = (~f[p] & g[q]) | (~f[q] & g[p]) | (g[p] & g[q]);
	  f[p] = f[p] | f[q];
	}
	break;
      case nodecircuit::NODE_NOR:
	f[p] = 0;
	g[p] = 0;
	for(auto q : p->inputs) {
	  g[p] = (~f[p] & g[q]) | (~f[q] & g[p]) | (g[p] & g[q]);
	  f[p] = f[p] | f[q];
	}
	f[p] = ~f[p];
	break;
      case nodecircuit::NODE_XOR:
	f[p] = 0;
	g[p] = 0;
	for(auto q : p->inputs) {
	  f[p] = f[p] ^ f[q];
	  g[p] = g[p] | g[q];
	}
	break;
      case nodecircuit::NODE_XNOR:
	f[p] = 0;
	g[p] = 0;
	for(auto q : p->inputs) {
	  f[p] = f[p] ^ f[q];
	  g[p] = g[p] | g[q];
	}
	f[p] = ~f[p];
	break;
      case nodecircuit::NODE_DC:
	f[p] = f[p->inputs[0]];
	g[p] = g[p->inputs[0]] | f[p->inputs[1]] | g[p->inputs[1]];
	break;
      case nodecircuit::NODE_MUX:
	// Xthen=1, Yelse=0, C=2
	f[p] = (f[p->inputs[2]] & f[p->inputs[1]]) | (~f[p->inputs[2]] & f[p->inputs[0]]);
	g[p] = (f[p->inputs[2]] & g[p->inputs[1]]) | (~f[p->inputs[2]] & g[p->inputs[0]]) |
	  (g[p->inputs[2]] & (g[p->inputs[1]] | g[p->inputs[0]] | (f[p->inputs[1]] ^ f[p->inputs[0]])));
	break;
      default:
	throw "unkown gate type";
	break;
      }
    }
    fs.clear();
    gs.clear();
    for(auto p : outputs) {
      fs.push_back(f[p]);
      gs.push_back(g[p]);
    }
    if(!fgiven) {
      delete fp;
    }
    if(!ggiven) {
      delete gp;
    }
  }

  void Miter(Circuit const &g, Circuit const &r, Circuit &miter) {
    std::map<Node *, Node *> m;
    // inputs
    for(int i = 0; i < g.inputs.size(); i++) {
      Node *q = miter.CreateNode(g.inputs[i]->name);
      q->is_input = true;
      miter.inputs.push_back(q);
      m[g.inputs[i]] = q;
      if(g.inputs[i]->name != r.inputs[i]->name) {
	throw "input name mismatch";	
      }
      m[r.inputs[i]] = q;
    }
    // gates in g
    NodeVector gates;
    g.GetGates(gates);
    for(Node *p : gates) {
      Node *q;
      if(p->type == NODE_OTHER) {
	q = miter.GetOrCreateNode(p->name);
      }
      else {
	q = miter.CreateNode("xeq_g_" + p->name);
	q->type = p->type;
	for(Node *i : p->inputs) {
	  q->inputs.push_back(m[i]);
	}
	for(Node *o : p->outputs) {
	  q->outputs.push_back(m[o]);
	}
      }
      m[p] = q;
    }
    // gates in r
    gates.clear();
    r.GetGates(gates);
    for(Node *p : gates) {
      Node *q;
      if(p->type == NODE_OTHER) {
	q = miter.GetOrCreateNode(p->name);
      }
      else {
	q = miter.CreateNode("xeq_r_" + p->name);
	q->type = p->type;
	for(Node *i : p->inputs) {
	  q->inputs.push_back(m[i]);
	}
	for(Node *o : p->outputs) {
	  q->outputs.push_back(m[o]);
	}
      }
      m[p] = q;
    }
    // outputs
    // check x compatibility (gx = 1 -> rx = 1)
    for(int i = 0; i < g.outputs.size(); i++) {
      std::string name = g.outputs[i]->name;
      Node *gisx = miter.CreateNode("xeq_isx_g_" + name);
      gisx->type = NODE_ISX;
      gisx->inputs.push_back(m[g.outputs[i]]);
      m[g.outputs[i]]->outputs.push_back(gisx);
      Node *risx = miter.CreateNode("xeq_isx_r_" + name);
      risx->type = NODE_ISX;
      risx->inputs.push_back(m[r.outputs[i]]);
      m[r.outputs[i]]->outputs.push_back(risx);
      Node *bothx = miter.CreateNode("xeq_bothx_" + name);
      bothx->type = NODE_AND;
      bothx->inputs.push_back(gisx);
      gisx->outputs.push_back(bothx);
      bothx->inputs.push_back(risx);
      risx->outputs.push_back(bothx);
      bothx->is_output = true;
      miter.outputs.push_back(bothx);
      risx->is_output = true;
      miter.outputs.push_back(risx);
    }
    // xor equivalence
    for(int i = 0; i < g.outputs.size(); i++) {
      std::string name = g.outputs[i]->name;
      Node *gisx = miter.GetNode("xeq_isx_g_" + name);
      Node *gisnx = miter.CreateNode("xeq_isnx_g_" + name);
      gisnx->type = NODE_NOT;
      gisnx->inputs.push_back(gisx);
      gisx->outputs.push_back(gisnx);
      Node *gand = miter.CreateNode("xeq_and_g_" + name);
      gand->type = NODE_AND;
      gand->inputs.push_back(gisnx);
      gisnx->outputs.push_back(gand);
      gand->inputs.push_back(m[g.outputs[i]]);
      m[g.outputs[i]]->outputs.push_back(gand);
      Node *rand = miter.CreateNode("xeq_and_r_" + name);
      rand->type = NODE_AND;
      rand->inputs.push_back(gisnx);
      gisnx->outputs.push_back(rand);
      rand->inputs.push_back(m[r.outputs[i]]);
      m[r.outputs[i]]->outputs.push_back(rand);
      gand->is_output = true;
      miter.outputs.push_back(gand);
      rand->is_output = true;
      miter.outputs.push_back(rand);
    }
  }
}
