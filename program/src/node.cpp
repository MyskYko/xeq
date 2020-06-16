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
	  dc.push_back(p);
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
  
  void Circuit::GetGates(NodeVector &gates) {
    gates.clear();
    Unmark();
    for(auto p : outputs) {
      GetGatesRec(p, gates);
    }
    Unmark();
  }
}
