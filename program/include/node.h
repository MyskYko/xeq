#pragma once

#include <string>
#include <vector>
#include <set>
#include <map>
#include <algorithm>

namespace nodecircuit {

  enum NodeType {
    NODE_OTHER,
    NODE_BUF,
    NODE_NOT,
    NODE_AND,
    NODE_NAND,
    NODE_OR,
    NODE_NOR,
    NODE_XOR,
    NODE_XNOR,
    NODE_DC,
    NODE_MUX
  };

  class Node;

  typedef std::vector<Node *> NodeVector;
  typedef std::set<Node *> NodeSet;

  class Node {
  public:
    Node() {
      type = NODE_OTHER;
      is_input = false;
      is_output = false;
    }
    virtual ~Node() {}

  public:
    NodeType type;
    std::string name;
    bool is_input;
    bool is_output;
    NodeVector inputs;  // fanins  of the node
    NodeVector outputs; // fanouts of the node
    bool mark;

  };

  class Circuit {
  public:
    Circuit() {};
    virtual ~Circuit() {};

    void ReadVerilog(std::string filename);
    void GetGates(NodeVector &gates);
    void GetGates(NodeVector &gates, Node *p); // gates in fanin cone
    void PrintNodes();

    void Simulate(std::vector<int> const &pat, std::vector<int> &fs, std::vector<int> &gs, std::map<Node *, int> *f = NULL,  std::map<Node *, int> *g = NULL); // simulate 32 patterns at once
    
  public:
    std::string name;
    NodeVector inputs;    // primary inputs
    NodeVector outputs;   // primary outputs
    NodeVector all_nodes; // all nodes including inputs/outputs/targets
    std::map<std::string, Node *> all_nodes_map; // mapping node names to nodes

    Node *CreateNode(std::string name) {
      Node *p = new Node;
      p->name = name;
      all_nodes.push_back(p);
      all_nodes_map[name] = p;
      return p;
    }
    // find a node by name, returns NULL if not found
    Node *GetNode(std::string name) {
      std::map<std::string, Node*>::iterator it = all_nodes_map.find(name);
      if (it != all_nodes_map.end())
        return it->second;
      return NULL;
    }
    Node *GetOrCreateNode(std::string name) {
      Node *p = GetNode(name);
      if(p == NULL) {
	p = CreateNode(name);
      }
      return p;
    }

    // find the index of a node in all_nodes
    int GetNodeIndex(std::string name) {
      Node *p = GetNode(name);
      std::vector<Node*>::iterator it = find(all_nodes.begin(), all_nodes.end(), p);
      bool node_exist = 0;
      if (it != all_nodes.end()) {
	node_exist = 1;
	return distance(all_nodes.begin(), it);
      }      
      abort();
    }
    
    void Unmark() {
      for(auto p : all_nodes) {
	p->mark = false;
      }
    }
  };

} // namespace nodecircuit
