#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <cctype>

#include <base/abc/abc.h>
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "minimize.h"

using namespace std;

void removecomment(string &str) {
  auto pos = str.find("//");
  if(pos != string::npos) {
    str = str.substr(0, pos);
  }
}

void Verilog2BLIF(string filename, vector<string> &inputs, vector<string> &outputs, vector<string> &dc) {
  ifstream f(filename);
  string line;
  string::size_type pos;
  vector<string> inputs_extend;
  vector<string> outputs_extend;
  ofstream blif("temp.blif");
    
  while(getline(f, line)) {
    removecomment(line);    
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
	inputs.push_back(item);
	item = item.substr(1);
	inputs_extend.push_back(item);
      }
    }
    else if(head == "output") {
      stringstream ss(line);
      string item;
      while(getline(ss, item, ',')) {
	outputs.push_back(item);
	item = item.substr(1);
	outputs_extend.push_back(item);
      }
    }
    else if(head == "wire") {
      // redundant
    }
    else if(head == "endmodule") {
      break;
    }
    else { // gates
      vector<string> names;
      if (head == "_DC") {
	dc.push_back(line);
	pos = line.find("(");
	line = line.substr(pos+1);
	pos = line.find(")");
	line = line.substr(0,pos);
	stringstream ss(line);
	string item;
	getline(ss, item, ',');
	names.push_back(item);
	while(getline(ss, item, ',')) {
	  names.push_back(item);	  	
	}
	assert(names.size() == 3);
	bool flag = false;
	for (int i = 0; i < inputs_extend.size(); i++) {
	  if (names[0] == inputs_extend[i] || names[0][0] == '\'') {
	    break;
	  }
	  if (i == inputs_extend.size() - 1) {
	    flag = true;
	  }
	}
	if (flag) {
	  inputs_extend.push_back(names[0]);
	}
	flag = false;
	for (int i = 0; i < outputs_extend.size(); i++) {
	  if (names[1] == outputs_extend[i] || names[1][0] == '\'') {
	    break;
	  }
	  if (i == outputs_extend.size() - 1) {
	    flag = true;
	  }
	}
	if (flag) {
	  outputs_extend.push_back(names[1]);
	}
	flag = false;
	for (int i = 0; i < outputs_extend.size(); i++) {
	  if (names[2] == outputs_extend[i] || names[2][0] == '\'') {
	    break;
	  }
	  if (i == outputs_extend.size() - 1) {
	    flag = true;
	  }
	}
	if (flag) {
	  outputs_extend.push_back(names[2]);
	}	 	    	  	 
      }
      else {
	pos = line.find("(");
	line = line.substr(pos+1);
	pos = line.find(")");
	line = line.substr(0,pos);
	stringstream ss(line);
	string item;
	getline(ss, item, ',');
	names.push_back(item);
	while(getline(ss, item, ',')) {
	  names.push_back(item);	  	
	}
	blif << ".names ";
	for (int i = 1; i < names.size(); i++) {
	  blif << names[i] << " ";
	}
	blif << names[0] << endl;
	if(head == "and") {
	  for (int i = 1; i < names.size(); i++) {
	    blif << "1";
	  }
	  blif << " 1" << endl;
	}	         	 
	else if(head == "or") {
	  for (int i = 1; i < names.size(); i++) {
	    for (int j = 1; j < i; j++) {
	      blif << "-";
	    }
	    blif << "1" ;
	    for (int j = i + 1; j < names.size(); j++) {
	      blif << "-";
	    }
	    blif << " 1" << endl;
	  }
	}
	else if(head == "nand") {
	  for (int i = 1; i < names.size(); i++) {
	    for (int j = 1; j < i; j++) {
	      blif << "-";
	    }
	    blif << "0" ;
	    for (int j = i + 1; j < names.size(); j++) {
	      blif << "-";
	    }
	    blif << " 1" << endl;
	  }	    
	}
	else if(head == "nor") {
	  for (int i = 1; i < names.size(); i++) {
	    blif << "0";
	  }
	  blif << " 1" << endl;
	}
	else if(head == "not") {
	  assert(names.size() == 2);
	  blif << "0 1" << endl;
	}
	else if(head == "buf") {
	  assert(names.size() == 2);
	  blif << "1 1" << endl;
	}
	else if(head == "xor") {
	  int k;
	  k = (1 << (names.size() - 1)) - 1;	  
	  while (k >= 0) {
	    vector<bool> temp;
	    int i = k;
	    while (i > 0) {
	      temp.push_back(i % 2);
	      i /= 2;
	    }
	    while (temp.size() < names.size() - 1)
	      temp.push_back(0);	    	    
	    int count_one = 0;
	    for (int j = 0; j < names.size() - 1; j++)
	      if (temp[j])
		count_one++;
	    if (count_one % 2 == 1) {
	      for (int j = temp.size() - 1; j >= 0; j--)
		blif << temp[j];
	      blif << " 1" << endl;
	    }	    
	    k--;
	  }
	}
	else if(head == "xnor") {
	  int k;
	  k = (1 << (names.size() - 1)) - 1;
	  while (k >= 0) {
	    vector<bool> temp;
	    int i = k;
	    while (i > 0) {
	      temp.push_back(i % 2);
	      i /= 2;
	    }
	    while (temp.size() < names.size() - 1)
	      temp.push_back(0);
	    int count_one = 0;
	    for (int j = 0; j < names.size() - 1; j++)
	      if (temp[j])
		count_one++;
	    if (count_one % 2 == 0) {
	      for (int j = temp.size() - 1; j >= 0; j--)
		blif << temp[j];
	      blif << " 1" << endl;
	    }	              
	    k--;
	  }
	}	
	else if(head == "_HMUX") {
	  assert(names.size() == 4);
	  blif << "1-0 1" << endl;
	  blif << "-11 1" << endl;
	}
	else {
	  throw "undefined type " + head;
	}
      }
    }
  }
  blif << ".end";
  blif.close();
  f.close();
  blif.open("Verilog2BLIF.blif");
  blif << ".module Ckt" << endl;   
  blif << ".inputs ";
  for (int i = 0; i < inputs_extend.size(); i++) {
    blif << inputs_extend[i] << " ";
  }
  blif << endl;
  blif << ".outputs ";
  for (int i = 0; i < outputs_extend.size(); i++) {
    blif << outputs_extend[i] << " ";
  }
  blif << endl;
  ifstream blif_temp("temp.blif");
  string temp;
  while (getline(blif_temp, temp)) {
    blif << temp << endl;
  }
  blif.close();
  blif_temp.close();
  
}      

void BLIF2Verilog(string blifname, string verilogname, vector<string> inputs, vector<string> outputs, vector<string> dc) {
  string temp = "temp.v"
  Abc_Frame_t *pAbc;
  pAbc = Abc_FrameGetGlobalFrame();
  string command = "read ";
  command += blifname;
  command += "; fx; strash; resyn2; resyn2; resyn2; resyn2; resyn2; write ";
  command += temp;
  Cmd_CommandExecute(pAbc, command.c_str());
  ifstream v_temp(temp);
  ofstream v(verilogname);
  string::size_type pos;
  
  v << "input ";
  v << inputs[0];
  for (int i = 1; i < inputs.size(); i++)
    v << " ,"<< inputs[i];
  v << " ;" << endl;
  v << "output ";
  v << outputs[0];
  for (int i = 1; i < outputs.size(); i++)
    v << " ,"<< outputs[i];
  v << " ;" << endl;

  string line;
  while(getline(v_temp, line)) {
    removecomment(line);    
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
	break;
      }
    }
    else {
      line = line.substr(0, pos);
    }
    line.erase(remove_if(line.begin(), line.end(),  [](unsigned char x){return isspace(x);}), line.end());
    if(head == "module" && head == "input" && head == "output" && head == "wire") {
      continue;
    }
    else if (head == "endmodule") {
      break;
    }
    else {
      v << head << " " << line << ";" << endl;
    }
  }
  for (int i = 0; i < dc.size(); i++) {
    v << "_DC " << dc[i] << ";" << endl;
  }
  v << "endmodule";
  v_temp.close();
  v.close();
}

void Minimize(string filename) {
  vector<string> inputs;
  vector<string> outputs;
  vector<string> dc;
  string blifname = "Verilog2BLIF.blif";
  string verilogname = "minimized_" + filename;
  Verilog2BLIF(filename, inputs, outputs, dc);
  BLIF2Verilog(blifname, verilogname, inputs, outputs, dc) {
}

