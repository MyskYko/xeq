#include <iostream>
#include <fstream>
#include <cassert>

#include <base/abc/abc.h>
#include <aig/aig/aig.h>
#include <opt/dar/dar.h>
#include <aig/gia/giaAig.h>

#include "abcoptimize.h"

void AbcOptimize(nodecircuit::Circuit &ckt, nodecircuit::Circuit &ckt2) {
  Gia_Man_t *pGia, *pTemp;
  std::map<int, int> dcgates;
  std::map<int, int> muxs;
  std::map<int, int> isxs;
  std::set<int> xs;
  
  {
    nodecircuit::NodeVector gates;
    ckt.GetGates(gates);
    pGia = Gia_ManStart(gates.size());
    Gia_ManHashStart(pGia);
    std::map<nodecircuit::Node *, int> f;
    // inputs
    for(auto p : ckt.inputs) {
      f[p] = Gia_ManAppendCi(pGia);
    }
    // gates
    for(auto p : gates) {
      switch(p->type) {
      case nodecircuit::NODE_OTHER:
	if(p->name == "1'b1") {
	  f[p] = Gia_ManConst1Lit();
	}
	else if(p->name == "1'b0") {
	  f[p] = Gia_ManConst0Lit();
	}
	else if(p->name == "1'bx") {
	  xs.insert(Gia_ManCiNum(pGia));
	  f[p] = Gia_ManAppendCi(pGia);
	}
	else {
	  throw "unknown constant " + p->name;
	}
	break;
      case nodecircuit::NODE_BUF:
	f[p] = f[p->inputs[0]];
	break;
      case nodecircuit::NODE_NOT:
	f[p] = Abc_LitNot(f[p->inputs[0]]);
	break;
      case nodecircuit::NODE_AND:
      case nodecircuit::NODE_NAND:
      case nodecircuit::NODE_OR:
      case nodecircuit::NODE_NOR:
	{
	  bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	  bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	  f[p] = Abc_LitNotCond(Gia_ManConst1Lit(), isOr);
	  for(auto q : p->inputs) {
	    int in0 = Abc_LitNotCond(f[p], isOr);
	    int in1 = Abc_LitNotCond(f[q], isOr);
	    f[p] = Gia_ManHashAnd(pGia, in0, in1);
	    f[p] = Abc_LitNotCond(f[p], isOr);
	  }
	  f[p] = Abc_LitNotCond(f[p], isNot);
	  break;
	}
      case nodecircuit::NODE_XOR:
      case nodecircuit::NODE_XNOR:
	{
	  bool isNot = p->type == nodecircuit::NODE_XNOR;
	  f[p] = Gia_ManConst0Lit();
	  for(auto q : p->inputs) {
	    f[p] = Gia_ManHashXor(pGia, f[p], f[q]);
	  }
	  f[p] = Abc_LitNotCond(f[p], isNot);
	  break;
	}
      case nodecircuit::NODE_DC:
	dcgates[Gia_ManCiNum(pGia)] = Gia_ManCoNum(pGia);
	f[p] = Gia_ManAppendCi(pGia);
	Gia_ManAppendCo(pGia, f[p->inputs[0]]);
	Gia_ManAppendCo(pGia, f[p->inputs[1]]);
	break;
      case nodecircuit::NODE_MUX:
	muxs[Gia_ManCiNum(pGia)] = Gia_ManCoNum(pGia);
	f[p] = Gia_ManAppendCi(pGia);
	Gia_ManAppendCo(pGia, f[p->inputs[0]]);
	Gia_ManAppendCo(pGia, f[p->inputs[1]]);
	Gia_ManAppendCo(pGia, f[p->inputs[2]]);
	break;
      case nodecircuit::NODE_ISX:
	isxs[Gia_ManCiNum(pGia)] = Gia_ManCoNum(pGia);
	f[p] = Gia_ManAppendCi(pGia);
	Gia_ManAppendCo(pGia, f[p->inputs[0]]);
	break;
      default:
	throw "unkown gate type";
	break;
      }
    }
    // outputs
    for(auto p : ckt.outputs) {
      Gia_ManAppendCo(pGia, f[p]);
    }
    Gia_ManHashStop(pGia);
    pGia = Gia_ManCleanup(pTemp = pGia);
  }
  
  //char cst[10] = "org.aig";
  //Gia_AigerWrite(pGia, cst, 0, 0, 0);
  
  {
    std::cout << "original AIG nodes :" << pGia->nObjs << std::endl;
    
    Dar_LibStart();
    pGia = Gia_ManCompress2(pTemp = pGia, 1, 0);
    Gia_ManStop(pTemp);
    pGia = Gia_ManCompress2(pTemp = pGia, 1, 0);
    Gia_ManStop(pTemp);
    pGia = Gia_ManCompress2(pTemp = pGia, 1, 0);
    Gia_ManStop(pTemp);
    pGia = Gia_ManCompress2(pTemp = pGia, 1, 0);
    Gia_ManStop(pTemp);
    pGia = Gia_ManCompress2(pTemp = pGia, 1, 0);
    Gia_ManStop(pTemp);
    
    std::cout << "optimized AIG nodes :" << pGia->nObjs << std::endl;
  }

  {
    bool fmap = 0;
    
    if(!fmap) {
      int i;
      Gia_Obj_t *pObj;
      std::map<int, nodecircuit::Node *> m;
      std::map<int, int> rev_cutmap;
      std::string prefix = "abc_opt_new";
      int ngates = 0;
      // constants
      m[Gia_ManConst0Lit()] = ckt2.CreateNode("1'b0");
      m[Gia_ManConst1Lit()] = ckt2.CreateNode("1'b1");
      // inputs
      Gia_ManForEachCi(pGia, pObj, i) {
	nodecircuit::Node *p;
	if(dcgates.count(i)) {
	  p = ckt2.CreateNode(prefix + std::to_string(ngates++));
	  p->type = nodecircuit::NODE_DC;
	  rev_cutmap[dcgates[i]] = i;
	  rev_cutmap[dcgates[i] + 1] = i;
	}
	else if(muxs.count(i)) {
	  p = ckt2.CreateNode(prefix + std::to_string(ngates++));
	  p->type = nodecircuit::NODE_MUX;
	  rev_cutmap[muxs[i]] = i;
	  rev_cutmap[muxs[i] + 1] = i;
	  rev_cutmap[muxs[i] + 2] = i;
	}
	else if(isxs.count(i)) {
	  p = ckt2.CreateNode(prefix + std::to_string(ngates++));
	  p->type = nodecircuit::NODE_ISX;
	  rev_cutmap[isxs[i]] = i;
	}
	else if(xs.count(i)) {
	  p = ckt2.GetOrCreateNode("1'bx");
	}
	else {
	  p = ckt2.CreateNode(ckt.inputs[ckt2.inputs.size()]->name);
	  p->is_input = true;
	  ckt2.inputs.push_back(p);
	}
	m[Gia_Obj2Lit(pGia, pObj)] = p;
      }
      // gates
      Gia_ManForEachAnd(pGia, pObj, i) {
	nodecircuit::Node *p, *p0, *p1;
	int i0, i1;
	i0 = Gia_ObjFaninLit0p(pGia, pObj);
	i1 = Gia_ObjFaninLit1p(pGia, pObj);
	if(!m.count(i0)) {
	  assert(m.count(Abc_LitNot(i0)));
	  m[i0] = ckt2.CreateNode(prefix + std::to_string(ngates++));
	  m[i0]->type = nodecircuit::NODE_NOT;
	  m[i0]->inputs.push_back(m[Abc_LitNot(i0)]);
	  m[Abc_LitNot(i0)]->outputs.push_back(m[i0]);
	}
	p0 = m[i0];
	if(!m.count(i1)) {
	  assert(m.count(Abc_LitNot(i1)));
	  m[i1] = ckt2.CreateNode(prefix + std::to_string(ngates++));
	  m[i1]->type = nodecircuit::NODE_NOT;
	  m[i1]->inputs.push_back(m[Abc_LitNot(i1)]);
	  m[Abc_LitNot(i1)]->outputs.push_back(m[i1]);
	}
	p1 = m[i1];
	p = ckt2.CreateNode(prefix + std::to_string(ngates++));
	p->type = nodecircuit::NODE_AND;
	p->inputs.push_back(p0);
	p0->outputs.push_back(p);
	p->inputs.push_back(p1);
	p1->outputs.push_back(p);
	m[Gia_Obj2Lit(pGia, pObj)] = p;
      }
      // outputs
      Gia_ManForEachCo(pGia, pObj, i) {
	nodecircuit::Node *p, *p0;
	int i0 = Gia_ObjFaninLit0p(pGia, pObj);
	if(!m.count(i0)) {
	  assert(m.count(Abc_LitNot(i0)));
	  m[i0] = ckt2.CreateNode(prefix + std::to_string(ngates++));
	  m[i0]->type = nodecircuit::NODE_NOT;
	  m[i0]->inputs.push_back(m[Abc_LitNot(i0)]);
	  m[Abc_LitNot(i0)]->outputs.push_back(m[i0]);
	}
	p0 = m[i0];
	if(rev_cutmap.count(i)) {
	  p = m[Gia_ManCiLit(pGia, rev_cutmap[i])];
	}
	else {
	  p = ckt2.CreateNode(ckt.outputs[ckt2.outputs.size()]->name);
	  p->type = nodecircuit::NODE_BUF;
	  p->is_output = true;
	  ckt2.outputs.push_back(p);
	}
	p->inputs.push_back(p0);
	p0->outputs.push_back(p);
      }
      assert(ckt.inputs.size() == ckt2.inputs.size());
      assert(ckt.outputs.size() == ckt2.outputs.size());
      return;
  }
  else {
    std::ofstream libfile("xag.genlib");
    libfile << "GATE zero	0	O=CONST0;" << std::endl;
    libfile << "GATE one	0	O=CONST1;" << std::endl;
    libfile << "GATE buf	0	O=a;		PIN * INV 1 999 0.9 0.3 0.9 0.3" << std::endl;
    libfile << "GATE not	0	O=!a;		PIN * INV 1 999 0.9 0.3 0.9 0.3" << std::endl;
    libfile << "GATE and	2	O=a*b;	PIN * INV 1 999 1.0 0.2 1.0 0.2" << std::endl;
    libfile << "GATE xor	2	O=a*!b+!a*b;	PIN * INV 1 999 1.0 0.2 1.0 0.2" << std::endl;
    libfile.close();

    /*
    Abc_Frame_t *pAbc = Abc_FrameGetGlobalFrame();
    if(pAbc->pGia) {
      Gia_ManStop(pAbc->pGia);
    }
    pAbc->pGia = pGia;
    std::string command = "&put: read_library xag.genlib; map -a";
    Cmd_CommandExecute(pAbc, command.c_str());
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    */
  }
}
}
