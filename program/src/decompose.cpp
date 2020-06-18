#include <iostream>

#include <base/abc/abc.h>
#include <proof/cec/cec.h>

#include "node.h"
#include "decompose.h"

void decompose_rec(nodecircuit::NodeVector const &ggates, nodecircuit::NodeVector const &rgates, int n, std::map<nodecircuit::Node *, int> &m, Gia_Man_t *pGia, int condition, nodecircuit::NodeVector const &goutputs, nodecircuit::NodeVector const &routputs, std::vector<bool> &result, int depth) {
  nodecircuit::Node *p;
  int target = -1;
  while(1) {
    if(n < ggates.size()) {
      p = ggates[n];
    }
    else if(n < ggates.size() + rgates.size()) {
      p = rgates[n - ggates.size()];
    }
    else {
      // solve at a leaf
      std::cout << "solve at leaf with depth " << depth << std::endl;
      std::vector<int> xors;
      for(int i = 0; i < goutputs.size(); i++) {
	if(goutputs[i]->mark) {
	  continue;
	}
	if(routputs[i]->mark) {
	  result.resize(Gia_ManCiNum(pGia));
	  for(int j = 0; j < Gia_ManCiNum(pGia); j++) {
	    if(Abc_InfoHasBit(pGia->pCexComb->pData, j)) {
	      result[j] = 1;
	    }
	  }
 	  return;
	}
	Gia_ManAppendCo(pGia, m[goutputs[i]]);
	Gia_ManAppendCo(pGia, m[routputs[i]]);
      }
      if(!Gia_ManPoNum(pGia)) {
	return;
      }
      Cec_ParCec_t ParsCec, * pPars = &ParsCec;
      Cec_ManCecSetDefaultParams(pPars);
      pPars->fSilent = 1;
      int r = Cec_ManVerify(pGia, pPars);
      assert(r == 0 || r == 1);
      if(!r) {
	result.resize(Gia_ManCiNum(pGia));
	for(int j = 0; j < Gia_ManCiNum(pGia); j++) {
	  if(Abc_InfoHasBit(pGia->pCexComb->pData, j)) {
	    result[j] = 1;
	  }
	}
      }
      return;
    }
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if(p->name == "1'b1") {
	m[p] = Gia_ManConst1Lit();
      }
      else if(p->name == "1'b0") {
	m[p] = Gia_ManConst0Lit();
      }
      else if(p->name == "1'bx") {
	p->mark = 1;
      }
      break;
    case nodecircuit::NODE_BUF:
      if(p->inputs[0]->mark) {
	p->mark = 1;
	break;
      }
      m[p] = m[p->inputs[0]];
      break;
    case nodecircuit::NODE_NOT:
      if(p->inputs[0]->mark) {
	p->mark = 1;
	break;
      }
      m[p] = Abc_LitNot(m[p->inputs[0]]);
      break;
    case nodecircuit::NODE_AND:
      {
	bool hasx = 0;
	m[p] = Gia_ManConst1Lit();
	for(auto q : p->inputs) {
	  if(q->mark) {
	    hasx = 1;
	    continue;
	  }
	  m[p] = Gia_ManAppendAnd2(pGia,m[p], m[q]);
	}
	if(hasx) {
	  target = m[p];
	}
	break;
      }
    case nodecircuit::NODE_NAND:
      {
	bool hasx = 0;
	m[p] = Gia_ManConst1Lit();
	for(auto q : p->inputs) {
	  if(q->mark) {
	    hasx = 1;
	    continue;
	  }
	  m[p] = Gia_ManAppendAnd2(pGia,m[p], m[q]);
	}
	if(hasx) {
	  target = m[p];
	}
	m[p] = Abc_LitNot(m[p]);
	break;
      }
    case nodecircuit::NODE_OR:
      {
	bool hasx = 0;
	m[p] = Gia_ManConst0Lit();
	for(auto q : p->inputs) {
	  if(q->mark) {
	    hasx = 1;
	    continue;
	  }
	  m[p] = Gia_ManAppendOr2(pGia,m[p], m[q]);
	}
	if(hasx) {
	  target = Abc_LitNot(m[p]);
	}
	break;
      }
    case nodecircuit::NODE_NOR:
      {
	bool hasx = 0;
	m[p] = Gia_ManConst0Lit();
	for(auto q : p->inputs) {
	  if(q->mark) {
	    hasx = 1;
	    continue;
	  }
	  m[p] = Gia_ManAppendOr2(pGia,m[p], m[q]);
	}
	if(hasx) {
	  target = Abc_LitNot(m[p]);
	}
	m[p] = Abc_LitNot(m[p]);
	break;
      }
    case nodecircuit::NODE_XOR:
      {
	for(auto q : p->inputs) {
	  p->mark = p->mark || q->mark;
	}
	if(!p->mark) {
	  m[p] = Gia_ManConst0Lit();
	  for(auto q : p->inputs) {
	    m[p] = Gia_ManAppendXor2(pGia, m[p], m[q]);
	  }
	}
	break;
      }
    case nodecircuit::NODE_XNOR:
      {
	for(auto q : p->inputs) {
	  p->mark = p->mark || q->mark;
	}
	if(!p->mark) {
	  m[p] = Gia_ManConst0Lit();
	  for(auto q : p->inputs) {
	    m[p] = Gia_ManAppendXor2(pGia, m[p], m[q]);
	  }
	  m[p] = Abc_LitNot(m[p]);	    
	}
	break;
      }
    case nodecircuit::NODE_DC:
      if(p->inputs[0]->mark || p->inputs[1]->mark) {
	p->mark = 1;
	break;
      }
      m[p] = m[p->inputs[0]];
      target = m[p->inputs[1]];
      break;
    case nodecircuit::NODE_MUX:
      // Xthen=1, Yelse=0, C=2
      if(p->inputs[2]->mark && (p->inputs[0]->mark || p->inputs[1]->mark)) {
	p->mark = 1;
	break;
      }
      if(p->inputs[0]->mark && p->inputs[1]->mark) {
	p->mark = 1;
	break;
      }
      m[p] = Gia_ManAppendMux2(pGia, m[p->inputs[2]], m[p->inputs[1]], m[p->inputs[0]]);
      if(p->inputs[2]->mark) {
	target = Gia_ManAppendXor2(pGia, m[p->inputs[1]], m[p->inputs[0]]);
	break;
      }
      if(p->inputs[0]->mark) {
	target = Abc_LitNot(m[p->inputs[2]]);
	break;
      }
      if(p->inputs[1]->mark) {
	target = m[p->inputs[2]];
	break;
      }
      break;
    default:
      throw "unkown gate type";
      break;
    }
    if(target >= 0) {
      break;
    }
    n++;
  }

  // if p is assigned to x
  {
    Gia_Man_t *pNew = Gia_ManDup(pGia);
    int cNew = Gia_ManAppendAnd2(pNew, condition, target);
    Gia_ManAppendCo(pNew, cNew);
    Gia_ManAppendCo(pNew, Gia_ManConst0Lit());
    Cec_ParCec_t ParsCec, * pPars = &ParsCec;
    Cec_ManCecSetDefaultParams(pPars);
    pPars->fSilent = 1;
    int r = Cec_ManVerify(pNew, pPars);
    assert(r == 0 || r == 1);
    if(!r) {
      Vec_IntClear(pNew->vCos);
      pNew->nObjs -= 2;
      p->mark = 1;
      decompose_rec(ggates, rgates, n + 1, m, pNew, cNew, goutputs, routputs, result, depth+1);
      p->mark = 0;
    }
    Gia_ManStop(pNew);
    if(!result.empty()) {
      return;
    }
  }
  // else
  {
    Gia_Man_t *pNew = Gia_ManDup(pGia);
    int cNew = Gia_ManAppendAnd2(pNew, condition, Abc_LitNot(target));
    Gia_ManAppendCo(pNew, cNew);
    Gia_ManAppendCo(pNew, Gia_ManConst0Lit());
    Cec_ParCec_t ParsCec, * pPars = &ParsCec;
    Cec_ManCecSetDefaultParams(pPars);
    pPars->fSilent = 1;
    int r = Cec_ManVerify(pNew, pPars);
    assert(r == 0 || r == 1);
    if(!r) {
      Vec_IntClear(pNew->vCos);
      pNew->nObjs -= 2;
      decompose_rec(ggates, rgates, n + 1, m, pNew, cNew, goutputs, routputs, result, depth+1);
    }
    Gia_ManStop(pNew);
  }
}

void decompose(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result) {
  nodecircuit::NodeVector ggates;
  gf.GetGates(ggates);
  gf.Unmark();
  nodecircuit::NodeVector rgates;
  rf.GetGates(rgates);
  rf.Unmark();
  std::map<nodecircuit::Node *, int> m;
  Gia_Man_t *pGia = Gia_ManStart(ggates.size() + rgates.size());
  for(int i = 0; i < gf.inputs.size(); i++) {
    int pi = Gia_ManAppendCi(pGia);
    m[gf.inputs[i]] = pi;
    m[rf.inputs[i]] = pi;
  }
  decompose_rec(ggates, rgates, 0, m, pGia, Gia_ManConst1Lit(), gf.outputs, rf.outputs, result, 0);
  Gia_ManStop(pGia);
}
