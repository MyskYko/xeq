#include <iostream>
#include <string>
#include <cassert>

#include <base/abc/abc.h>
#include <aig/aig/aig.h>
#include <opt/dar/dar.h>
#include <proof/cec/cec.h>
#include <base/main/main.h>
#include <base/main/mainInt.h>
#include <bdd/extrab/extraBdd.h>

#include "abcsolve.h"
#include "cec.h"

Gia_Man_t *Ckt2Gia(nodecircuit::Circuit &ckt, int gate_encoding) {
  Gia_Man_t *pGia, *pTemp;
  nodecircuit::NodeVector gates;
  ckt.GetGates(gates);
  pGia = Gia_ManStart(gates.size());
  Gia_ManHashStart(pGia);
  std::map<nodecircuit::Node *, int> f, g;
  // inputs
  for(auto p : ckt.inputs) {
    f[p] = Gia_ManAppendCi(pGia);
    g[p] = Gia_ManConst0Lit();
  }
  // gates
  for(auto p : gates) {
    switch(p->type) {
    case nodecircuit::NODE_OTHER:
      if(p->name == "1'b1") {
	f[p] = Gia_ManConst1Lit();
	g[p] = Gia_ManConst0Lit();
      }
      else if(p->name == "1'b0") {
	f[p] = Gia_ManConst0Lit();
	g[p] = Gia_ManConst0Lit();
      }
      else if(p->name == "1'bx") {
	f[p] = Gia_ManConst0Lit();
	g[p] = Gia_ManConst1Lit();
      }
      else {
	throw "unknown constant " + p->name;
      }
      break;
    case nodecircuit::NODE_BUF:
    case nodecircuit::NODE_NOT:
      {
	bool isNot = p->type == nodecircuit::NODE_NOT;
	f[p] = Abc_LitNotCond(f[p->inputs[0]], isNot);
	g[p] = g[p->inputs[0]];
	switch(gate_encoding) {
	case 0:
	  break;
	case 1:
	  f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
	  break;
	case 2:
	  /*
	  if(g[p] != Gia_ManConst0Lit()) {
	    f[p] = Gia_ManHashMux(pGia, g[p], Gia_ManAppendCi(pGia), f[p]);
	  }
	  */
	  break;
	default:
	  throw "undefined gate_encoding";
	  break;
	}
	break;
      }
    case nodecircuit::NODE_AND:
    case nodecircuit::NODE_NAND:
    case nodecircuit::NODE_OR:
    case nodecircuit::NODE_NOR:
      {
	bool isNot = p->type == nodecircuit::NODE_NAND || p->type == nodecircuit::NODE_NOR;
	bool isOr = p->type == nodecircuit::NODE_OR || p->type == nodecircuit::NODE_NOR;
	f[p] = Abc_LitNotCond(Gia_ManConst1Lit(), isOr);
	g[p] = Gia_ManConst0Lit();
	for(auto q : p->inputs) {
	  int in0 = Abc_LitNotCond(f[p], isOr);
	  int in1 = Abc_LitNotCond(f[q], isOr);
	  g[p] = Gia_ManHashOr(pGia,
			       Gia_ManHashOr(pGia,
					     Gia_ManHashAnd(pGia, in0, g[q]),
					     Gia_ManHashAnd(pGia, in1, g[p])),
			       Gia_ManHashAnd(pGia, g[p], g[q]));
	  f[p] = Gia_ManHashAnd(pGia, in0, in1);
	  f[p] = Abc_LitNotCond(f[p], isOr);
	}
	f[p] = Abc_LitNotCond(f[p], isNot);
	switch(gate_encoding) {
	case 0:
	  break;
	case 1:
	  f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
	  break;
	case 2:
	  /*
	  if(g[p] != Gia_ManConst0Lit()) {
	    f[p] = Gia_ManHashMux(pGia, g[p], Gia_ManAppendCi(pGia), f[p]);
	  }
	  */
	  break;
	default:
	  throw "undefined gate_encoding";
	  break;
	}
	break;
      }
    case nodecircuit::NODE_XOR:
    case nodecircuit::NODE_XNOR:
      {
	bool isNot = p->type == nodecircuit::NODE_XNOR;
	f[p] = Gia_ManConst0Lit();
	g[p] = Gia_ManConst0Lit();
	for(auto q : p->inputs) {
	  f[p] = Gia_ManHashXor(pGia, f[p], f[q]);
	  g[p] = Gia_ManHashOr(pGia, g[p], g[q]);
	}
	f[p] = Abc_LitNotCond(f[p], isNot);
	switch(gate_encoding) {
	case 0:
	  break;
	case 1:
	  f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
	  break;
	case 2:
	  /*
	  if(g[p] != Gia_ManConst0Lit()) {
	    f[p] = Gia_ManHashMux(pGia, g[p], Gia_ManAppendCi(pGia), f[p]);
	  }
	  */
	  break;
	default:
	  throw "undefined gate_encoding";
	  break;
	}
	break;
      }
    case nodecircuit::NODE_DC:
      f[p] = f[p->inputs[0]];
      g[p] = Gia_ManHashOr(pGia,
			   Gia_ManHashOr(pGia, g[p->inputs[0]], f[p->inputs[1]]),
			   g[p->inputs[1]]);
      switch(gate_encoding) {
      case 0:
	break;
      case 1:
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
	break;
      case 2:
	if(g[p] != Gia_ManConst0Lit()) {
	  f[p] = Gia_ManHashMux(pGia, g[p], Gia_ManAppendCi(pGia), f[p]);
	}
	break;
      default:
	throw "undefined gate_encoding";
	break;
      }
      break;
    case nodecircuit::NODE_MUX:
      // Xthen=1, Yelse=0, C=2
      f[p] = Gia_ManHashMux(pGia, f[p->inputs[2]], f[p->inputs[1]], f[p->inputs[0]]);
      g[p] = Gia_ManHashOr(pGia,
			   Gia_ManHashMux(pGia, f[p->inputs[2]], g[p->inputs[1]], g[p->inputs[0]]),
			   Gia_ManHashAnd(pGia,
					  g[p->inputs[2]],
					  Gia_ManHashOr(pGia,
							Gia_ManHashOr(pGia, g[p->inputs[1]], g[p->inputs[0]]),
							Gia_ManHashXor(pGia, f[p->inputs[1]], f[p->inputs[0]]))));
      switch(gate_encoding) {
      case 0:
	break;
      case 1:
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
	break;
      case 2:
	if(g[p] != Gia_ManConst0Lit()) {
	  f[p] = Gia_ManHashMux(pGia, g[p], Gia_ManAppendCi(pGia), f[p]);
	}
	break;
      default:
	throw "undefined gate_encoding";
	break;
      }
      break;
    case nodecircuit::NODE_ISX:
      f[p] = g[p->inputs[0]];
      g[p] = Gia_ManConst0Lit();
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
  Gia_ManStop(pTemp);
  return pGia;
}

int AbcBddCollapse(Gia_Man_t *pMiter, std::vector<bool> &result) {
  Abc_Frame_t *pAbc = Abc_FrameGetGlobalFrame();
  if(pAbc->pGia) {
    Gia_ManStop(pAbc->pGia);
  }
  pAbc->pGia = pMiter;
  std::string command = "&put; miter -t; orpos; if -K 6 -m; order; strash";
  Cmd_CommandExecute(pAbc, command.c_str());
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int maxsize = 1000000;
  int fVerbose = 0;
#ifndef NDEBUG
  fVerbose = 1;
#endif
  if(Abc_NtkBuildGlobalBdds(pNtk, maxsize, 1, 0, 0, fVerbose) == NULL) {
    // undecided
    return 1;
  }
  DdManager *dd = (DdManager *)Abc_NtkGlobalBddMan(pNtk);
  Abc_Obj_t *pNode = Abc_NtkCo(pNtk, 0);
  DdNode *bFunc = (DdNode *)Abc_ObjGlobalBdd(pNode);
  if(bFunc == b0) {
    // equivalent
    Abc_NtkFreeGlobalBdds(pNtk, 1);
    return 0;
  }
  // non-equivalent
  bFunc = Extra_bddFindOneCube(dd, bFunc);
  int *pArray = (int*)malloc(sizeof(int) *Abc_NtkCiNum(pNtk));
  Cudd_BddToCubeArray(dd, bFunc, pArray);
  result.resize(Abc_NtkCiNum(pNtk));
  int i;
  Abc_Obj_t *pCi;
  Abc_NtkForEachCi(pNtk, pCi, i) {
    if(pArray[i]) {
      std::string name(Abc_ObjName(pCi));
      name = name.substr(2);
      int j = std::stoi(name);
      result[j] = 1;
    }
  }
  free(pArray);
  Abc_NtkFreeGlobalBdds(pNtk, 1);
  return 0;
}

int AbcSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, int gate_encoding) {
  nodecircuit::Circuit miter;
  nodecircuit::Miter(gf, rf, miter);
  Gia_Man_t *pGia = Ckt2Gia(miter, gate_encoding);
  Cec_ParCec_t ParsCec, *pPars = &ParsCec;
  Cec_ManCecSetDefaultParams(pPars);
  //pPars->nBTLimit = 0;
  //pPars->fSilent = 1;
  //pPars->TimeLimit = 90;
#ifndef NDEBUG
  pPars->fVerbose = 1;
#endif
  pPars->fNaive = 1;
  Dar_LibStart();
  int r = cec(pGia, pPars);
  if(r == -1) {
    pPars->fNaive = 0;
    r = cec(pGia, pPars);
  }
  if(r == -1) {
    //acec
    ;
  }
  if(r == 1) {
    Gia_ManStop(pGia);
    return 0;
  }
  if(!r) {
    result.resize(miter.inputs.size());
    for(int j = 0; j < miter.inputs.size(); j++) {
      if(Abc_InfoHasBit(pGia->pCexComb->pData, j)) {
	result[j] = 1;
      }
    }
    return 0;
  }
  r = AbcBddCollapse(pGia, result);
  Gia_ManStop(pGia);
  return r;
}

int AbcSolve2(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, bool fzero) {
  nodecircuit::Circuit miter;
  nodecircuit::Miter(gf, rf, miter);
  Gia_Man_t *pGia = Ckt2Gia(miter, fzero);
  Abc_Frame_t *pAbc = Abc_FrameGetGlobalFrame();
  pAbc->pGia = pGia;
  //std::string command = "&demiter -f; cec miter_part0.aig miter_part1.aig";
  //Cmd_CommandExecute(pAbc, command.c_str());
  //return 0;
  std::string command = "&demiter -f; miter miter_part0.aig miter_part1.aig";
  Cmd_CommandExecute(pAbc, command.c_str());
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int r = Abc_NtkMiterSat( pNtk, 0, 0, 0, NULL, NULL );
  if(r == -1) {
    std::cout << "undecided" << std::endl;
    return 1;
  }
  assert(r == 0 || r == 1);
  if(!r) {
    result.resize(Abc_NtkCiNum(pNtk));
    int i;
    Abc_Obj_t *pCi;
    Abc_NtkForEachCi(pNtk, pCi, i) {
      if(pNtk->pModel[i]) {
	std::string name(Abc_ObjName(pCi));
	name = name.substr(2);
	int j = std::stoi(name);
	result[j] = 1;
      }
    }
  }
  return 0;
}

void DumpMiterAiger(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::string filename, bool fzero) {
  nodecircuit::Circuit miter;
  nodecircuit::Miter(gf, rf, miter);
  Gia_Man_t *pGia = Ckt2Gia(miter, fzero);
  char cstr[filename.size() + 1];
  strcpy(cstr, filename.c_str());
  Gia_AigerWrite(pGia, cstr, 0, 0, 0);
  Gia_ManStop(pGia);
}

