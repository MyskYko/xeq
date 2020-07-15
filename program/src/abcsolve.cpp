#include <iostream>
#include <cassert>

#include <base/abc/abc.h>
#include <aig/aig/aig.h>
#include <opt/dar/dar.h>
#include <proof/cec/cec.h>

#include "abcsolve.h"

int AbcSolve(nodecircuit::Circuit &gf, nodecircuit::Circuit &rf, std::vector<bool> &result, bool fzero) {
  nodecircuit::Circuit miter;
  nodecircuit::Miter(gf, rf, miter);
  nodecircuit::NodeVector gates;
  miter.GetGates(gates);
  Gia_Man_t *pTemp;
  Gia_Man_t *pGia = Gia_ManStart(gates.size());
  Gia_ManHashStart(pGia);
  std::map<nodecircuit::Node *, int> f, g;
  // inputs
  for(auto p : miter.inputs) {
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
	assert(0);
      }
      break;
    case nodecircuit::NODE_BUF:
      f[p] = f[p->inputs[0]];
      g[p] = g[p->inputs[0]];
      break;
    case nodecircuit::NODE_NOT:
      f[p] = Abc_LitNot(f[p->inputs[0]]);
      g[p] = g[p->inputs[0]];
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
      }
      break;
    case nodecircuit::NODE_AND:
      f[p] = Gia_ManConst1Lit();
      g[p] = Gia_ManConst0Lit();
      for(auto q : p->inputs) {
	g[p] = Gia_ManHashOr(pGia,
			     Gia_ManHashOr(pGia,
					   Gia_ManHashAnd(pGia, f[p], g[q]), 
					   Gia_ManHashAnd(pGia, f[q], g[p])),
			     Gia_ManHashAnd(pGia, g[p], g[q]));
	f[p] = Gia_ManHashAnd(pGia, f[p], f[q]);
      }
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
      }
      break;
    case nodecircuit::NODE_NAND:
      f[p] = Gia_ManConst1Lit();
      g[p] = Gia_ManConst0Lit();
      for(auto q : p->inputs) {
	g[p] = Gia_ManHashOr(pGia,
			     Gia_ManHashOr(pGia,
					   Gia_ManHashAnd(pGia, f[p], g[q]), 
					   Gia_ManHashAnd(pGia, f[q], g[p])),
			     Gia_ManHashAnd(pGia, g[p], g[q]));
	f[p] = Gia_ManHashAnd(pGia, f[p], f[q]);
      }
      f[p] = Abc_LitNot(f[p]);
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
      }
      break;
    case nodecircuit::NODE_OR:
      f[p] = Gia_ManConst0Lit();
      g[p] = Gia_ManConst0Lit();
      for(auto q : p->inputs) {
	g[p] = Gia_ManHashOr(pGia,
			     Gia_ManHashOr(pGia,
					   Gia_ManHashAnd(pGia, Abc_LitNot(f[p]), g[q]),
					   Gia_ManHashAnd(pGia, Abc_LitNot(f[q]), g[p])),
			     Gia_ManHashAnd(pGia, g[p], g[q]));
	f[p] = Gia_ManHashOr(pGia, f[p], f[q]);
      }
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
      }
      break;
    case nodecircuit::NODE_NOR:
      f[p] = Gia_ManConst0Lit();
      g[p] = Gia_ManConst0Lit();
      for(auto q : p->inputs) {
	g[p] = Gia_ManHashOr(pGia,
			     Gia_ManHashOr(pGia,
					   Gia_ManHashAnd(pGia, Abc_LitNot(f[p]), g[q]),
					   Gia_ManHashAnd(pGia, Abc_LitNot(f[q]), g[p])),
			     Gia_ManHashAnd(pGia, g[p], g[q]));
	f[p] = Gia_ManHashOr(pGia, f[p], f[q]);
      }
      f[p] = Abc_LitNot(f[p]);
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
      }
      break;
    case nodecircuit::NODE_XOR:
      f[p] = Gia_ManConst0Lit();
      g[p] = Gia_ManConst0Lit();
      for(auto q : p->inputs) {
	f[p] = Gia_ManHashXor(pGia, f[p], f[q]);
	g[p] = Gia_ManHashOr(pGia, g[p], g[q]);
      }
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
      }
      break;
    case nodecircuit::NODE_XNOR:
      f[p] = Gia_ManConst0Lit();
      g[p] = Gia_ManConst0Lit();
      for(auto q : p->inputs) {
	f[p] = Gia_ManHashXor(pGia, f[p], f[q]);
	g[p] = Gia_ManHashOr(pGia, g[p], g[q]);
      }
      f[p] = Abc_LitNot(f[p]);
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
      }
      break;
    case nodecircuit::NODE_DC:
      f[p] = f[p->inputs[0]];
      g[p] = Gia_ManHashOr(pGia,
			   Gia_ManHashOr(pGia, g[p->inputs[0]], f[p->inputs[1]]),
			   g[p->inputs[1]]);
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
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
      if(fzero) {
	f[p] = Gia_ManHashAnd(pGia, f[p], Abc_LitNot(g[p]));
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
  for(auto p : miter.outputs) {
    Gia_ManAppendCo(pGia, f[p]);
  }
  Gia_ManHashStop(pGia);
  pGia = Gia_ManCleanup(pTemp = pGia);
  Gia_ManStop(pTemp);
  Cec_ParCec_t ParsCec, *pPars = &ParsCec;
  Cec_ManCecSetDefaultParams(pPars);
  //pPars->nBTLimit = 0;
  //pPars->fSilent = 1;
  //pPars->TimeLimit = 90;
  //pPars->fVerbose = 1;
  Dar_LibStart();
  int r = Cec_ManVerify(pGia, pPars);
  if(r == -1) {
    std::cout << "undecided" << std::endl;
    Gia_ManStop(pGia);
    return 1;
  }
  assert(r == 0 || r == 1);
  if(!r) {
    result.resize(Gia_ManCiNum(pGia));
    for(int j = 0; j < Gia_ManCiNum(pGia); j++) {
      if(Abc_InfoHasBit(pGia->pCexComb->pData, j)) {
	result[j] = 1;
      }
    }
  }
  Gia_ManStop(pGia);
  return 0;
}
