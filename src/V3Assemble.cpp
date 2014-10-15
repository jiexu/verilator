// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Assemble optimizations, such as wire elimination
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2014 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3Assemble's Transformations:
//
// check all the assign inside each active, if they can be assembled to 
// just one assignment, do it.
// 
// need to consider the order of assignments, e.g., given the following 
// active@(a) begin b[0] = c; c = d; b[1] = c; end
// assignment to b can NOT be assembled.
//
// so only search the adjacent assignments.
// 
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <iomanip>
#include <vector>
#include <list>

#include "V3Global.h"
#include "V3Assemble.h"
#include "V3Ast.h"
#include "V3Const.h"
#include "V3Stats.h"
#include "V3Simulate.h"


//######################################################################

#define MAX_INSTR_COUNT 64

class AssembleVisitor : public AstNVisitor {
private:
    AstActive* m_active; 
    AstNodeAssign* m_preAssign; 
    int m_statAssembleLogic;

    bool varsSame(AstNode* node1p, AstNode* node2p) {
        if (node1p->castVarRef() && node2p->castVarRef()) 
            return node1p->same(node2p);
        else
            return false;
    }
    //
    bool adjacent(AstNode* lhsp, AstNode* rhsp) {
        // a[a:b] a[b-1:c] are adjacent
        // same as a[a:b] a[c:a+1] 
        AstSel* lSel = lhsp->castSel();
        AstSel* rSel = rhsp->castSel();
        if(!lSel || !rSel) return false;
        AstVarRef* lvar = lSel->fromp()->castVarRef();
        AstVarRef* rvar = rSel->fromp()->castVarRef();
        if (!lvar || !rvar || !varsSame(lvar, rvar)) return false;
        AstConst* lStart = lSel->lsbp()->castConst();
        AstConst* rStart = rSel->lsbp()->castConst();
        AstConst* lWidth = lSel->widthp()->castConst();
        AstConst* rWidth = rSel->widthp()->castConst();
        if (!lStart || !rStart || !lWidth || !rWidth) return false;  // too complicated
        if (lStart->toUInt()+lWidth->toUInt() == rStart->toUInt()
            || rStart->toUInt()+rWidth->toUInt() == lStart->toUInt()) {
            return true;
        }
        return false;
    }
    // assemble two Sel into one if possible 
    AstSel* merge(AstSel* pre, AstSel* cur) {
        AstVarRef* preVarRef = pre->fromp()->castVarRef();
        AstVarRef* curVarRef = cur->fromp()->castVarRef();
        if (!preVarRef || !curVarRef || curVarRef->varp() != curVarRef->varp()) return NULL; // not the same var
        if (pre->lsbConst()+pre->widthConst() == cur->lsbConst()) {
            return new AstSel(preVarRef->fileline(), preVarRef->cloneTree(false), pre->lsbConst(), pre->widthConst()+cur->widthConst());
        } else if (cur->lsbConst()+cur->widthConst() == pre->lsbConst()) { 
            return new AstSel(curVarRef->fileline(), curVarRef->cloneTree(false), cur->lsbConst(), pre->widthConst()+cur->widthConst());
        }
        else {
            return NULL;
        }
    }
    //
    void simplifyConcatBiComAsv(AstConcat* nodep) {
        // {a&b, c&d} -> {a,b} & {c,d}
        if (nodep->lhsp()->type() != nodep->rhsp()->type())  return; 
        AstNodeBiComAsv* lhs = nodep->lhsp()->unlinkFrBack()->castNodeBiComAsv();
        AstNodeBiComAsv* rhs = nodep->rhsp()->castNodeBiComAsv();
        if (!lhs || !rhs) return; 

        AstNode* ll = lhs->lhsp()->cloneTree(false);
        AstNode* lr = lhs->rhsp()->cloneTree(false);
        AstNode* rl = rhs->lhsp()->cloneTree(false);
        AstNode* rr = rhs->rhsp()->cloneTree(false);
        AstConcat* lp = new AstConcat(ll->fileline(), ll, rl);
        AstConcat* rp = new AstConcat(rl->fileline(), lr, rr);
        // use the lhs to replace the parent concat
        lhs->lhsp()->replaceWith(lp);
        lhs->rhsp()->replaceWith(rp);
        rhs->unlinkFrBack(); rhs->deleteTree();
        nodep->replaceWith(lhs);
        lhs->lhsp()->accept(*this);
        lhs->rhsp()->accept(*this);
        lhs->dtypeChgWidthSigned(lp->width(), lp->width(), AstNumeric::fromBool(true));
    }
    // simplify concat if possible, maybe use hash to check?
    void simplifyConcatSel(AstConcat* nodep) {
        // {a[1], a[0]} -> a[1:0]
        AstSel* lhs = nodep->lhsp()->castSel();
        AstSel* rhs = nodep->rhsp()->castSel();
        if (!lhs || !rhs || !adjacent(lhs, rhs)) return; 

        {
            AstSel* newSel = merge(lhs, rhs);
            if (!newSel) {
                nodep->v3fatalSrc("try to merge two SEL which can't be done");
                return;
            }

            if (newSel->lsbConst() == lhs->lsbConst()) return;
            nodep->replaceWith(newSel);
            nodep->deleteTree();
            nodep = NULL;
        }
    }
    // 
    void simplify(AstConcat* nodep)
    {
        if (nodep->lhsp()->castSel() && nodep->rhsp()->castSel()) 
            simplifyConcatSel(nodep);
        else if (nodep->lhsp()->castNodeBiComAsv() && nodep->rhsp()->castNodeBiComAsv()) 
            simplifyConcatBiComAsv(nodep);
        else return;
    }
    // assemble two assigns into one if possible
    AstNodeAssign* assemble(AstNodeAssign* pre, AstNodeAssign* cur) {
        AstSel* preSel = pre->lhsp()->castSel();
        AstSel* curSel = cur->lhsp()->castSel();
        if (!adjacent(preSel, curSel)) return NULL; 
        // too complicated
        if (pre->rhsp()->type() != cur->rhsp()->type()) return NULL;
        SimulateVisitor chkvis;
        chkvis.mainTableCheck(pre->rhsp());
        if (chkvis.instrCount() > MAX_INSTR_COUNT) return NULL;
        chkvis.clear();
        chkvis.mainTableCheck(cur->rhsp());
        if (chkvis.instrCount() > MAX_INSTR_COUNT) return NULL;
        if (pre->nextp() != cur)  return NULL;
        // 
        if (AstSel* newSel = merge(preSel, curSel)) {
            UINFO(4, "assemble to new sel: "<<newSel<<endl);
            // replace preSel with newSel
            preSel->replaceWith(newSel); preSel->deleteTree(); preSel = NULL;
            // create new rhs for pre assignment
            AstNode* newRhsp;
            if (curSel->lsbConst() == newSel->lsbConst())
                newRhsp = new AstConcat(pre->rhsp()->fileline(), pre->rhsp()->cloneTree(false), cur->rhsp()->cloneTree(false));
            else
                newRhsp = new AstConcat(pre->rhsp()->fileline(), cur->rhsp()->cloneTree(false), pre->rhsp()->cloneTree(false));
            AstNode* oldRhsp = pre->rhsp();
            oldRhsp->replaceWith(newRhsp); oldRhsp->deleteTree(); oldRhsp = NULL;
            pre->rhsp()->accept(*this); // simplify the concat
            pre->dtypeChgWidthSigned(pre->width()+cur->width(), pre->width()+cur->width(), AstNumeric::fromBool(true));
            return pre;
        } 
        return NULL;
    }




    // visitor functions
    virtual void visit(AstActive* nodep, AstNUser*) {
        m_active = nodep;
        m_preAssign = NULL;
        nodep->iterateChildren(*this);
        m_active = NULL;
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
        if (!m_active) return;
        if (!m_preAssign && nodep->lhsp()->castSel()) {
            m_preAssign = nodep;  // first assignment
        } else {
            if (!nodep->lhsp()->castSel()) { // not a sel, no chance to assemble
                m_preAssign = NULL; return; 
            }
            // check whether current assignment can be merged with previous one
            if (AstNodeAssign* newp = assemble(m_preAssign, nodep)) {
                m_preAssign = newp; 
                ++ m_statAssembleLogic;
                AstNode* delp = nodep->unlinkFrBack(); delp->deleteTree(); delp=NULL;
            } else {
                m_preAssign = nodep;
            }
        }
    }
    virtual void visit(AstConcat* nodep, AstNUser*) {
        simplify(nodep);
    }

    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
        nodep->iterateChildren(*this);
    }

private:
    static int debug() {
        static int level = -1;
        if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
        return level;
    }

public:
    // CONSTUCTORS
    AssembleVisitor(AstNode* nodep) {
        m_statAssembleLogic = 0;
        m_active= NULL;
        m_preAssign = NULL;
        nodep->accept(*this);
    }
    virtual ~AssembleVisitor() {
        V3Stats::addStat("Optimizations, logic assembled", m_statAssembleLogic);
    }
};



//######################################################################
// Assemble class functions

void V3Assemble::assembleAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    AssembleVisitor visitor (nodep);
}
