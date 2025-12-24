/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A6Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);
    auto cg = pag->getCallGraph();

    // TODO: complete the following two methods
    andersen.runPointerAnalysis();
    andersen.updateCallGraph(cg);

    cg->dump();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    
    WorkList<unsigned> wList;

    // Helper lambda to check existence before adding a Copy edge (avoids graph explosion)
    auto tryAddCopyEdge = [&](unsigned srcId, unsigned dstId) -> bool {
        auto* sNode = consg->getConstraintNode(srcId);
        if (!sNode) return false;

        // Scan existing edges to avoid duplicates
        for (auto* e : sNode->getCopyOutEdges()) {
            if (e->getDstID() == dstId) return false;
        }

        consg->addCopyCGEdge(srcId, dstId);
        return true;
    };

    // Phase 1: Initialize points-to sets with Address-of constraints (p = &a)
    for (auto const& item : *consg) {
        auto nodeId = item.first;
        auto* node = item.second;

        for (auto* edge : node->getAddrInEdges()) {
            if (auto* addr = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge)) {
                // If insertion is successful (element was new), add to worklist
                if (pts[nodeId].insert(addr->getSrcID()).second) {
                    wList.push(nodeId);
                }
            }
        }
    }

    // Phase 2: Worklist algorithm for transitive closure
    while (!wList.empty()) {
        auto topId = wList.pop();
        auto* topNode = consg->getConstraintNode(topId);
        const auto& topPts = pts[topId]; // Current points-to set

        // 2a. Handle Complex Constraints (Load/Store)
        // Iterate over all objects 'o' that 'topId' points to
        for (auto o : topPts) {
            
            // Store: *topId = src  =>  Add Copy Edge: src -> o
            for (auto* edge : topNode->getStoreInEdges()) {
                if (auto* store = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge)) {
                    if (tryAddCopyEdge(store->getSrcID(), o)) {
                        // If edge is new, process src to propagate its values
                        wList.push(store->getSrcID());
                    }
                }
            }

            // Load: dst = *topId  =>  Add Copy Edge: o -> dst
            for (auto* edge : topNode->getLoadOutEdges()) {
                if (auto* load = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge)) {
                    if (tryAddCopyEdge(o, load->getDstID())) {
                        // If edge is new, process o to propagate its values
                        wList.push(o);
                    }
                }
            }
        }

        // 2b. Handle Simple Copy Constraints: dst = topId
        for (auto* edge : topNode->getCopyOutEdges()) {
            if (auto* copy = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge)) {
                auto dst = copy->getDstID();
                auto& dstSet = pts[dst];
                bool isChanged = false;

                // Propagate everything topId points to -> dst
                for (auto val : topPts) {
                    if (dstSet.insert(val).second) isChanged = true;
                }

                if (isChanged) wList.push(dst);
            }
        }

        // 2c. Handle GEP Constraints: dst = &topId[i]
        for (auto* edge : topNode->getGepOutEdges()) {
            if (auto* gep = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge)) {
                auto dst = gep->getDstID();
                auto& dstSet = pts[dst];
                bool isChanged = false;

                // Calculate offset for each object topId points to
                for (auto val : topPts) {
                    auto offsetObj = consg->getGepObjVar(val, gep);
                    if (dstSet.insert(offsetObj).second) isChanged = true;
                }

                if (isChanged) wList.push(dst);
            }
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    // TODO: complete this method.
    //  The implementation of call graph is provided in the SVF library
    
    // Iterate over all indirect call sites (e.g., function pointers)
    for (const auto& entry : consg->getIndirectCallsites()) {
        auto* callNode = entry.first;
        auto funcPtrId = entry.second;

        // If the pointer has no points-to targets, skip
        if (pts.find(funcPtrId) == pts.end()) continue;

        auto* callerFunc = callNode->getCaller();
        const auto& possibleTargets = pts[funcPtrId];

        for (auto targetId : possibleTargets) {
            // Verify the target is actually a function before adding edge
            if (consg->isFunction(targetId)) {
                auto* calleeFunc = consg->getFunction(targetId);
                cg->addIndirectCallGraphEdge(callNode, callerFunc, calleeFunc);
            }
        }
    }
}
