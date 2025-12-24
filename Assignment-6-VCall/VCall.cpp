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
    
    WorkList<unsigned> candidates;

    for (auto const& pair : *consg)
    {
        SVF::ConstraintNode* node = pair.second;
        SVF::NodeID nodeId = pair.first;

        for (auto edge : node->getAddrInEdges())
        {
            if (auto addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge))
            {
                if (pts[nodeId].insert(addrEdge->getSrcID()).second)
                {
                    candidates.push(nodeId);
                }
            }
        }
    }

    while (!candidates.empty())
    {
        SVF::NodeID currId = candidates.pop();
        SVF::ConstraintNode* currNode = consg->getConstraintNode(currId);
        const auto& currPts = pts[currId];

        
        for (SVF::NodeID objId : currPts)
        {
            for (auto edge : currNode->getStoreInEdges())
            {
                if (auto storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge))
                {
                    SVF::NodeID srcId = storeEdge->getSrcID();
                    bool edgeExists = false;
                    auto srcNode = consg->getConstraintNode(srcId);
                    for (auto outEdge : srcNode->getCopyOutEdges()) {
                        if (outEdge->getDstID() == objId) {
                            edgeExists = true;
                            break;
                        }
                    }
                    
                    if (!edgeExists) {
                        consg->addCopyCGEdge(srcId, objId);
                        candidates.push(srcId);
                    }
                }
            }

            for (auto edge : currNode->getLoadOutEdges())
            {
                if (auto loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge))
                {
                    SVF::NodeID dstId = loadEdge->getDstID();
                    bool edgeExists = false;
                    auto objNode = consg->getConstraintNode(objId);
                    if (objNode) {
                        for (auto outEdge : objNode->getCopyOutEdges()) {
                            if (outEdge->getDstID() == dstId) {
                                edgeExists = true;
                                break;
                            }
                        }
                    }

                    if (!edgeExists) {
                        consg->addCopyCGEdge(objId, dstId);
                        candidates.push(objId);
                    }
                }
            }
        }

        for (auto edge : currNode->getCopyOutEdges())
        {
            if (auto copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge))
            {
                SVF::NodeID dstId = copyEdge->getDstID();
                if (pts[dstId].insert(currPts.begin(), currPts.end()))
                {
                    candidates.push(dstId); 
                }
            }
        }

        for (auto edge : currNode->getGepOutEdges())
        {
            if (auto gepEdge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge))
            {
                SVF::NodeID dstId = gepEdge->getDstID();
                bool changed = false;
                for (SVF::NodeID o : currPts)
                {
                    SVF::NodeID fieldInfo = consg->getGepObjVar(o, gepEdge);
                    if (pts[dstId].insert(fieldInfo).second) {
                        changed = true;
                    }
                }
                
                if (changed) {
                    candidates.push(dstId);
                }
            }
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    // TODO: complete this method.
    //  The implementation of call graph is provided in the SVF library
    
    auto& indirectCalls = consg->getIndirectCallsites();
    
    for (auto it = indirectCalls.begin(); it != indirectCalls.end(); ++it)
    {
        const SVF::CallICFGNode* cNode = it->first;
        SVF::NodeID funcPtrId = it->second;

        if (pts.find(funcPtrId) == pts.end()) continue;

        for (SVF::NodeID targetId : pts[funcPtrId])
        {
            if (consg->isFunction(targetId))
            {
                const SVF::Function* calleeFunc = consg->getFunction(targetId);
                const SVF::Function* callerFunc = cNode->getCaller();
                
                if (!cg->hasCallGraphEdge(callerFunc->getId(), calleeFunc->getId()))
                {
                     cg->addIndirectCallGraphEdge(cNode, callerFunc, calleeFunc);
                }
            }
        }
    }
}
