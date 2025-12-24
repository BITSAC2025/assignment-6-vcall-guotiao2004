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
    WorkList<unsigned> nodeQueue;

    auto addCopyEdge = [&](unsigned src, unsigned dst) -> bool
    {
        auto *srcNode = consg->getConstraintNode(src);
        if (!srcNode) return false;

        for (auto edge : srcNode->getCopyOutEdges())
        {
            if (edge->getDstID() == dst)
                return false;
        }

        consg->addCopyCGEdge(src, dst);
        return true;
    };

    for (auto iter = consg->begin(); iter != consg->end(); ++iter)
    {
        auto nodeId = iter->first;
        SVF::ConstraintNode *node = iter->second;

        for (auto edge : node->getAddrInEdges())
        {
            if (auto *addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge))
            {
                auto srcId = addrEdge->getSrcID();
                if (pts[nodeId].insert(srcId).second)
                {
                    nodeQueue.push(nodeId);
                }
            }
        }
    }

    while (!nodeQueue.empty())
    {
        auto currID = nodeQueue.pop();
        auto *currNode = consg->getConstraintNode(currID);
        auto &currPts = pts[currID];

        for (auto obj : currPts)
        {
            for (auto edge : currNode->getStoreInEdges())
            {
                if (auto *storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge))
                {
                    if (addCopyEdge(storeEdge->getSrcID(), obj))
                        nodeQueue.push(storeEdge->getSrcID());
                }
            }

            for (auto edge : currNode->getLoadOutEdges())
            {
                if (auto *loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge))
                {
                    if (addCopyEdge(obj, loadEdge->getDstID()))
                        nodeQueue.push(obj);
                }
            }
        }

        for (auto edge : currNode->getCopyOutEdges())
        {
            if (auto *copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge))
            {
                auto dstID = copyEdge->getDstID();
                auto &dstPts = pts[dstID];
                bool changed = false;

                for (auto val : currPts)
                    changed |= dstPts.insert(val).second;

                if (changed)
                    nodeQueue.push(dstID);
            }
        }

        for (auto edge : currNode->getGepOutEdges())
        {
            if (auto *gepEdge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge))
            {
                auto dstID = gepEdge->getDstID();
                auto &dstPts = pts[dstID];
                bool changed = false;

                for (auto val : currPts)
                {
                    auto gepObj = consg->getGepObjVar(val, gepEdge);
                    changed |= dstPts.insert(gepObj).second;
                }

                if (changed)
                    nodeQueue.push(dstID);
            }
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    for (const auto &siteInfo : consg->getIndirectCallsites())
    {
        auto *callNode = siteInfo.first;
        const auto calleePtrId = siteInfo.second;
        
        auto *caller = callNode->getCaller();
        const auto &candidateTargets = pts[calleePtrId];

        for (auto objId : candidateTargets)
        {
            if (consg->isFunction(objId))
            {
                auto *callee = consg->getFunction(objId);
                cg->addIndirectCallGraphEdge(callNode, caller, callee);
            }
        }
    }
}
