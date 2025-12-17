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
    // 定义工作列表 (WorkList)，用于存储需要处理的约束节点 ID
    WorkList<unsigned> nodeQueue;

    // =========================================================
    // 第一阶段：初始化指向集 (处理取地址约束)
    // =========================================================
    // 遍历约束图中的所有节点，寻找 "p = &x" 形式的初始约束
    for (const auto& nodePair : *consg)
    {
        auto nodeID = nodePair.first;
        auto* constraintNode = nodePair.second;

        // 处理入边的 Address Edge (由 &x 指向 p)
        for (auto* edge : constraintNode->getAddrInEdges())
        {
            if (auto* addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge))
            {
                auto srcVar = addrEdge->getSrcID(); // 被取地址的变量 (x)
                auto dstPtr = addrEdge->getDstID(); // 指针变量 (p)

                // 将 x 加入到 p 的指向集 pts(p) 中
                // insert 返回 pair，第二个元素表示是否插入了新元素
                if (pts[dstPtr].insert(srcVar).second) {
                    nodeQueue.push(dstPtr);
                }
            }
        }
    }

    // 辅助 Lambda 函数：检查两个节点之间是否已经存在 Copy 边
    // 用于防止重复添加相同的边，避免图变得无限大或浪费计算资源
    auto copyEdgeExists = [&](unsigned src, unsigned dst) -> bool {
        auto* srcNode = consg->getConstraintNode(src);
        for (auto* outEdge : srcNode->getCopyOutEdges()) {
            if (outEdge->getDstID() == dst) return true;
        }
        return false;
    };

    // =========================================================
    // 第二阶段：计算传递闭包 (Worklist 算法主循环)
    // =========================================================
    while (!nodeQueue.empty())
    {
        // 从队列中取出一个节点作为当前处理节点
        auto currID = nodeQueue.pop();
        auto* currNode = consg->getConstraintNode(currID);
        const auto& currentObjects = pts[currID]; // 获取当前节点的指向集引用

        // -----------------------------------------------------
        // 部分 A: 处理复杂约束 (Store 和 Load)
        // 核心思想：遍历当前指针指向的所有对象 obj
        // -----------------------------------------------------
        for (auto obj : currentObjects)
        {
            // 情况 1: 处理 Store 指令 (*currID = val)
            // 语义：将 val 的值存入 currID 指向的对象 obj 中
            // 动作：添加一条 Copy 边 (val -> obj)
            for (auto* edge : currNode->getStoreInEdges())
            {
                if (auto* storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge))
                {
                    auto val = storeEdge->getSrcID();
                    // 如果边不存在，则添加并激活源节点
                    if (!copyEdgeExists(val, obj)) {
                        consg->addCopyCGEdge(val, obj);
                        nodeQueue.push(val); // 重新处理 val，使其指向集流向 obj
                    }
                }
            }

            // 情况 2: 处理 Load 指令 (val = *currID)
            // 语义：从 currID 指向的对象 obj 中读取值赋给 val
            // 动作：添加一条 Copy 边 (obj -> val)
            for (auto* edge : currNode->getLoadOutEdges())
            {
                if (auto* loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge))
                {
                    auto val = loadEdge->getDstID();
                    // 如果边不存在，则添加并激活源节点
                    if (!copyEdgeExists(obj, val)) {
                        consg->addCopyCGEdge(obj, val);
                        nodeQueue.push(obj); // 重新处理 obj，使其指向集流向 val
                    }
                }
            }
        }

        // -----------------------------------------------------
        // 部分 B: 处理 Copy 约束 (指针赋值传播)
        // 语义：currID = y  =>  pts(currID) ⊆ pts(y)
        // -----------------------------------------------------
        for (auto* edge : currNode->getCopyOutEdges())
        {
            if (auto* copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge))
            {
                auto dstID = copyEdge->getDstID();
                size_t oldSize = pts[dstID].size();
                
                // 集合并集操作：pts(dst) U= pts(curr)
                pts[dstID].insert(currentObjects.begin(), currentObjects.end());

                // 如果目标节点的指向集变大了，说明信息更新了，加入队列继续处理
                if (pts[dstID].size() > oldSize) {
                    nodeQueue.push(dstID);
                }
            }
        }

        // -----------------------------------------------------
        // 部分 C: 处理 GEP 约束 (结构体/数组字段访问)
        // 语义：currID --GEP--> dst
        // -----------------------------------------------------
        for (auto* edge : currNode->getGepOutEdges())
        {
            if (auto* gepEdge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge))
            {
                auto dstID = gepEdge->getDstID();
                size_t oldSize = pts[dstID].size();

                // 对于 currID 指向的每个对象 obj，计算其字段偏移后的新对象
                for (auto obj : currentObjects) {
                    auto fieldObj = consg->getGepObjVar(obj, gepEdge);
                    pts[dstID].insert(fieldObj);
                }

                // 如果目标节点的指向集变化，加入队列
                if (pts[dstID].size() > oldSize) {
                    nodeQueue.push(dstID);
                }
            }
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    // 获取程序赋值图 (PAG) 和 过程间控制流图 (ICFG)
    auto* pag = consg->getPAG();
    auto* icfg = pag->getICFG();

    // 遍历 ICFG 中的所有节点，寻找间接调用 (Indirect Call)
    for (auto& iter : *icfg)
    {
        auto* node = iter.second;
        
        // 检查当前节点是否为调用节点 (CallICFGNode)
        if (auto* callNode = SVF::SVFUtil::dyn_cast<SVF::CallICFGNode>(node))
        {
            // 我们只关心间接调用 (例如函数指针调用)
            // 直接调用通常在构建 CallGraph 的初始阶段就已经处理了
            if (callNode->isIndirectCall())
            {
                // 1. 获取函数指针变量的 PAG 节点 ID
                // CallICFGNode 关联了一个 CallInstruction，我们需要获取它的 CalledOperand (函数指针)
                // 然后通过 PAG 将该 LLVM Value 映射为 PAG Node ID
                const llvm::CallBase* callInst = llvm::cast<llvm::CallBase>(callNode->getCallInst());
                const llvm::Value* funcPtrVal = callInst->getCalledOperand();
                SVF::NodeID ptrID = pag->getValueNode(funcPtrVal);

                // 2. 查询指针分析结果 (pts)，获取该函数指针可能指向的目标
                if (pts.find(ptrID) != pts.end())
                {
                    const auto& targets = pts[ptrID];
                    
                    // 3. 遍历每一个可能的目标对象
                    for (auto targetID : targets)
                    {
                        // 检查该目标对象是否确实是一个函数
                        if (const SVF::Function* calleeFunc = pag->getFunction(targetID))
                        {
                            // 4. 在调用图中添加边
                            // 边从 Caller (当前指令所属函数) 指向 Callee (被调用的函数)
                            // 注意：需要避免重复添加相同的边
                            SVF::NodeID callerID = callNode->getFun()->getId();
                            SVF::NodeID calleeID = calleeFunc->getId();

                            if (!cg->hasCallGraphEdge(callerID, calleeID)) {
                                cg->addCallGraphEdge(callerID, calleeID);
                            }
                        }
                    }
                }
            }
        }
    }
}
