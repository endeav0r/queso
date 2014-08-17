#ifndef quesoGraph_HEADER
#define quesoGraph_HEADER

#include <inttypes.h>
#include "queso/queso.h"
#include "graph.h"

enum ControlFlowType {
    CFT_NORMAL,
    CFT_JUMP,
    CFT_JCC_TRUE,
    CFT_JCC_FALSE,
    CFT_CALL
};


class QuesoEdge : public GraphEdge {
    private :
        ControlFlowType type;
    public :
        QuesoEdge (ControlFlowType type,
                   Instruction * head,
                   Instruction * tail)
            : GraphEdge (head, tail), type (type) {}
        QuesoEdge () {}

        ControlFlowType g_type () { return type; }

        const Instruction * g_head () { return dynamic_cast<Instruction *>(head); }
        const Instruction * g_tail () { return dynamic_cast<Instruction *>(tail); }
};


class QuesoGraph : public Graph {
    public :
        const Instruction * absorbInstruction (Instruction * Instruction);
        const QuesoEdge *   absorbQuesoEdge   (QuesoEdge * quesoEdge);

        std::string dotGraph ();
};


#endif