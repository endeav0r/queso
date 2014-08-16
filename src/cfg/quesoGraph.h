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


class QuesoVertex : public Instruction, public GraphVertex {
};


class QuesoEdge : public GraphEdge {
    private :
        ControlFlowType type;
    public :
        QuesoEdge (ControlFlowType type,
                   QuesoVertex * head,
                   QuesoVertex * tail)
            : GraphEdge (head, tail), type (type) {}
        QuesoEdge () {}

        ControlFlowType g_type () { return type; }
};


class QuesoCfg {
    private :
        Graph cfg;
    public :
        const QuesoVertex * absorbQuesoVertex (QuesoVertex * quesoVertex);
        const QuesoEdge *   absorbQuesoEdge   (QuesoEdge * quesoEdge);

        std::string dotGraph (const QuesoVertex * quesoVertex);
};


#endif