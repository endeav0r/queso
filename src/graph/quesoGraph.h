#ifndef quesoGraph_HEADER
#define quesoGraph_HEADER

#include <cstdio>
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
                   Instruction * tail) {
            this->type = type;
            this->head = head;
            this->tail = tail;
        }
        QuesoEdge () {}

        ControlFlowType g_type () { return type; }

        GraphEdge * copy () const {
            printf("start quesoEdge copy\n");fflush(stdout);
            printf("head %p\n", head);fflush(stdout);
            printf("dynamic_cast<GraphEdge *>(head)\n");fflush(stdout);
            printf("%p\n", dynamic_cast<GraphEdge *>(head));fflush(stdout);
            printf("dynamic_cast<Instruction *>(head)\n");fflush(stdout);
            printf("%p\n", dynamic_cast<Instruction *>(head)); fflush(stdout);
            fflush(stdout);
            QuesoEdge * newQuesoEdge = new QuesoEdge(type,
                                 dynamic_cast<Instruction *>(head),
                                 dynamic_cast<Instruction *>(tail));
            printf("end copy\n");fflush(stdout);
            return newQuesoEdge;
        }

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