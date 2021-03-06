#ifndef quesoGraph_HEADER
#define quesoGraph_HEADER

#include <cstdio>
#include <inttypes.h>
#include <memory>

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
        QuesoEdge (Graph * graph,
                   uint64_t head,
                   uint64_t tail,
                   ControlFlowType type) {
            this->graph = graph;
            this->head = head;
            this->tail = tail;
            this->type = type;
        }
        
        QuesoEdge () {}

        ControlFlowType g_type () { return type; }

        Instruction * g_head () { return (Instruction *) graph->g_vertex(head); }
        Instruction * g_tail () { return (Instruction *) graph->g_vertex(tail); }
};


class QuesoGraph : public Graph {
    public :
        const Instruction * absorbInstruction (Instruction * Instruction);
        const Instruction * absorbInstruction (Instruction * Instruction, uint64_t vIndex);
        const QuesoEdge *   absorbQuesoEdge   (QuesoEdge * quesoEdge);

        std::string dotGraph ();
        std::string dotGraphVIndex ();

        Instruction * g_vertex (uint64_t vIndex);

        std::string smtlib2Declarations ();
        std::string smtlib2 ();

        // returns NULL if operand could not be found by name & SSA
        QuesoGraph * slice_backward (Operand * operand);

        // same as slice_backward, but only returns minimum instructions necessary
        QuesoGraph * slice_backward_thin (Operand * operand);

        json_t * json () const;
};


#endif