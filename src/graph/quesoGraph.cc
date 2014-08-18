#include "quesoGraph.h"

#include <cstdio>
#include <queue>
#include <sstream>
#include <unordered_set>

const Instruction * QuesoGraph :: absorbInstruction (Instruction * instruction) {
    return dynamic_cast<const Instruction *>(absorbVertex(instruction));
}


const QuesoEdge * QuesoGraph :: absorbQuesoEdge (QuesoEdge * quesoEdge) {
    return dynamic_cast<const QuesoEdge *>(absorbEdge(quesoEdge));
}


std::string instructionDotName (const Instruction * instruction) {
    char tmp[64];
    snprintf(tmp, 64, "%p", instruction);
    return tmp;
}


std::string QuesoGraph :: dotGraph () {
    std::stringstream ss;
    
    std::map <const GraphVertex *, GraphVertex *> :: iterator it;

    ss << "digraph G {" << std::endl;

    for (it = vertices.begin(); it != vertices.end(); it++) {
        const Instruction * instruction = dynamic_cast<Instruction *>(it->second);

        // draw this vertex
        ss << instructionDotName(instruction) << " [label=\""
           << instruction->queso() << "\"];" << std::endl;

        std::list <GraphEdge *> :: const_iterator it;
        const std::list <GraphEdge *> successors = instruction->g_successors();
        for (it = successors.begin(); it != successors.end(); it++) {
            QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*it);
            const Instruction * head = quesoEdge->g_head();
            const Instruction * tail = quesoEdge->g_tail();


            ss << instructionDotName(head) << " -> " << instructionDotName(tail)
               << ";" << std::endl;
        }
    }

    ss << "}";
    return ss.str();
}