#include "quesoGraph.h"

#include <cstdio>
#include <iostream>
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
    snprintf(tmp, 64, "%lld", (unsigned long long) instruction);
    return tmp;
}

void subQuesoText (std::stringstream & ss, const Instruction * instruction, unsigned int depth) {
    std::string spacers;
    for (unsigned int i = 0; i < depth; i++)
        spacers = spacers + " ";
    ss << "\\l" << spacers << instruction->queso();
    std::list <Instruction *> :: const_iterator it;
    for (it = instruction->g_depth_instructions().begin();
         it != instruction->g_depth_instructions().end();
         it++)
        subQuesoText(ss, *it, depth + 2);
}

std::string QuesoGraph :: dotGraph () {
    std::stringstream ss;
    
    std::map <uint64_t, GraphVertex *> :: iterator it;

    ss << "digraph G {" << std::endl;

    for (it = vertices.begin(); it != vertices.end(); it++) {
        const Instruction * instruction = dynamic_cast<Instruction *>(it->second);
        // draw this vertex
        ss << instructionDotName(instruction) << " [label=\"";
        subQuesoText(ss, instruction, 0);
        ss << "\", shape=box];" << std::endl;

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