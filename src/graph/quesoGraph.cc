#include "quesoGraph.h"

#include <cstdio>
#include <iostream>
#include <queue>
#include <set>
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

void subQuesoText (std::stringstream & ss, Instruction * instruction, unsigned int depth) {
    std::string spacers;
    for (unsigned int i = 0; i < depth; i++)
        spacers = spacers + " ";
    ss << "\\l" << spacers << instruction->queso();
    std::list <Instruction *> :: iterator it;
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
        Instruction * instruction = dynamic_cast<Instruction *>(it->second);
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


Instruction * QuesoGraph :: g_vertex (uint64_t vIndex) {
    return dynamic_cast<Instruction *>(Graph::g_vertex(vIndex));
}


void QuesoGraph_smtlib2Declarations (std::set <std::string> & declarations,
                                     Instruction * instruction) {
    std::list <Operand *> operands = instruction->operands();
    std::list <Operand *> :: iterator it;
    for (it = operands.begin(); it != operands.end(); it++) {
        if (Variable * variable = dynamic_cast<Variable *>(*it)) {
            declarations.insert(variable->smtlib2_declaration());
        }
        else if (Array * array = dynamic_cast<Array *>(*it)) {
            declarations.insert(array->smtlib2_declaration());
        }
    }

    std::list <Instruction *> :: iterator iit;
    for (iit = instruction->g_depth_instructions().begin();
         iit != instruction->g_depth_instructions().end();
         iit++) {
        QuesoGraph_smtlib2Declarations(declarations, *iit);
    }
}


std::string QuesoGraph :: smtlib2Declarations () {
    std::stringstream ss;
    std::set <std::string> declarations;

    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = g_vertices().begin(); it != g_vertices().end(); it++) {
        Instruction * instruction = dynamic_cast<Instruction *>(it->second);
        QuesoGraph_smtlib2Declarations(declarations, instruction);
    }

    std::set <std::string> :: iterator dit;
    for (dit = declarations.begin(); dit != declarations.end(); dit++) {
        ss << *dit << std::endl;
    }

    return ss.str();
}


std::string QuesoGraph :: smtlib2 () {
    std::stringstream ss;

    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = g_vertices().begin(); it != g_vertices().end(); it++) {
        Instruction * instruction = dynamic_cast<Instruction *>(it->second);
        ss << instruction->depthSmtlib2();
    }

    return ss.str();
}