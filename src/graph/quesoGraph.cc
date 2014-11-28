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


const Instruction * QuesoGraph :: absorbInstruction (Instruction * instruction,
                                                     uint64_t vIndex) {
    return dynamic_cast<const Instruction *>(absorbVertex(instruction, vIndex));
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
    return (Instruction *) Graph::g_vertex(vIndex);
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


class QuesoGraphSlice {
    public :
        Instruction * predecessor;
        Instruction * successor;
        QuesoGraphSlice (Instruction * predecessor, Instruction * successor)
            : predecessor (predecessor), successor (successor) {}
};


QuesoGraph * QuesoGraph :: slice_backward (Operand * operand) {
    Instruction * startInstruction = NULL;
    std::set <std::string> dominators;

    // first, let's find where this operand is set
    // for all instructions in the graph
    std::map <uint64_t, GraphVertex *> :: iterator graphIt;
    for (graphIt = g_vertices().begin(); graphIt != g_vertices().end(); graphIt++) {
        Instruction * instruction = dynamic_cast<Instruction *>(graphIt->second);

        // flatten the instruction
        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator it;
        for (it = flattened.begin(); it != flattened.end(); it++) {
            Instruction * ins = *it;

            if (ins->operand_written() == NULL) {
                continue;
            }

            // if this operand is set in this instruction
            if (    (operand->g_name() == ins->operand_written()->g_name())
                 && (operand->g_ssa() == ins->operand_written()->g_ssa())) {
                startInstruction = instruction;

                std::list <Operand *> operands_read = ins->operands_read();
                std::list <Operand *> :: iterator opIt;
                for (opIt = operands_read.begin(); opIt != operands_read.end(); opIt++) {
                    dominators.insert((*opIt)->queso());
                }
                dominators.insert(operand->queso());

                graphIt = g_vertices().end();
                graphIt--;
                break;
            }
        }
    }

    if (startInstruction == NULL)
        return NULL;

    QuesoGraph * quesoGraph = new QuesoGraph();

    // now we will construct a graph containing all instructions from predecessor
    std::set <Instruction *> touched;
    std::queue <QuesoGraphSlice> queue;

    queue.push(QuesoGraphSlice(startInstruction, NULL));

    while (queue.size() != 0) {
        QuesoGraphSlice & quesoGraphSlice = queue.front();
        Instruction * instruction = quesoGraphSlice.predecessor;
        Instruction * sliceSuccessor = quesoGraphSlice.successor;
        queue.pop();

        // important for cyclic graphs
        if (touched.count(instruction) > 0)
            continue;
        touched.insert(instruction);

        bool isDominatorInstruction = false;
        std::list <Instruction *> flattened = instruction->flatten();
        flattened.reverse();
        std::list <Instruction *> :: iterator fIt;
        for (fIt = flattened.begin(); fIt != flattened.end(); fIt++) {
            if ((*fIt)->operand_written() == NULL)
                continue;
            if (dominators.count((*fIt)->operand_written()->queso()) > 0) {
                isDominatorInstruction = true;

                std::list <Operand *> operands_read = (*fIt)->operands_read();
                std::list <Operand *> :: iterator opIt;
                for (opIt = operands_read.begin(); opIt != operands_read.end(); opIt++) {
                    dominators.insert((*opIt)->queso());
                }
            }
        }

        // if this was a dominator instruction, insert it into the graph
        if (isDominatorInstruction) {
            Instruction * newSuccessor = instruction->copy();
            quesoGraph->absorbInstruction(newSuccessor);

            if (sliceSuccessor != NULL)
                quesoGraph->absorbQuesoEdge(new QuesoEdge(quesoGraph,
                                                          newSuccessor->g_vIndex(),
                                                          sliceSuccessor->g_vIndex(),
                                                          CFT_NORMAL));
            sliceSuccessor = newSuccessor;
        }

        // insert predecessors for search
        std::list <GraphEdge *> predecessors = instruction->g_predecessors();
        std::list <GraphEdge *> :: iterator pIt;
        for (pIt = predecessors.begin(); pIt != predecessors.end(); pIt++) {
            QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*pIt);
            queue.push(QuesoGraphSlice(quesoEdge->g_head(), sliceSuccessor));
        }
    }

    return quesoGraph;
}


QuesoGraph * QuesoGraph :: slice_backward_thin (Operand * operand) {
    Instruction * startInstruction = NULL;
    std::set <std::string> dominators;

    // first, let's find where this operand is set
    std::map <uint64_t, GraphVertex *> :: iterator graphIt;
    for (graphIt = g_vertices().begin(); graphIt != g_vertices().end(); graphIt++) {
        Instruction * instruction = dynamic_cast<Instruction *>(graphIt->second);

        // flatten the instruction
        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator it;
        for (it = flattened.begin(); it != flattened.end(); it++) {
            Instruction * ins = *it;

            if (ins->operand_written() == NULL) {
                continue;
            }

            // if this operand is set in this instruction
            if (    (operand->g_name() == ins->operand_written()->g_name())
                 && (operand->g_ssa() == ins->operand_written()->g_ssa())) {
                startInstruction = instruction;

                std::list <Operand *> operands_read = ins->operands_read();
                std::list <Operand *> :: iterator opIt;
                for (opIt = operands_read.begin(); opIt != operands_read.end(); opIt++) {
                    dominators.insert((*opIt)->queso());
                }
                dominators.insert(operand->queso());

                graphIt = g_vertices().end();
                graphIt--;
                break;
            }
        }
    }

    if (startInstruction == NULL)
        return NULL;

    QuesoGraph * quesoGraph = new QuesoGraph();

    // now we will construct a graph containing all instructions from predecessor
    // instructions that contain dominators of this operand
    std::set <Instruction *> touched;
    std::queue <QuesoGraphSlice> queue;

    queue.push(QuesoGraphSlice(startInstruction, NULL));

    while (queue.size() != 0) {
        QuesoGraphSlice & quesoGraphSlice = queue.front();
        Instruction * instruction = quesoGraphSlice.predecessor;
        Instruction * sliceSuccessor = quesoGraphSlice.successor;
        queue.pop();

        // important for cyclic graphs
        if (touched.count(instruction) > 0)
            continue;
        touched.insert(instruction);

        std::list <Instruction *> flattened = instruction->flatten();
        flattened.reverse();
        std::list <Instruction *> :: iterator fIt;
        for (fIt = flattened.begin(); fIt != flattened.end(); fIt++) {
            Instruction * flatIns = *fIt;

            if (flatIns->operand_written() == NULL)
                continue;

            if (dominators.count(flatIns->operand_written()->queso()) > 0) {

                std::list <Operand *> operands_read = flatIns->operands_read();
                std::list <Operand *> :: iterator opIt;
                for (opIt = operands_read.begin(); opIt != operands_read.end(); opIt++) {
                    dominators.insert((*opIt)->queso());
                }

                Instruction * newSuccessor = flatIns->copy();
                quesoGraph->absorbInstruction(newSuccessor);
                if (sliceSuccessor != NULL) {
                    quesoGraph->absorbQuesoEdge(new QuesoEdge(quesoGraph,
                                                              newSuccessor->g_vIndex(),
                                                              sliceSuccessor->g_vIndex(),
                                                              CFT_NORMAL));
                }
                sliceSuccessor = newSuccessor;
            }
        }

        // insert predecessors for search
        std::list <GraphEdge *> predecessors = instruction->g_predecessors();
        std::list <GraphEdge *> :: iterator pIt;
        for (pIt = predecessors.begin(); pIt != predecessors.end(); pIt++) {
            QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*pIt);
            queue.push(QuesoGraphSlice(quesoEdge->g_head(), sliceSuccessor));
        }
    }

    return quesoGraph;
}


json_t * QuesoGraph :: json () const {
    json_t * json = json_object();

    char tmp[64];
    
    json_t * instructions = json_object();
    json_t * json_edges   = json_array();

    std::map <uint64_t, GraphVertex *> :: const_iterator it;
    for (it = vertices.begin(); it != vertices.end(); it++) {
        Instruction * instruction = (Instruction *) it->second;

        snprintf(tmp, sizeof(tmp), "%llx", it->first);
        json_object_set(instructions, tmp, instruction->json());

        std::list <GraphEdge *> :: const_iterator eit;
        for (eit = instruction->g_edges().begin();
             eit != instruction->g_edges().end();
             eit++) {

            GraphEdge * edge = *eit;
            if (edge->g_head()->g_vIndex() == instruction->g_vIndex()) {
                json_t * json_edge = json_array();
                snprintf(tmp, sizeof(tmp), "%llx", edge->g_head()->g_vIndex());
                json_array_append(json_edge, json_string(tmp));
                snprintf(tmp, sizeof(tmp), "%llx", edge->g_tail()->g_vIndex());
                json_array_append(json_edge, json_string(tmp));
                json_array_append(json_edges, json_edge);
            }
        }
    }

    json_object_set(json, "instructions", instructions);
    json_object_set(json, "edges", json_edges);

    return json;
}