#include "spicyQueso.h"

#include "queso/generic_instructions.h"

#include <cstdio>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <string>


void SpicyQueso_ssa_assign_read (std::map <std::string, uint64_t> & variableCounts,
                                 Instruction * instruction) {
    std::list <Operand *> :: iterator it;
    std::list <Operand *> operands_read = instruction->operands_read();
    for (it = operands_read.begin(); it != operands_read.end(); it++) {
        if (Variable * variable = dynamic_cast<Variable *>(*it)) {
            if (variableCounts.count(variable->g_name()) == 0)
                variableCounts[variable->g_name()] = 0;
            variable->s_ssa(variableCounts[variable->g_name()]);
        }
        else if (Array * array = dynamic_cast<Array *>(*it)) {
            if (variableCounts.count(array->g_name()) == 0)
                variableCounts[array->g_name()] = 0;
            array->s_ssa(variableCounts[array->g_name()]);
        }
    }
}


void SpicyQueso_ssa_assign_written (std::map <std::string, uint64_t> & variableCounts,
                                    Instruction * instruction) {
    Operand * dst = instruction->operand_written();

    if (Variable * variable = dynamic_cast<Variable *>(dst)) {
        if (variableCounts.count(variable->g_name()) == 0)
            variableCounts[variable->g_name()] = 0;
        else
            variableCounts[variable->g_name()] += 1;
        variable->s_ssa(variableCounts[variable->g_name()]);
    }
    else if (Array * array = dynamic_cast<Array *>(dst)) {
        if (variableCounts.count(array->g_name()) == 0)
            variableCounts[array->g_name()] = 0;
        else
            variableCounts[array->g_name()] += 1;
        array->s_ssa(variableCounts[array->g_name()]);
    }

}


void SpicyQueso_ssa (std::map <std::string, uint64_t> & variableCounts,
                     Instruction * instruction) {

    SpicyQueso_ssa_assign_read(variableCounts, instruction);
    SpicyQueso_ssa_assign_written(variableCounts, instruction);

    std::list <Instruction *> ::iterator iit;
    for (iit = instruction->g_depth_instructions().begin();
         iit != instruction->g_depth_instructions().end();
         iit++) {
        SpicyQueso_ssa(variableCounts, *iit);
    }
}


void SpicyQueso :: ssa (std::list <Instruction *> & instructions) {
    std::map <std::string, uint64_t> variableCounts;

    std::list <Instruction *> :: iterator it;
    for (it = instructions.begin(); it != instructions.end(); it++)
        SpicyQueso_ssa(variableCounts, *it);
}


// searches predecessor instructions for instances of given operand
std::list <Operand *> spicyQueso_ssa_find_operand (QuesoGraph * quesoGraph,
                                                   uint64_t vId,
                                                   Operand * operand,
                                                   Instruction * startIns) {
    std::set <uint64_t> touched;
    std::list <Operand *> operands;
    std::queue <uint64_t> queue;

    touched.insert(vId);

    // the current ins is a special case
    std::list <Instruction *> flattened = quesoGraph->g_vertex(vId)->flatten();
    flattened.reverse();
    std::list <Instruction *> :: iterator it;
    bool start = false;
    bool operand_found = false;
    for (it = flattened.begin(); it != flattened.end(); it++) {
        if (*it == startIns) {
            start = true;
            continue;
        }
        else if (not start)
            continue;

        Instruction * instruction = *it;
        if (    (instruction->operand_written() != NULL)
             && (instruction->operand_written()->g_name() == operand->g_name())) {
            operands.push_back(instruction->operand_written());
            operand_found = true;
            break;
        }
    }

    if (operand_found)
        return operands;

    std::list <GraphEdge *> predecessors = quesoGraph->g_vertex(vId)->g_predecessors();
    std::list <GraphEdge *> :: iterator geit;
    for (geit = predecessors.begin(); geit != predecessors.end(); geit++) {
        QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*geit);
        queue.push(quesoEdge->g_head()->g_vIndex());
    }


//    touched.insert(vId);

    //printf("spicyQueso_ssa_find_operand 1\n");fflush(stdout);
    //queue.push(vId);
    // populate initial queue
    /*
    Instruction * instruction = quesoGraph->g_vertex(vId);
    std::list <GraphEdge *> predecessors = instruction->g_predecessors();
    std::list <GraphEdge *> :: iterator geit;
    for (geit = predecessors.begin(); geit != predecessors.end(); geit++) {
        QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*geit);
        queue.push(quesoEdge->g_head()->g_vIndex());
    }
    */

    //printf("spicyQueso_ssa_find_operand 2\n");fflush(stdout);

    while (queue.size() > 0) {
        while ((queue.size() > 0) && (touched.count(queue.front()) > 0)) {
            queue.pop();
        }

        if (queue.size() == 0)
            break;

        touched.insert(queue.front());
        Instruction * instruction = quesoGraph->g_vertex(queue.front());
        queue.pop();

        bool operand_found = false;
        std::list <Instruction *> flattened = instruction->flatten();
        flattened.reverse();

        //printf("spicyQueso_ssa_find_operand 5\n");fflush(stdout);

        std::list <Instruction *> :: iterator it;
        for (it = flattened.begin(); it != flattened.end(); it++) {
            Instruction * instruction = *it;
            if (    (instruction->operand_written() != NULL)
                 && (instruction->operand_written()->g_name() == operand->g_name())) {
                operands.push_back(instruction->operand_written());
                operand_found = true;
                break;
            }
        }

        if (operand_found)
            continue;

        std::list <GraphEdge *> predecessors = instruction->g_predecessors();
        std::list <GraphEdge *> :: iterator geit;
        for (geit = predecessors.begin(); geit != predecessors.end(); geit++) {
            QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*geit);
            queue.push(quesoEdge->g_head()->g_vIndex());
        }
    }

    //printf("spicyQueso_ssa_find_operand 3\n");fflush(stdout);
    
    return operands;
}


void spicyQueso_ssa_zero (QuesoGraph * quesoGraph) {
    std::map <uint64_t, GraphVertex *> & vertices = quesoGraph->g_vertices();
    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = vertices.begin(); it != vertices.end(); it++) {
        Instruction * instruction = dynamic_cast<Instruction *>(it->second);
        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator fit;
        for (fit = flattened.begin(); fit != flattened.end(); fit++) {
            std::list <Operand *> operands = (*fit)->operands();
            std::list <Operand *> :: iterator oit;
            for (oit = operands.begin(); oit != operands.end(); oit++) {
                (*oit)->s_ssa(0);
            }
        }
    }
}


uint64_t spicyQueso_new_ssa (std::map <std::string, uint64_t> & ssa, std::string name) {
    if (ssa.count(name) == 0)
        ssa[name] = 0;
    ssa[name]++;
    return ssa[name];
}


void SpicyQueso :: ssa (QuesoGraph * quesoGraph, uint64_t entry_vId) {
    std::queue <uint64_t> queue;

    std::map <std::string, uint64_t> ssa;

    spicyQueso_ssa_zero(quesoGraph);

    queue.push(entry_vId);

    while (queue.size() > 0) {
        uint64_t vId = queue.front();
        queue.pop();

        Instruction * instruction = quesoGraph->g_vertex(vId);
        if (instruction == NULL) {
            std::cerr << "null vertex SpicyQueso :: ssa vId=" << vId << std::endl;
            continue;
        }

        bool changed = false;

        // flatten out the instruction
        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator it;
        for (it = flattened.begin(); it != flattened.end(); it++) {
            Instruction * flatIns = *it;

            // for each operand read
            std::list <Operand *> operands_read = flatIns->operands_read();
            std::list <Operand *> :: iterator it;
            for (it = operands_read.begin(); it != operands_read.end(); it++) {
                // get a list of preceding values of this operand
                std::list <Operand *> preceding = spicyQueso_ssa_find_operand(quesoGraph, vId, *it, flatIns);

                // if no preceding, set ssa to 0
                if (preceding.size() == 0) {
                    if ((*it)->g_ssa() != 0)
                        changed = true;
                    (*it)->s_ssa(0);
                }

                // if 1 preceding operand, set ssa to that value
                else if (preceding.size() == 1) {
                    if ((*it)->g_ssa() != preceding.front()->g_ssa())
                        changed = true;
                    (*it)->s_ssa(preceding.front()->g_ssa());
                }

                // if >1 preceding operands... PHI TIME!
                else {
                    // phi is always true for changed, because fuck trying to figure
                    // that noise out
                    changed = true;

                    // if this is a phi instruction, we just update src values
                    if (InstructionPhi * phi = dynamic_cast<InstructionPhi *>(flatIns)) {
                        phi->set_src(preceding);
                        // and we're done with this instruction
                        break;
                    }
                    // create a phi instruction
                    (*it)->s_ssa(spicyQueso_new_ssa(ssa, (*it)->g_name()));
                    InstructionPhi * phi = new InstructionPhi(*it);
                    std::list <Operand *> :: iterator pit;
                    for (pit = preceding.begin(); pit != preceding.end(); pit++) {
                        phi->add_src(*pit);
                    }

                    quesoGraph->absorbInstruction(phi);

                    // get a list of all predecessors to this vertex
                    std::list <GraphEdge *> predecessors = instruction->g_predecessors();

                    // point all predecessors to phi, then remove edge from predecessor
                    // to this instruction
                    std::list <GraphEdge *> :: iterator ppit;
                    for (ppit = predecessors.begin(); ppit != predecessors.end(); ppit++) {
                        quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                             (*ppit)->g_head()->g_vIndex(),
                                                             phi->g_vIndex(),
                                                             CFT_NORMAL));
                        delete *ppit;
                    }

                    // point phi at this instruction
                    quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                         phi->g_vIndex(),
                                                         instruction->g_vIndex(),
                                                         CFT_NORMAL));
                }
            }

            // operand written gets a new SSA
            Operand * operand = flatIns->operand_written();
            if ((operand != NULL) && (operand->g_ssa() == 0)) {
                changed = true;
                operand->s_ssa(spicyQueso_new_ssa(ssa, operand->g_name()));
            }
        }

        if (true) {//(changed) {
            std::list <GraphEdge *> successors = instruction->g_successors();
            std::list <GraphEdge *> :: iterator geit;
            for (geit = successors.begin(); geit != successors.end(); geit++) {
                QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*geit);
                queue.push(quesoEdge->g_tail()->g_vIndex());
            }
        }
    }
}