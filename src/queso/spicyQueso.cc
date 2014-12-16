#include "spicyQueso.h"

#include "queso/generic_instructions.h"
#include "machine/machine.h"

#include <algorithm>
#include <cstdio>
#include <iostream>
#include <map>
#include <queue>
#include <stack>
#include <set>
#include <string>
#include <vector>


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
                                                   Instruction * startIns,
                                                   std::map <uint64_t, std::set<std::string>> & vertex_operands_written,
                                                   std::map <uint64_t, std::list <Instruction *>> & vertex_predecessors) {
    std::set <uint64_t> touched;
    std::list <Operand *> operands;
    std::queue <Instruction *> queue;

    touched.insert(vId);

    if (vertex_operands_written[vId].count(operand->g_name()) > 0) {
        // the current ins is a special case
        std::list <Instruction *> & flattened = quesoGraph->g_vertex(vId)->flatten();
        std::list <Instruction *> :: reverse_iterator it;
        bool start = false;
        bool operand_found = false;
        for (it = flattened.rbegin(); it != flattened.rend(); it++) {
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
    }

    std::list <Instruction *> :: iterator pit;
    for (pit = vertex_predecessors[vId].begin(); pit != vertex_predecessors[vId].end(); pit++) {
        queue.push(*pit);
    }

    std::list <Instruction *> :: reverse_iterator it;
    while (queue.size() > 0) {
        while ((queue.size() > 0) && (touched.count(queue.front()->g_vIndex()) > 0)) {
            queue.pop();
        }

        if (queue.size() == 0)
            break;

        Instruction * instruction = queue.front();

        uint64_t vIndex = instruction->g_vIndex();

        touched.insert(vIndex);
        queue.pop();

        if (vertex_operands_written[vIndex].count(operand->g_name()) > 0) {
            bool operand_found = false;
            std::list <Instruction *> & flattened = instruction->flatten();
            for (it = flattened.rbegin(); it != flattened.rend(); it++) {
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
        }

        //std::list <Instruction *> :: iterator pit;
        for (pit = vertex_predecessors[vIndex].begin();
             pit != vertex_predecessors[vIndex].end();
             pit++) {
            queue.push(*pit);
        }
    }
    
    return operands;
}


void spicyQueso_ssa_zero (QuesoGraph * quesoGraph) {
    std::map <uint64_t, GraphVertex *> & vertices = quesoGraph->g_vertices();
    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = vertices.begin(); it != vertices.end(); it++) {
        Instruction * instruction = dynamic_cast<Instruction *>(it->second);
        std::list <Instruction *> & flattened = instruction->flatten();
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


void SpicyQueso :: ssa (QuesoGraph * quesoGraph) {
    std::stack <uint64_t> queue_multiple_predecessors;
    std::stack <uint64_t> queue;
    std::set   <uint64_t> queue_set;

    // this speeds up looking for operands in predecessor instructions a great
    // deal
    std::map <uint64_t, std::set<std::string>> vertex_operands_written;
    std::map <uint64_t, std::list <Instruction *>> vertex_predecessors;

    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = quesoGraph->g_vertices().begin(); it != quesoGraph->g_vertices().end(); it++) {
        Instruction * instruction = dynamic_cast<Instruction *>(it->second);
        std::list <Instruction *> & flattened = instruction->flatten();
        std::list <Instruction *> :: iterator iit;
        for (iit = flattened.begin(); iit != flattened.end(); iit++) {
            if ((*iit)->operand_written() != NULL)
                vertex_operands_written[it->first].insert((*iit)->operand_written()->g_name());
        }

        std::list <GraphEdge *> predecessor_edges = instruction->g_predecessors();
        std::list <Instruction *> predecessors;
        std::list <GraphEdge *> :: iterator git;
        for (git = predecessor_edges.begin(); git != predecessor_edges.end(); git++) {
            predecessors.push_back((Instruction *) (*git)->g_head());
        }

        vertex_predecessors[instruction->g_vIndex()] = predecessors;
    }


    std::map <std::string, uint64_t> ssa;

    spicyQueso_ssa_zero(quesoGraph);

    // add every vertex to the queue
    for (it = quesoGraph->g_vertices().begin(); it != quesoGraph->g_vertices().end(); it++) {
        if (it->second->g_predecessors().size() <= 1)
            queue.push(it->first);
    }

    while (true) {
        // if we have no more nodes to process
        if (queue.size() == 0) {
            if (queue_multiple_predecessors.size() == 0)
                break;
            // we set this to queue_multiple_predecessors and clear that queue
            queue = queue_multiple_predecessors;
            queue_multiple_predecessors = std::stack <uint64_t> ();
        }

        uint64_t vId = queue.top();
        queue.pop();
        queue_set.erase(vId);

        Instruction * instruction = quesoGraph->g_vertex(vId);
        if (instruction == NULL) {
            std::cerr << "null vertex SpicyQueso :: ssa vId=" << vId << std::endl;
            continue;
        }

        bool changed = false;

        std::map <std::string, uint64_t> localSsa;

        // flatten out the instruction
        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator it;
        for (it = flattened.begin(); it != flattened.end(); it++) {
            Instruction * flatIns = *it;

            // for each operand read
            std::list <Operand *> operands_read = flatIns->operands_read();
            std::list <Operand *> :: iterator it;
            for (it = operands_read.begin(); it != operands_read.end(); it++) {

                // check our local SSA cache for this variable
                if (    (localSsa.count((*it)->g_name()) > 0)
                     && (dynamic_cast<InstructionPhi *>(flatIns) == NULL)) {
                    (*it)->s_ssa(localSsa[(*it)->g_name()]);
                    continue;
                }

                // get a list of preceding values of this operand
                std::list <Operand *> preceding = spicyQueso_ssa_find_operand(quesoGraph,
                                                                              vId,
                                                                              *it,
                                                                              flatIns,
                                                                              vertex_operands_written,
                                                                              vertex_predecessors);

                // if no preceding, set ssa to 0
                if (preceding.size() == 0) {
                    if ((*it)->g_ssa() != 0)
                        changed = true;
                    (*it)->s_ssa(0);
                    localSsa[(*it)->g_name()] = 0;
                }

                // if 1 preceding operand, set ssa to that value
                else if (preceding.size() == 1) {
                    if ((*it)->g_ssa() != preceding.front()->g_ssa())
                        changed = true;
                    (*it)->s_ssa(preceding.front()->g_ssa());
                    localSsa[(*it)->g_name()] = preceding.front()->g_ssa();
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
                    phi->set_src(preceding);

                    // set localSsa
                    localSsa[(*it)->g_name()] = (*it)->g_ssa();

                    quesoGraph->absorbInstruction(phi);

                    // add it to our vertex_operands_written
                    vertex_operands_written[phi->g_vIndex()].insert(phi->operand_written()->g_name());

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
                        vertex_predecessors[phi->g_vIndex()].push_back((Instruction *) (*ppit)->g_head());
                        delete *ppit;
                    }

                    // point phi at this instruction
                    quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                         phi->g_vIndex(),
                                                         instruction->g_vIndex(),
                                                         CFT_NORMAL));

                    // phi is the predecessor for this instruction
                    vertex_predecessors[instruction->g_vIndex()].clear();
                    vertex_predecessors[instruction->g_vIndex()].push_back(phi);
                }
            }

            // operand written gets a new SSA
            Operand * operand = flatIns->operand_written();
            if ((operand != NULL) && (operand->g_ssa() == 0)) {
                changed = true;
                operand->s_ssa(spicyQueso_new_ssa(ssa, operand->g_name()));
                localSsa[operand->g_name()] = operand->g_ssa();
            }
        }

        // if something changed, we add children back to the queue
        if (true) {//changed) {
            std::list <GraphEdge *> successors = instruction->g_successors();
            std::list <GraphEdge *> :: iterator geit;
            for (geit = successors.begin(); geit != successors.end(); geit++) {
                QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*geit);
                uint64_t vIndex = quesoEdge->g_tail()->g_vIndex();
                if (queue_set.count(vIndex) == 0) {
                    //printf("adding %llx to queue\n", vIndex);
                    // add node to queue based on number of predecessors
                    if (quesoGraph->g_vertex(vIndex)->g_predecessors().size() > 1)
                        queue_multiple_predecessors.push(vIndex);
                    else
                        queue.push(vIndex);
                    queue_set.insert(vIndex);
                }
                //else
                    //printf("not adding %llx to queue\n", vIndex);
            }
        }
    }
}


void ssa2_blocks (QuesoGraph * quesoGraph,
                  std::map <std::string, uint64_t> & ssa) {

    std::map <uint64_t, GraphVertex *> :: iterator it;

    // for every block in the graph
    for (it  = quesoGraph->g_vertices().begin();
         it != quesoGraph->g_vertices().end();
         it++) {
        Instruction * instruction = (Instruction *) it->second;

        // ssa for this individual block
        std::map <std::string, uint64_t> block_ssa;

        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator iit;
        // for every instruction in this block
        for (iit = flattened.begin(); iit != flattened.end(); iit++) {
            Instruction * instruction = (Instruction *) (*iit);

            // set each read operand, if it has been set in this block
            std::list <Operand *> operands_read = instruction->operands_read();
            std::list <Operand *> :: iterator oit;
            for (oit = operands_read.begin(); oit != operands_read.end(); oit++) {
                Operand * operand = (Operand *) (*oit);

                if (operand->g_type() == CONSTANT)
                    continue;

                if (block_ssa.count(operand->g_name()) > 0) {
                    operand->s_ssa(block_ssa[operand->g_name()]);
                }
            }

            // set the write operand to a new ssa value
            Operand * operand = instruction->operand_written();
            if (operand == NULL)
                continue;

            if (ssa.count(operand->g_name()) == 0)
                ssa[operand->g_name()] = 1;
            else
                ssa[operand->g_name()] += 1;

            operand->s_ssa(ssa[operand->g_name()]);
            // and set the value for this block
            block_ssa[operand->g_name()] = ssa[operand->g_name()];
        }
    }
}


std::list <Operand *> ssa2_predecessor_get (Instruction * instruction,
                                            Operand * operand) {
    std::list <Operand *> result;
    std::set  <uint64_t> touched;

    std::queue <Instruction *> queue;

    touched.insert(instruction->g_vIndex());

    std::list <GraphEdge *> predecessors = instruction->g_predecessors();
    std::list <GraphEdge *> :: const_iterator it;
    for (it = predecessors.begin(); it != predecessors.end(); it++) {
        queue.push((Instruction *) (*it)->g_head());
    }

    while (queue.size() > 0) {
        Instruction * instruction = queue.front();
        queue.pop();

        bool operand_found = false;

        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: reverse_iterator rit;
        for (rit = flattened.rbegin(); rit != flattened.rend(); rit++) {
            Instruction * instruction = (*rit);

            Operand * operand_written = instruction->operand_written();

            if (operand_written == NULL)
                continue;

            if (operand_written->g_name() == operand->g_name()) {
                result.push_back(operand_written);
                operand_found = true;
                break;
            }
        }

        if (operand_found)
            continue;

        std::list <GraphEdge *> predecessors = instruction->g_predecessors();
        std::list <GraphEdge *> :: const_iterator it;
        for (it = predecessors.begin(); it != predecessors.end(); it++) {
            GraphEdge * graphEdge = (GraphEdge *) (*it);

            if (touched.count(graphEdge->g_head()->g_vIndex()) > 0)
                continue;

            touched.insert(graphEdge->g_head()->g_vIndex());
            queue.push((Instruction *) graphEdge->g_head());
        }
    }

    return result;
}


void ssa2_predecessors (QuesoGraph * quesoGraph,
                        std::map <std::string, uint64_t> & ssa) {
    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it  = quesoGraph->g_vertices().begin();
         it != quesoGraph->g_vertices().end();
         it++) {

        Instruction * instruction = (Instruction *) it->second;

        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator iit;
        for (iit = flattened.begin(); iit != flattened.end(); iit++) {

            Instruction * flatins = (Instruction *) (*iit);

            std::list <Operand *> operands_read = flatins->operands_read();
            std::list <Operand *> :: iterator oit;
            for (oit = operands_read.begin(); oit != operands_read.end(); oit++) {
                Operand * operand = (Operand *) (*oit);

                if (operand->g_type() == CONSTANT)
                    continue;

                if (operand->g_ssa() != 0)
                    continue;

                std::list <Operand *> operands = ssa2_predecessor_get(instruction, operand);

                if (operands.size() == 0)
                    continue;

                else if (operands.size() == 1)
                    operand->s_ssa(operands.front()->g_ssa());

                else {
                    Operand * tmp = operand->copy();
                    
                    if (ssa[operand->g_name()] == 0)
                        ssa[operand->g_name()] = 1;
                    else
                        ssa[operand->g_name()] += 1;

                    operand->s_ssa(ssa[operand->g_name()]);

                    tmp->s_ssa(ssa[operand->g_name()]);

                    InstructionPhi * phi = new InstructionPhi(tmp);

                    delete tmp;

                    std::list <Operand *> :: iterator oit;
                    phi->set_src(operands);

                    // add phi into the graph
                    quesoGraph->absorbInstruction(phi);

                    // add edges to phi, and delete original edge
                    std::list <GraphEdge *> predecessors = instruction->g_predecessors();
                    std::list <GraphEdge *> :: iterator git;
                    for (git = predecessors.begin(); git != predecessors.end(); git++) {
                        quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                             (*git)->g_head()->g_vIndex(),
                                                             phi->g_vIndex(),
                                                             CFT_NORMAL));
                        delete *git;
                    }

                    // add edge from phi to instruction
                    quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                         phi->g_vIndex(),
                                                         instruction->g_vIndex(),
                                                         CFT_NORMAL));
                }
            }
        }
    }
}


void SpicyQueso :: ssa2 (QuesoGraph * quesoGraph) {
    std::map <std::string, uint64_t> ssa;
    spicyQueso_ssa_zero(quesoGraph);
    ssa2_blocks(quesoGraph, ssa);
    ssa2_predecessors(quesoGraph, ssa);
}


void SpicyQueso :: blockize (QuesoGraph * quesoGraph) {
    bool blocked = true;

    std::set <uint64_t> to_remove;
    std::queue <Instruction *> to_delete;

    while (blocked) {
        blocked = false;

        std::map <uint64_t, GraphVertex *> :: iterator it;
        for (it = quesoGraph->g_vertices().begin();
             it != quesoGraph->g_vertices().end();
             it++) {

            if (to_remove.count(it->first) > 0)
                continue;

            Instruction * instruction = (Instruction *) it->second;
            
            std::list <GraphEdge *> successors = instruction->g_successors();

            // must have one and only one successor
            if (successors.size() != 1)
                continue;

            Instruction * successor = ((QuesoEdge *) successors.front())->g_tail();
            if (successor == NULL)
                continue;
            std::list <GraphEdge *> predecessors = successor->g_predecessors();

            // must have one and only one predecessor
            if (predecessors.size() != 1)
                continue;

            blocked = true;

            InstructionBlock * block;

            // if current instruction isn't a block, blockitize
            if ((block = dynamic_cast<InstructionBlock *>(instruction)) == NULL) {
                block = new InstructionBlock();

                block->push_depth_instruction(instruction);

                quesoGraph->absorbInstruction(block);

                // for each predecessor to this instruction
                std::list <GraphEdge *> predecessors = instruction->g_predecessors();
                std::list <GraphEdge *> :: iterator it;
                for (it = predecessors.begin(); it != predecessors.end(); it++) {
                    // point this predecessor to the block
                    quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                         (*it)->g_head()->g_vIndex(),
                                                         block->g_vIndex(),
                                                         CFT_NORMAL));
                    // delete this edge
                    delete *it;
                }

                to_remove.insert(instruction->g_vIndex());
                //quesoGraph->removeVertex(instruction->g_vIndex());
            }
            else
                // delete edge from instruction to successor
                delete block->g_successors().front();

            InstructionBlock * successorBlock = NULL;
            // if successor is an instructionblock
            if (successorBlock = dynamic_cast<InstructionBlock *>(successor)) {
                // we are going to insert all of these depth instructions into current block
                std::list <Instruction *> :: iterator it;
                for (it = successorBlock->g_depth_instructions().begin();
                     it != successorBlock->g_depth_instructions().end();
                     it++) {
                    block->push_depth_instruction((*it)->copy());
                }
            }
            else
                // insert successor into block
                block->push_depth_instruction(successor);

            // repoint all successors
            successors = successor->g_successors();
            std::list <GraphEdge *> :: iterator it;
            for (it = successors.begin(); it != successors.end(); it++) {
                quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                     block->g_vIndex(),
                                                     (*it)->g_tail()->g_vIndex(),
                                                     CFT_NORMAL));

                delete *it;
            }
            
            to_remove.insert(successor->g_vIndex());
            //quesoGraph->removeVertex(successor->g_vIndex());
            if (successorBlock != NULL) {
                to_remove.insert(successorBlock->g_vIndex());
                to_delete.push(successorBlock);
            }
        }

        std::set <uint64_t> :: iterator sit;
        for (sit = to_remove.begin(); sit != to_remove.end(); sit++) {
            quesoGraph->removeVertex(*sit);
        }

        to_remove.clear();

        while (to_delete.size() > 0) {
            delete to_delete.front();
            to_delete.pop();
        }
    }
}


// eliminates across blocks, except blocks with no successors
void SpicyQueso :: dead_code_elimination (QuesoGraph * quesoGraph) {
    std::set <std::string> vars_read;

    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = quesoGraph->g_vertices().begin();
         it != quesoGraph->g_vertices().end();
         it++) {
        Instruction * instruction = (Instruction *) it->second;

        bool noSuccessors = false;
        if (instruction->g_successors().size() == 0)
            noSuccessors = true;

        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator iit;
        for (iit = flattened.begin(); iit != flattened.end(); iit++) {

            // terminating vertices retain all operands
            std::list <Operand *> operands;
            if (noSuccessors)
                operands = (*iit)->operands();
            else
                operands = (*iit)->operands_read();
            std::list <Operand *> :: iterator oit;
            for (oit = operands.begin(); oit != operands.end(); oit++) {
                Operand * operand = *oit;
                if (operand->g_type() == CONSTANT)
                    continue;
                vars_read.insert(operand->queso());
            }
        }
    }


    for (it = quesoGraph->g_vertices().begin();
         it != quesoGraph->g_vertices().end();
         it++) {
        Instruction * instruction = (Instruction *) it->second;

        std::queue <Instruction *> to_delete;

        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator iit;
        for (iit = flattened.begin(); iit != flattened.end(); iit++) {
            Operand * operand_written = (*iit)->operand_written();
            if (operand_written == NULL)
                continue;

            if (vars_read.count(operand_written->queso()) == 0) {
                to_delete.push(*iit);
            }
        }

        while (to_delete.size() > 0) {
            // fix later, but will keep graph nodes from dying
            if (instruction->flatten().size() == 1) {
                to_delete.pop();
                continue;
            }
            instruction->remove_depth_instruction(to_delete.front());
            delete to_delete.front();
            to_delete.pop();
        }
    }
}


bool spicyQueso_replace_operand (Instruction * instruction,
                                 const std::string & needle,
                                 const Operand * newOperand) {
    bool result = false;
    if (InstructionAssign * assign = dynamic_cast<InstructionAssign *>(instruction)) {
        if (assign->g_src()->queso() == needle) {
            assign->s_src(newOperand);
            result = true;
        }
    }
    else if (InstructionStore * store = dynamic_cast<InstructionStore *>(instruction)) {
        if (store->g_address()->queso() == needle) {
            store->s_address(newOperand);
            result = true;
        }
        if (store->g_value()->queso() == needle) {
            store->s_value(newOperand);
            result = true;
        }
    }
    else if (InstructionLoad * load = dynamic_cast<InstructionLoad *>(instruction)) {
        if (load->g_address()->queso() == needle) {
            load->s_address(newOperand);
            result = true;
        }
    }
    else if (InstructionIte * ite = dynamic_cast<InstructionIte *>(instruction)) {
        if (ite->g_condition()->queso() == needle) {
            ite->s_condition(newOperand);
            result = true;
        }
        if (ite->g_t()->queso() == needle) {
            ite->s_t(newOperand);
            result = true;
        }
        if (ite->g_e()->queso() == needle) {
            ite->s_e(newOperand);
            result = true;
        }
    }
    else if (InstructionSignExtend * signExtend = dynamic_cast<InstructionSignExtend *>(instruction)) {
        if (signExtend->g_src()->queso() == needle) {
            signExtend->s_src(newOperand);
            result = true;
        }
    }
    else if (InstructionArithmetic * arithmetic = dynamic_cast<InstructionArithmetic *>(instruction)) {
        if (arithmetic->g_lhs()->queso() == needle) {
            arithmetic->s_lhs(newOperand);
            result = true;
        }
        if (arithmetic->g_rhs()->queso() == needle) {
            arithmetic->s_rhs(newOperand);
            result = true;
        }
    }
    else if (InstructionCmp * cmp = dynamic_cast<InstructionCmp *>(instruction)) {
        if (cmp->g_lhs()->queso() == needle) {
            cmp->s_lhs(newOperand);
            result = true;
        }
        if (cmp->g_rhs()->queso() == needle) {
            cmp->s_rhs(newOperand);
            result = true;
        }
    }
    else if (InstructionLoadLE32 * loadLE32 = dynamic_cast<InstructionLoadLE32 *>(instruction)) {
        if (loadLE32->g_address()->queso() == needle) {
            loadLE32->s_address(newOperand);
            result = true;
        }
    }
    else if (InstructionStoreLE32 * storeLE32 = dynamic_cast<InstructionStoreLE32 *>(instruction)) {
        if (storeLE32->g_address()->queso() == needle) {
            storeLE32->s_address(newOperand);
            result = true;
        }
        if (storeLE32->g_value()->queso() == needle) {
            storeLE32->s_value(newOperand);
            result = true;
        }
    }
    return result;
}


// creates a new quesoGraph with constants propagated
void SpicyQueso :: constant_fold_propagate (QuesoGraph * quesoGraph) {
    // a mapping from variables to their solved constant value
    // string is queso SSA
    std::map <std::string, Constant> solvedConstants;

    // when an operand is replaced as constant, it goes into the queue to
    // propagate out to other instructions
    // string is queso SSA
    std::queue <std::string> solvedQueue;

    // we keep track of which variables are sources to instructions in the
    // new graph
    std::map <std::string, std::list <Instruction *>> operandMap;

    // populate the initial solvedQueue
    std::map <uint64_t, GraphVertex *> :: iterator mit;
    for (mit = quesoGraph->g_vertices().begin();
         mit != quesoGraph->g_vertices().end();
         mit++) {
        Instruction * instruction = (Instruction *) mit->second;
        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator it;
        for (it = flattened.begin(); it != flattened.end(); it++) {
            Instruction * instruction = (Instruction *) *it;
            bool allConstants = true;

            std::list <Operand *> operands_read = instruction->operands_read();
            if (operands_read.size() == 0)
                allConstants = false;
            else {
                std::list <Operand *> :: iterator oit;
                for (oit = operands_read.begin(); oit != operands_read.end(); oit++) {
                    Operand * operand = *oit;
                    if (operand->g_type() == VARIABLE) {
                        allConstants = false;
                        operandMap[operand->queso()].push_back(instruction);
                    }
                    else if (operand->g_type() == ARRAY) {
                        allConstants = false;
                    }
                }
            }

            // if rhs is all constants, solve and set
            if (allConstants) {
                Operand * dst = instruction->operand_written();
                if (Variable * variable = dynamic_cast<Variable *>(dst)) {
                    Machine machine;
                    machine.concreteExecution(instruction);
                    MachineVariable mVar = machine.g_variable(variable->g_name());
                    solvedConstants[variable->queso()] = Constant(mVar.g_bits(), mVar.g_value());
                    solvedQueue.push(variable->queso());
                }
            }
        }
    }

    while (solvedQueue.size() > 0) {
        std::string solvedName = solvedQueue.front();
        solvedQueue.pop();

        std::list <Instruction *> :: iterator it;
        for (it = operandMap[solvedName].begin();
             it != operandMap[solvedName].end();
             it++) {

            if (! spicyQueso_replace_operand(*it, solvedName, &(solvedConstants[solvedName]))) {
                //printf(" [-] propagation failed\n");
                continue;
            }

            //printf(" [+] propagated to %s\n", (*it)->queso().c_str());

            // check if all operands are now constants
            bool allConstants = true;
            std::list <Operand *> operands_read = (*it)->operands_read();
            std::list <Operand *> :: iterator oit;
            for (oit = operands_read.begin(); oit != operands_read.end(); oit++) {
                if ((*oit)->g_type() != CONSTANT) {
                    allConstants = false;
                    break;
                }
            }

            if (allConstants) {
                if (Variable * variable = dynamic_cast<Variable *>((*it)->operand_written())) {
                    Machine machine;
                    machine.concreteExecution(*it);
                    MachineVariable mVar = machine.g_variable(variable->g_name());
                    solvedConstants[variable->queso()] = Constant(mVar.g_bits(), mVar.g_value());
                    solvedQueue.push(variable->queso());
                }
            }
        }
    }
}


void SpicyQueso :: replace_operand (QuesoGraph * quesoGraph,
                                    const Operand * needle,
                                    const Operand * newOperand) {
    std::string needleString = needle->queso();

    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = quesoGraph->g_vertices().begin(); it != quesoGraph->g_vertices().end(); it++) {
        Instruction * instruction = (Instruction *) it->second;
        std::list <Instruction *> flattened = instruction->flatten();
        std::list <Instruction *> :: iterator fit;
        for (fit = flattened.begin(); fit != flattened.end(); fit++) {
            Instruction * instruction = (Instruction *) *fit;

            spicyQueso_replace_operand(instruction, needleString, newOperand);
        }
    }
}


std::map <uint64_t, std::set <uint64_t>> SpicyQueso :: dominator_map (QuesoGraph * quesoGraph) {
    std::map <uint64_t, std::set <uint64_t>> dom_map;
    std::stack <uint64_t> stack;

    std::map <uint64_t, GraphVertex *> :: iterator mit;
    for (mit = quesoGraph->g_vertices().begin();
         mit != quesoGraph->g_vertices().end();
         mit++) {
        stack.push(mit->second->g_vIndex());

        while (stack.size() > 0) {
            uint64_t vIndex = stack.top();
            stack.pop();

            if (dom_map.count(vIndex) > 0)
                continue;

            std::list <GraphEdge *> predecessors = quesoGraph->g_vertex(vIndex)->g_predecessors();
            if (predecessors.size() == 0) {
                dom_map[vIndex] = std::set<uint64_t>();
                dom_map[vIndex].insert(vIndex);
                continue;
            }
            else if (    (predecessors.size() == 1)
                      && (predecessors.front()->g_head()->g_vIndex() == vIndex)) {
                dom_map[vIndex] = std::set<uint64_t>();
                dom_map[vIndex].insert(vIndex);
            }
            else if (    (predecessors.size() == 1)
                      && (dom_map.count(predecessors.front()->g_head()->g_vIndex()) > 0)) {
                dom_map[vIndex] = dom_map[predecessors.front()->g_head()->g_vIndex()];
                dom_map[vIndex].insert(vIndex);
                continue;
            }
            else {
                // check if all predecessor dominators are set
                // if not set, push them to be set
                bool predecessorsSet = true;
                std::list <GraphEdge *> :: iterator eit;
                for (eit = predecessors.begin(); eit != predecessors.end(); eit++) {
                    GraphEdge * graphEdge = *eit;
                    if (graphEdge->g_head()->g_vIndex() == vIndex)
                        continue;
                    if (dom_map.count(graphEdge->g_head()->g_vIndex()) == 0) {
                        if (predecessorsSet)
                            stack.push(vIndex);
                        stack.push(graphEdge->g_head()->g_vIndex());
                        predecessorsSet = false;
                    }
                }

                if (predecessorsSet == false)
                    continue;

                // all predecessor dominators are set
                // this vertex's dominators are itself, and the intersection of the
                // sets of dominators before it
                std::set <uint64_t> dominators(dom_map[predecessors.front()->g_head()->g_vIndex()]);
                for (eit = predecessors.begin(); eit != predecessors.end(); eit++) {
                    if ((*eit)->g_head()->g_vIndex() == vIndex)
                        continue;

                    std::set <uint64_t> predMap = dom_map[(*eit)->g_head()->g_vIndex()];

                    std::queue <uint64_t> removeQueue;
                    std::set <uint64_t> :: iterator it;
                    for (it = dominators.begin(); it != dominators.end(); it++) {
                        if (predMap.count(*it) == 0)
                            removeQueue.push(*it);
                    }

                    while (removeQueue.size() > 0) {
                        dominators.erase(removeQueue.front());
                        removeQueue.pop();
                    }
                }

                dom_map[vIndex] = dominators;
                dom_map[vIndex].insert(vIndex);
            }
        }
    }

    return dom_map;
}


// sets the immediate dominator of the top node to itself
// this is also a lazy and inefficient way of doing this
std::map <uint64_t, uint64_t> SpicyQueso :: idominator_map (QuesoGraph * quesoGraph,
                                 std::map <uint64_t, std::set <uint64_t>> & dom_map) {
    Graph * dominatorTree = new Graph();

    // create the dominatorTree
    std::map <uint64_t, GraphVertex *> :: iterator mit;
    for (mit = quesoGraph->g_vertices().begin();
         mit != quesoGraph->g_vertices().end();
         mit++) {
        dominatorTree->absorbVertex(new GraphVertex(), mit->first);
    }

    // begin by finding the top of the graph
    std::queue <uint64_t> domTreeQueue;

    for (mit = quesoGraph->g_vertices().begin();
         mit != quesoGraph->g_vertices().end();
         mit++) {
        std::list <GraphEdge *> predecessors = mit->second->g_predecessors();

        // vertices that point to themselves
        while (    (predecessors.size() > 0)
                && (predecessors.front()->g_head()->g_vIndex() == mit->first)) {
            predecessors.pop_front();
        }

        if (predecessors.size() == 0)
            continue;

        // add one, and only one, predecessor to tree-itize
        dominatorTree->absorbEdge(new GraphEdge(dominatorTree,
                                                predecessors.front()->g_head()->g_vIndex(),
                                                predecessors.front()->g_tail()->g_vIndex()));

        domTreeQueue.push(mit->first);
    }

    // for every vertex in domTreeQueue, we will walk upwards in the graph
    // until we find the first vertex which is a dominator of the given vertex
    while (domTreeQueue.size() > 0) {
        uint64_t vIndex = domTreeQueue.front();
        domTreeQueue.pop();

        GraphVertex * vertex = dominatorTree->g_vertex(vIndex);
        GraphVertex * nextVertex = vertex;
        while (true) {
            if (nextVertex->g_predecessors().size() == 0)
                break;
            uint64_t parentIndex = nextVertex->g_predecessors().front()->g_head()->g_vIndex();
            if (dom_map[vIndex].count(parentIndex) > 0) {
                // delete the original edge from this vertex to its direct predecessor
                delete vertex->g_predecessors().front();
                // insert a new edge from this parent to this vertex
                dominatorTree->absorbEdge(new GraphEdge(dominatorTree, parentIndex, vIndex));
                break;
            }
            else {
                nextVertex = dominatorTree->g_vertex(parentIndex);
            }
        }
    }

    // for every vertex in the dominatorTree, its immediate dominator is its parent
    std::map <uint64_t, uint64_t> idom_map;
    for (mit = dominatorTree->g_vertices().begin();
         mit != dominatorTree->g_vertices().end();
         mit++) {
        std::list <GraphEdge *> predecessors = mit->second->g_predecessors();
        if (predecessors.size() == 0)
            idom_map[mit->first] = mit->first;
        else
            idom_map[mit->first] = predecessors.front()->g_head()->g_vIndex();
    }

    delete dominatorTree;

    return idom_map;
}


std::map <uint64_t, std::set <uint64_t>> SpicyQueso :: predecessor_map (QuesoGraph * quesoGraph) {
    std::map <uint64_t, std::set <uint64_t>> pred_map;
    std::stack <uint64_t> stack;
    std::set <uint64_t> done;

    std::map <uint64_t, GraphVertex *> :: iterator mit;
    for (mit = quesoGraph->g_vertices().begin();
         mit != quesoGraph->g_vertices().end();
         mit++) {
        stack.push(mit->second->g_vIndex());

        while (stack.size() > 0) {
            uint64_t vIndex = stack.top();
            stack.pop();

            std::list <GraphEdge *> predecessors = quesoGraph->g_vertex(vIndex)->g_predecessors();

            if (predecessors.size() == 0) {
                pred_map[vIndex] = std::set <uint64_t> ();
                done.insert(vIndex);
                continue;
            }

            // check if all predecessors are set
            bool predecessorsSet = true;
            std::list <GraphEdge *> :: iterator it;
            for (it = predecessors.begin(); it != predecessors.end(); it++) {
                uint64_t predecessor_vIndex = (*it)->g_head()->g_vIndex();

                // if this vertex is a predecessor of itself
                if (predecessor_vIndex == vIndex)
                    continue;

                if (done.count(predecessor_vIndex) == 0) {
                    if (predecessorsSet == true)
                        stack.push(vIndex);
                    predecessorsSet = false;
                    stack.push(predecessor_vIndex);
                }
            }

            if (predecessorsSet == false)
                continue;

            //pred_map[vIndex] = std::set <uint64_t> ();

            for (it = predecessors.begin(); it != predecessors.end(); it++) {
                uint64_t predecessor_vIndex = (*it)->g_head()->g_vIndex();

                // if this vertex is a predecessor of itself
                if (predecessor_vIndex == vIndex) {
                    pred_map[vIndex].insert(vIndex);
                    continue;
                }

                pred_map[vIndex].insert(predecessor_vIndex);
                for (auto iit = pred_map[predecessor_vIndex].begin();
                     iit != pred_map[predecessor_vIndex].end();
                     iit++)
                    pred_map[vIndex].insert(*iit);
            }

            done.insert(vIndex);
        }
    }
    return pred_map;
}


template <class T>
std::set <T> set_intersection (std::set <T> & a, std::set <T> & b) {
    std::set <T> result;
    typename std::set <T> :: iterator it;
    for (it = a.begin(); it != a.end(); it++) {
        if (b.count(*it) > 0)
            result.insert(*it);
    }
    return result;
}


template <class T>
std::set <T> symmetric_difference (std::set <T> & a, std::set <T> & b) {
    std::set <T> result;
    typename std::set <T> :: iterator it;
    for (it = a.begin(); it != a.end(); it++) {
        if (b.count(*it) == 0)
            result.insert(*it);
    }
    for (it = b.begin(); it != b.end(); it++) {
        if (a.count(*it) == 0)
            result.insert(*it);
    }
    return result;
}


std::list <std::set <uint64_t>> enumerate_paths (Graph * graph,
                                                 uint64_t head,
                                                 uint64_t tail,
                     std::map <uint64_t, std::set <uint64_t>> & pred_map) {
    std::list <std::set <uint64_t>> result;
    if (head == tail) {
        std::set <uint64_t> tmp;
        tmp.insert(head);
        result.push_back(tmp);
        return result;
    }

    //printf("%lld -> %lld\n", head, tail);

    // get current vertex
    GraphVertex * vertex = graph->g_vertex(head);

    // get all successors
    std::list <GraphEdge *> successors = vertex->g_successors();
    std::list <GraphEdge *> :: iterator it;
    for (it = successors.begin(); it != successors.end(); it++) {
        // if this successor is not a predecessor of tail, continue
        uint64_t successor_vIndex = (*it)->g_tail()->g_vIndex();

        if (successor_vIndex == tail) {
            std::set <uint64_t> tmp;
            tmp.insert(head);
            result.push_back(tmp);
            continue;
        }

        if (pred_map[tail].count(successor_vIndex) == 0) {
            continue;
        }

        // successor is a predecessor of tail
        // get a list of all paths from this successor to tail
        std::list <std::set <uint64_t>> tmp = enumerate_paths(graph,
                                                              successor_vIndex,
                                                              tail,
                                                              pred_map);

        // for each of these paths
        std::list <std::set <uint64_t>> :: iterator tit;
        for (tit = tmp.begin(); tit != tmp.end(); tit++) {
            // add this vertex to the path
            (*tit).insert(head);
            // this this path to the result paths
            result.push_back(*tit);
        }
    }

    return result;
}


QuesoGraph * SpicyQueso :: shadowGraph (QuesoGraph * quesoGraph) {
    QuesoGraph * shadowGraph = new QuesoGraph();

    std::map <uint64_t, std::set <uint64_t>> dom_map  = dominator_map(quesoGraph);
    std::map <uint64_t, std::set <uint64_t>> pred_map = predecessor_map(quesoGraph);
    std::map <uint64_t, uint64_t> idom_map = idominator_map(quesoGraph, dom_map);

    std::map <uint64_t, GraphVertex *> ::iterator mit;
    // for every vertex in the graph
    for (mit = quesoGraph->g_vertices().begin();
         mit != quesoGraph->g_vertices().end();
         mit++) {
        Instruction * vertex = (Instruction *) mit->second;
        uint64_t vIndex = mit->first;

        // get all direct predecessors
        std::list <GraphEdge *> predecessors = vertex->g_predecessors();

        // create a set of all direct predecessors of vertex
        std::set <uint64_t> directPredecessors;
        std::list <GraphEdge *> :: iterator pit;
        for (pit = predecessors.begin(); pit != predecessors.end(); pit++) {
            directPredecessors.insert((*pit)->g_head()->g_vIndex());
        }

        // enumerate all paths from this vertex's idominator to it
        std::list <std::set <uint64_t>> paths = enumerate_paths(quesoGraph,
                                                                idom_map[vIndex],
                                                                vIndex,
                                                                pred_map);

        // create conjunctions of true variables based on directPredecessors
        std::set <std::set <uint64_t>> pathConjunctions;
        std::list <std::set <uint64_t>> :: iterator ppit;
        for (ppit = paths.begin(); ppit != paths.end(); ppit++) {
            pathConjunctions.insert(set_intersection(directPredecessors, *ppit));
        }

        // create the shadow instruction
        std::stringstream vertexName;
        vertexName << "v" << vIndex;
        Variable * dst = new Variable(1, vertexName.str());
        InstructionShadow * instructionShadow = new InstructionShadow(dst);
        delete dst;

        // create each of the conjunctions
        std::set <std::set <uint64_t>> :: iterator pCit;
        for (pCit = pathConjunctions.begin(); pCit != pathConjunctions.end(); pCit++) {
            std::set <uint64_t> trues = *pCit;
            std::set <OperandShadow *> conjunction;
            // for each of the direct predecessors
            std::set <uint64_t> :: iterator dit;
            for (dit = directPredecessors.begin(); dit != directPredecessors.end(); dit++) {
                std::stringstream operandName;
                operandName << "v" << (*dit);
                // add the direct predecessor based on its occurence in trues
                if (trues.count(*dit) == 1) {
                    conjunction.insert(new OperandShadow(operandName.str(), true));
                }
                else {
                    conjunction.insert(new OperandShadow(operandName.str(), false));
                }
            }
            instructionShadow->addConjunction(conjunction);
        }

        // add shadow instruction to the graph
        shadowGraph->absorbInstruction(instructionShadow, vIndex);
    }

    // add all the graph edges to shadow graph
    for (mit = quesoGraph->g_vertices().begin();
         mit != quesoGraph->g_vertices().end();
         mit++) {
        std::list <GraphEdge *> successors = mit->second->g_successors();
        std::list <GraphEdge *> :: iterator it;
        for (it = successors.begin(); it != successors.end(); it++) {
            GraphEdge * graphEdge = *it;
            shadowGraph->absorbEdge(new QuesoEdge(shadowGraph,
                                                  graphEdge->g_head()->g_vIndex(),
                                                  graphEdge->g_tail()->g_vIndex(),
                                                  CFT_NORMAL));
        }
    }

    return shadowGraph;
}