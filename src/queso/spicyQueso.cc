#include "spicyQueso.h"

#include <cstdio>
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


class SQSSAGraph {
    public :
        Instruction * instruction;
        std::map <std::string, uint64_t> variableCounts;
        std::map <std::string, uint64_t> & writeCounts;

        SQSSAGraph (Instruction * instruction,
                    const std::map <std::string, uint64_t> & variableCounts,
                    std::map <std::string, uint64_t> & writeCounts)
            : instruction (instruction),
              variableCounts (variableCounts),
              writeCounts (writeCounts) {}
        SQSSAGraph (Instruction * instruction,
                    std::map <std::string, uint64_t> & writeCounts)
            : instruction (instruction),
              writeCounts (writeCounts) {}

        void ssa (Instruction * instruction) {
            std::list <Operand *> operands = instruction->operands();
            std::list <Operand *> :: iterator it;
            for (it = operands.begin(); it != operands.end(); it++) {
                if (Variable * variable = dynamic_cast<Variable *>(*it)) {
                    // if this variable exists in variableCounts, use that
                    if (variableCounts.count(variable->g_name()))
                        variable->s_ssa(variableCounts[variable->g_name()]);
                    // if it doesn't, check if it exists in writeCounts
                    else if (writeCounts.count(variable->g_name())) {
                        // it exists. increment writeCount for this variable and use that ssa
                        writeCounts[variable->g_name()] += 1;
                        variableCounts[variable->g_name()] = writeCounts[variable->g_name()];
                        variable->s_ssa(variableCounts[variable->g_name()]);
                    }
                    // it doesn't exist, create it, use that ssa
                    else {
                        writeCounts[variable->g_name()] = 0;
                        variableCounts[variable->g_name()] = 0;
                        variable->s_ssa(0);
                    }
                }
                else if (Array * array = dynamic_cast<Array *>(*it)) {
                    if (variableCounts.count(array->g_name()))
                        array->s_ssa(variableCounts[array->g_name()]);
                    else if (writeCounts.count(array->g_name())) {
                        writeCounts[array->g_name()] += 1;
                        variableCounts[array->g_name()] = writeCounts[array->g_name()];
                        array->s_ssa(variableCounts[array->g_name()]);
                    }
                    else {
                        writeCounts[array->g_name()] = 0;
                        variableCounts[array->g_name()] = 0;
                        array->s_ssa(0);
                    }
                }
            }

            Operand * dst = instruction->operand_written();

            if (Variable * variable = dynamic_cast<Variable *>(dst)) {
                if (writeCounts.count(variable->g_name()) == 0) {
                    writeCounts[variable->g_name()] = 0;
                    variableCounts[variable->g_name()] = 0;
                }
                else {
                    writeCounts[variable->g_name()] += 1;
                    variableCounts[variable->g_name()] = writeCounts[variable->g_name()];
                }
                variable->s_ssa(variableCounts[variable->g_name()]);
            }
            else if (Array * array = dynamic_cast<Array *>(dst)) {
                if (variableCounts.count(array->g_name()) == 0) {
                    writeCounts[array->g_name()] = 0;
                    variableCounts[array->g_name()] = 0;
                }
                else {
                    writeCounts[array->g_name()] += 1;
                    variableCounts[array->g_name()] += writeCounts[array->g_name()];
                }
                array->s_ssa(variableCounts[array->g_name()]);
            }

            std::list <Instruction *> :: iterator iit;
            for (iit = instruction->g_depth_instructions().begin();
                 iit != instruction->g_depth_instructions().end();
                 iit++) {
                ssa(*iit);
            }
        }

        void ssa () {
            ssa(instruction);
        }
};


void SpicyQueso :: ssa (QuesoGraph * quesoGraph, uint64_t entry_vId) {
    std::map   <std::string, uint64_t> writeCounts;
    std::set   <uint64_t>   touched;
    std::queue <SQSSAGraph> queue;

    touched.insert(entry_vId);
    queue.push(SQSSAGraph(quesoGraph->g_vertex(entry_vId), writeCounts));

    // initial pass
    while (queue.size() > 0) {
        SQSSAGraph & sqssaGraph = queue.front();

        /*
        printf("SpicyQueso::ssa loop %x %llx %s\n",
               sqssaGraph.instruction->g_vIndex(),
               (unsigned long long) sqssaGraph.instruction->g_pc(),
               sqssaGraph.instruction->queso().c_str());
        */

        sqssaGraph.ssa();

        std::list <GraphEdge *> successors = sqssaGraph.instruction->g_successors();
        std::list <GraphEdge *> :: iterator it;
        for (it = successors.begin(); it != successors.end(); it++) {
            QuesoEdge * quesoEdge = dynamic_cast<QuesoEdge *>(*it);
            Instruction * tail = quesoEdge->g_tail();

            if (touched.count(tail->g_vIndex()) == 0) {
                touched.insert(tail->g_vIndex());
                queue.push(SQSSAGraph(tail, sqssaGraph.variableCounts, writeCounts));
            }
        }

        queue.pop();
    }
}