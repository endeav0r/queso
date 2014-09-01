#include "spicyQueso.h"

#include <string>
#include <map>

void SpicyQueso_ssa (std::map <std::string, uint64_t> & variableCounts,
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
            array->s_ssa(variableCounts[variable->g_name()]);
        }
    }

    Operand * dst = instruction->operand_written();

    if (Variable * variable = dynamic_cast<Variable *>(dst)) {
        if (variableCounts.count(variable->g_name()) == 0)
            variableCounts[variable->g_name()] = 0;
        else
            variableCounts[variable->g_name()] += 1;
        variable->s_ssa(variableCounts[variable->g_name()]);
    }
    else if (Array * array = dynamic_cast<Array *>(dst)) {
        if (variableCounts.count(variable->g_name()) == 0)
            variableCounts[variable->g_name()] = 0;
        else
            variableCounts[variable->g_name()] += 1;
        variable->s_ssa(variableCounts[variable->g_name()]);
    }


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