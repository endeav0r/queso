#include "x86Disassembler.h"

#include "machine/machine.h"

#include <iostream>
#include <queue>
#include <set>
#include <unordered_set>

/*
 * To determine successor instructions, we
 * 1) grab all sub instructions of this instruction which influence our instruction pointer
 * 2) evaluate these in a machine
 * 3) if we encounter a load instruction, we stop
 * 4) if we encounter a variable which is not a flag or rip, we stop
 */
std::list <uint64_t> X86Disassembler :: evalEip (const InstructionX86 * ix86) {
    const std::list <const Instruction *> dominators = ix86->var_dominators("eip");

    std::list <Machine> machines;

    Machine firstMachine;
    firstMachine.s_variable(MachineVariable("eip", ix86->g_pc(), 32));

    machines.push_back(firstMachine);

    std::list <const Instruction *> :: const_iterator it;
    for (it = dominators.begin(); it != dominators.end(); it++) {
        const Instruction * instruction = *it;

        // stop on a load instruction
        if (dynamic_cast<const InstructionLoad *>(instruction))
            return std::list <uint64_t> ();

        Machine & firstMachine = machines.front();

        const std::list <Operand *> read_operands = instruction->operands_read();
        std::list <Operand *> :: const_iterator it;
        for (it = read_operands.begin(); it != read_operands.end(); it++) {
            // a read operand is a variable

            if (const Variable * variable = dynamic_cast<const Variable *>(*it)) {

                std::string variableName = variable->g_name();
                // this operand doesn't exist yet in the machine
                if (firstMachine.variable_exists(variableName) == false) {
                    // this operand is an arithmetic flag
                    if (    (variableName == "OF")
                         || (variableName == "SF")
                         || (variableName == "ZF")
                         || (variableName == "CF")) {
                        std::queue <Machine> newMachines;
                        std::list <Machine> :: iterator mit;
                        for (mit = machines.begin(); mit != machines.end(); mit++) {
                            Machine newMachine = *mit;
                            (*mit).s_variable(MachineVariable(variableName, 0, 1));
                            newMachine.s_variable(MachineVariable(variableName, 1, 1));
                            newMachines.push(newMachine);
                        }
                        while (newMachines.size() > 0) {
                            machines.push_back(newMachines.front());
                            newMachines.pop();
                        }
                    }
                    else {
                        // no result
                        return std::list <uint64_t> ();
                    }
                }
            }
        }

        std::list <Machine> :: iterator mit;
        for (mit = machines.begin(); mit != machines.end(); mit++) {
            (*mit).concreteExecution(instruction);
        }
    }

    std::set <uint64_t> eips;
    std::list <Machine> :: iterator mit;
    for (mit = machines.begin(); mit != machines.end(); mit++) {
        uint64_t eip = (*mit).g_variable("eip").g_value();
        if (eips.count(eip) == 0)
            eips.insert(eip);
    }

    return std::list <uint64_t> (eips.begin(), eips.end());
}

QuesoGraph * X86Disassembler :: disassemble (uint64_t entry,
                                         const MemoryModel * memoryModel) {
    std::unordered_set <uint64_t> queued;
    std::queue <uint64_t> queue;
    std::map <uint64_t, Instruction *> instructionMap;
    std::map <uint64_t, std::map <uint64_t, ControlFlowType>> edgeMap;

    QuesoX86 quesoX86;
    QuesoGraph * quesoGraph = new QuesoGraph();

    queue.push(entry);
    queued.insert(entry);

    while (queue.size() > 0) {
        uint64_t address = queue.front();
        queue.pop();

        MemoryBuffer memoryBuffer = memoryModel->g_bytes(address, 16);

        InstructionX86 * ix86 = quesoX86.translate(memoryBuffer.g_data(),
                                                   memoryBuffer.g_size(),
                                                   address);

        ix86 = ix86->copy();

        quesoGraph->absorbInstruction(ix86);

        instructionMap[address] = ix86;

        std::list <uint64_t> successors = evalEip(ix86);

        std::list <uint64_t> :: iterator it;
        for (it = successors.begin(); it != successors.end(); it++) {
            uint64_t successor = *it;
            edgeMap[address][successor] = CFT_NORMAL;
            if (queued.count(successor) == 0) {
                queued.insert(successor);
                queue.push(successor);
            }
        }

    }

    std::map <uint64_t, std::map <uint64_t, ControlFlowType>> :: iterator it;
    for (it = edgeMap.begin(); it != edgeMap.end(); it++) {
        std::map <uint64_t, ControlFlowType> :: iterator iit;
        for (iit = it->second.begin(); iit != it->second.end(); iit++) {
            Instruction * head = instructionMap[it->first];
            Instruction * tail = instructionMap[iit->first];
            if ((head == NULL) || (tail == NULL))
                continue;
            ControlFlowType type = iit->second;
            QuesoEdge * newQuesoEdge = new QuesoEdge(type, head, tail);
            quesoGraph->absorbQuesoEdge(newQuesoEdge);
        }
    }

    return quesoGraph;
}