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
std::list <uint64_t> X86Disassembler :: evalEip (InstructionX86 * ix86) {
    std::list <Instruction *> dominators = ix86->var_dominators("eip");

    std::list <Machine> machines;

    Machine firstMachine;
    firstMachine.s_variable(MachineVariable("eip", ix86->g_pc(), 32));

    machines.push_back(firstMachine);

    std::list <Instruction *> :: iterator it;
    for (it = dominators.begin(); it != dominators.end(); it++) {
        Instruction * instruction = *it;

        // stop on a load instruction
        if (dynamic_cast<const InstructionLoad *>(instruction))
            return std::list <uint64_t> ();

        Machine & firstMachine = machines.front();

        std::list <Operand *> read_operands = instruction->operands_read();
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


class X86DisassemblerNext {
    public :
        uint64_t predecessor_vIndex;
        uint64_t successor_address;
        bool has_predecessor;
        X86DisassemblerNext (uint64_t predecessor_vIndex, uint64_t successor_address)
            : predecessor_vIndex (predecessor_vIndex),
              successor_address (successor_address),
              has_predecessor (true) {}
};


QuesoGraph * X86Disassembler :: disassemble (uint64_t entry,
                                         const MemoryModel * memoryModel) {
    std::unordered_set <uint64_t> queued;
    std::queue <X86DisassemblerNext> queue;

    X86DisassemblerNext first(0, entry);
    first.has_predecessor = false;

    queue.push(first);

    QuesoX86 quesoX86;
    QuesoGraph * quesoGraph = new QuesoGraph();

    queued.insert(entry);

    while (queue.size() > 0) {
        X86DisassemblerNext next = queue.front();
        queue.pop();

        MemoryBuffer memoryBuffer = memoryModel->g_bytes(next.successor_address, 16);

        InstructionX86 * ix86 = quesoX86.translate(memoryBuffer.g_data(),
                                                   memoryBuffer.g_size(),
                                                   next.successor_address);

        ix86 = ix86->copy();

        quesoGraph->absorbInstruction(ix86, ix86->g_pc());

        if (next.has_predecessor)
            quesoGraph->absorbQuesoEdge(new QuesoEdge(quesoGraph,
                                                      next.predecessor_vIndex,
                                                      ix86->g_vIndex(),
                                                      CFT_NORMAL));

        std::list <uint64_t> successors = evalEip(ix86);

        std::list <uint64_t> :: iterator it;
        for (it = successors.begin(); it != successors.end(); it++) {
            uint64_t successor_address = *it;
            if (queued.count(successor_address) == 0) {
                queued.insert(successor_address);
                queue.push(X86DisassemblerNext(ix86->g_vIndex(), successor_address));
            }
            else {
                quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                     ix86->g_vIndex(),
                                                     successor_address,
                                                     CFT_NORMAL));
            }
        }

    }

    return quesoGraph;
}


QuesoGraph * X86Disassembler :: acyclicDepth (uint64_t entry,
                                              const MemoryModel * memoryModel,
                                              uint64_t depth) {
    std::queue <InstructionX86 *> queue;
    QuesoGraph * quesoGraph = new QuesoGraph();
    QuesoX86 quesoX86;

    // disassemble the first instruction, prime the queue
    MemoryBuffer memoryBuffer = memoryModel->g_bytes(entry, 16);
    InstructionX86 * ix86 = quesoX86.translate(memoryBuffer.g_data(),
                                               memoryBuffer.g_size(),
                                               entry);
    ix86 = ix86->copy();
    quesoGraph->absorbInstruction(ix86);
    queue.push(ix86);

    for (uint64_t i = 0; i < depth; i++) {
        std::queue <InstructionX86 *> newQueue = std::queue <InstructionX86 *>();

        // for every instruction at this depth
        while (queue.size() > 0) {
            InstructionX86 * ix86 = queue.front();
            queue.pop();

            // get all successors for this instruction
            std::list <uint64_t> successors = evalEip(ix86);
            std::list <uint64_t> :: iterator it;
            for (it = successors.begin(); it != successors.end(); it++) {
                uint64_t address = *it;
                // disassemble each instruction
                MemoryBuffer memoryBuffer = memoryModel->g_bytes(address, 16);
                InstructionX86 * nextIx86 = quesoX86.translate(memoryBuffer.g_data(),
                                                               memoryBuffer.g_size(),
                                                               address);
                nextIx86 = nextIx86->copy();

                // add to graph and create the edge
                quesoGraph->absorbInstruction(nextIx86);
                quesoGraph->absorbEdge(new QuesoEdge(quesoGraph,
                                                     ix86->g_vIndex(),
                                                     nextIx86->g_vIndex(),
                                                     CFT_NORMAL));

                // add this instruction to the new queue
                newQueue.push(nextIx86);
            }
        }
        queue = newQueue;
    }

    return quesoGraph;
}