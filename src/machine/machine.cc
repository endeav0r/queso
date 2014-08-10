#include "machine.h"

#define INVALID_OPERAND_TYPE -100

void Machine :: s_variable (const MachineVariable & machineVariable) {
    this->variables[machineVariable.g_name()] = machineVariable;
}

void Machine :: s_memory (uint64_t address, uint8_t * bytes, size_t size) {
    for (size_t i = 0; i < size; i++) {
        this->memory[address + i] = bytes[i];
    }
}


uint8_t Machine :: g_memory (uint64_t address) {
    return memory[address];
}


MachineBuffer Machine :: g_memory (uint64_t address, size_t size) {
    uint8_t * buffer = new uint8_t [size];

    for (size_t i = 0; i < size; i++) {
        buffer[i] = memory[address + i];
    }

    return MachineBuffer(buffer, size, true);
}


int64_t Machine :: signExtend (uint64_t variable, size_t inBits, size_t outBits) {
    uint64_t outMask;
    outMask = 1 << (outBits + 1);
    outMask -= 1;

    uint64_t signMask = -1;
    signMask <<= inBits;

    if (variable & (1 << (inBits - 1)))
        return (variable & signMask) & outMask;
    else
        return variable & outMask;
}


uint64_t Machine :: operandValue (const Operand * operand) {
    if (operand->g_type() == CONSTANT)
        return dynamic_cast<const Constant *>(operand)->g_value();
    else if (operand->g_type() == VARIABLE)
        return variables[dynamic_cast<const Variable *>(operand)->g_name()].g_value();

    throw INVALID_OPERAND_TYPE;
    return -1;
}


void Machine :: concreteExecution (const Instruction * instruction) {
    // ASSIGN
    if (const InstructionAssign * ins = dynamic_cast<const InstructionAssign *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_src()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // STORE
    else if (const InstructionStore * ins = dynamic_cast<const InstructionStore *>(instruction)) {
        memory[operandValue(ins->g_address())] = operandValue(ins->g_value());
    }

    // LOAD
    else if (const InstructionLoad * ins = dynamic_cast<const InstructionLoad *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            memory[operandValue(ins->g_address())],
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // ITE
    else if (const InstructionIte * ins = dynamic_cast<const InstructionIte *>(instruction)) {
        if (operandValue(ins->g_condition()) != 0) {
            MachineVariable dst(ins->g_dst()->g_name(),
                                operandValue(ins->g_t()),
                                ins->g_dst()->g_bits());
            variables[dst.g_name()] = dst;
        }
        else {
            MachineVariable dst(ins->g_dst()->g_name(),
                                operandValue(ins->g_e()),
                                ins->g_dst()->g_bits());
            variables[dst.g_name()] = dst;
        }
    }

    // SIGN EXTEND
    else if (const InstructionSignExtend * ins = dynamic_cast<const InstructionSignExtend *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            signExtend(operandValue(ins->g_src()),
                                                    ins->g_dst()->g_bits(),
                                                    ins->g_src()->g_bits()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // ADD
    else if (const InstructionAdd * ins = dynamic_cast<const InstructionAdd *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) + operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // SUB
    else if (const InstructionSub * ins = dynamic_cast<const InstructionSub *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) - operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // MUL
    else if (const InstructionMul * ins = dynamic_cast<const InstructionMul *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) * operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // UDIV
    else if (const InstructionUdiv * ins = dynamic_cast<const InstructionUdiv *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) / operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // UMOD
    else if (const InstructionUmod * ins = dynamic_cast<const InstructionUmod *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) % operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // AND
    else if (const InstructionAnd * ins = dynamic_cast<const InstructionAnd *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) & operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // OR
    else if (const InstructionOr * ins = dynamic_cast<const InstructionOr *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) | operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // XOR
    else if (const InstructionXor * ins = dynamic_cast<const InstructionXor *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) ^ operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // SHL
    else if (const InstructionShl * ins = dynamic_cast<const InstructionShl *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) << operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // SHR
    else if (const InstructionShr * ins = dynamic_cast<const InstructionShr *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) >> operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        variables[dst.g_name()] = dst;
    }

    // CMPEQ
    else if (const InstructionCmpEq * ins = dynamic_cast<const InstructionCmpEq *>(instruction)) {
        unsigned int result = 0;
        if (operandValue(ins->g_lhs()) == operandValue(ins->g_rhs()))
            result = 1;
        variables[ins->g_dst()->g_name()] = MachineVariable(ins->g_dst()->g_name(), result, 1);
    }

    // CMPLTU
    else if (const InstructionCmpLtu * ins = dynamic_cast<const InstructionCmpLtu *>(instruction)) {
        unsigned int result = 0;
        if (operandValue(ins->g_lhs()) < operandValue(ins->g_rhs()))
            result = 1;
        variables[ins->g_dst()->g_name()] = MachineVariable(ins->g_dst()->g_name(), result, 1);
    }

    // CMPLTS
    else if (const InstructionCmpLts * ins = dynamic_cast<const InstructionCmpLts *>(instruction)) {
        unsigned int result = 0;
        int64_t lhs = signExtend(operandValue(ins->g_lhs()), 64, ins->g_lhs()->g_bits());
        int64_t rhs = signExtend(operandValue(ins->g_rhs()), 64, ins->g_rhs()->g_bits());
        if (lhs < rhs)
            result = 1;
        variables[ins->g_dst()->g_name()] = MachineVariable(ins->g_dst()->g_name(), result, 1);
    }

    // CMPLEU
    else if (const InstructionCmpLeu * ins = dynamic_cast<const InstructionCmpLeu *>(instruction)) {
        unsigned int result = 0;
        if (operandValue(ins->g_lhs()) <= operandValue(ins->g_rhs()))
            result = 1;
        variables[ins->g_dst()->g_name()] = MachineVariable(ins->g_dst()->g_name(), result, 1);
    }

    // CMPLES
    else if (const InstructionCmpLes * ins = dynamic_cast<const InstructionCmpLes *>(instruction)) {
        unsigned int result = 0;
        int64_t lhs = signExtend(operandValue(ins->g_lhs()), 64, ins->g_lhs()->g_bits());
        int64_t rhs = signExtend(operandValue(ins->g_rhs()), 64, ins->g_rhs()->g_bits());
        if (lhs <= rhs)
            result = 1;
        variables[ins->g_dst()->g_name()] = MachineVariable(ins->g_dst()->g_name(), result, 1);
    }

    std::list <Instruction *> :: const_iterator it;
    for (it = instruction->g_depth_instructions().begin();
         it != instruction->g_depth_instructions().end();
         it++) {
        concreteExecution(*it);
    }
}