#include "machine.h"

#include <iostream>

#define INVALID_OPERAND_TYPE -100
#define DEBUG_ENGINE
//#define DEBUG_ENGINE_MEMORY


Machine :: Machine () {
    memReadHook = NULL;
    memWriteHook = NULL;
    varReadHook = NULL;
    varWriteHook = NULL;
}


void Machine :: s_variable_internal (const MachineVariable & machineVariable) {
    this->variables[machineVariable.g_name()] = machineVariable;
    if (varWriteHook != NULL)
        varWriteHook(this, machineVariable);
}


void Machine :: s_variable (const MachineVariable & machineVariable) {
    this->variables[machineVariable.g_name()] = machineVariable;
}


void Machine :: s_memory (uint64_t address, uint8_t * bytes, size_t size) {
    for (size_t i = 0; i < size; i++) {
        #ifdef DEBUG_ENGINE_MEMORY
        char tmp[8];
        snprintf(tmp, 8, "%02x", bytes[i]);
        std::cout << "DEBUG_ENGINE_MEMORY s_memory " 
                  << std::hex << (address + i) << " = " << tmp << std::endl;
        #endif
        this->memory[address + i] = bytes[i];
    }
}


void Machine :: s_memory (uint64_t address, uint8_t value) {
    this->memory[address] = value;
    if (memWriteHook != NULL)
        memWriteHook(this, address, value);
}


uint8_t Machine :: g_memory (uint64_t address) {
    #ifdef DEBUG_ENGINE_MEMORY
    std::cout << "DEBUG_ENGINE_MEMORY g_memory " << std::hex << address << std::endl;
    #endif

    if (memReadHook != NULL)
        memReadHook(this, address, memory[address]);
    return memory[address];
}


MachineBuffer Machine :: g_memory (uint64_t address, size_t size) {
    uint8_t * buffer = new uint8_t [size];

    for (size_t i = 0; i < size; i++) {
        buffer[i] = memory[address + i];
    }

    return MachineBuffer(buffer, size, true);
}


int64_t Machine :: signExtend (uint64_t variable, unsigned int inBits, unsigned int outBits) {
    uint64_t outMask = (((uint64_t ) 1) << outBits) - 1;

    uint64_t signMask = ((uint64_t) -1) << inBits;

    uint64_t matchMask = (uint64_t) ((uint64_t) 1) << (inBits - (uint64_t) 1);

    #ifdef DEBUG_ENGINE
    std::cout << "DEBUG_ENGINE signExtend variable=" << std::hex << variable 
              << " inBits=" << std::hex << inBits
              << " outBits=" << std::hex << outBits 
              << " outMask=" << std::hex << outMask 
              << " signMask=" << std::hex << signMask 
              << " matchMask=" << std::hex << matchMask << std::endl;
    #endif

    if (variable & matchMask)
        return (variable | signMask) & outMask;
    else
        return variable & outMask;
}


uint64_t Machine :: operandValue (const Operand * operand) {
    if (operand->g_type() == CONSTANT)
        return dynamic_cast<const Constant *>(operand)->g_value();
    else if (operand->g_type() == VARIABLE) {
        if (varReadHook != NULL)
            varReadHook(this, variables[dynamic_cast<const Variable *>(operand)->g_name()]);
        return variables[dynamic_cast<const Variable *>(operand)->g_name()].g_value();
    }

    throw INVALID_OPERAND_TYPE;
    return -1;
}


void Machine :: concreteExecution (const Instruction * instruction) {

    // ASSIGN
    if (const InstructionAssign * ins = dynamic_cast<const InstructionAssign *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_src()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // STORE
    else if (const InstructionStore * ins = dynamic_cast<const InstructionStore *>(instruction)) {
        #ifdef DEBUG_ENGINE
        std::cout << "DEBUG_ENGINE store [" << std::hex << operandValue(ins->g_address())
                  << "] = " << std::hex << operandValue(ins->g_value()) << std::endl;
        #endif
        s_memory(operandValue(ins->g_address()), operandValue(ins->g_value()));
    }

    // LOAD
    else if (const InstructionLoad * ins = dynamic_cast<const InstructionLoad *>(instruction)) {
        #ifdef DEBUG_ENGINE
        std::cout << "DEBUG_ENGINE load " << ins->g_dst()->queso() << " = "
                  << "[" << std::hex << operandValue(ins->g_address()) << "]" << std::endl;
        #endif
        MachineVariable dst(ins->g_dst()->g_name(),
                            g_memory(operandValue(ins->g_address())),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // ITE
    else if (const InstructionIte * ins = dynamic_cast<const InstructionIte *>(instruction)) {
        #ifdef DEBUG_ENGINE
        std::cout << "DEBUG_ENGINE ite " << ins->g_dst()->queso() << " = "
                  << ins->g_condition()->queso() << " ("
                  << operandValue(ins->g_condition()) << ") ? "
                  << ins->g_t()->queso() << " (" << std::hex << operandValue(ins->g_t()) << ") : " 
                  << ins->g_e()->queso() << " (" << std::hex << operandValue(ins->g_e()) << ")"
                  << std::endl;
        #endif
        if (operandValue(ins->g_condition()) != 0) {
            MachineVariable dst(ins->g_dst()->g_name(),
                                operandValue(ins->g_t()),
                                ins->g_dst()->g_bits());
            s_variable_internal(dst);
        }
        else {
            MachineVariable dst(ins->g_dst()->g_name(),
                                operandValue(ins->g_e()),
                                ins->g_dst()->g_bits());
            s_variable_internal(dst);
        }
    }

    // SIGN EXTEND
    else if (const InstructionSignExtend * ins = dynamic_cast<const InstructionSignExtend *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            signExtend(operandValue(ins->g_src()),
                                                    ins->g_src()->g_bits(),
                                                    ins->g_dst()->g_bits()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // ADD
    else if (const InstructionAdd * ins = dynamic_cast<const InstructionAdd *>(instruction)) {
        #ifdef DEBUG_ENGINE
        std::cout << "DEBUG_ENGINE " << ins->g_dst()->g_name() << " = "
                  << operandValue(ins->g_lhs()) << " + " << operandValue(ins->g_rhs())
                  << " => " << (operandValue(ins->g_lhs()) + operandValue(ins->g_rhs()))
                  << std::endl;
        #endif

        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) + operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // SUB
    else if (const InstructionSub * ins = dynamic_cast<const InstructionSub *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) - operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // MUL
    else if (const InstructionMul * ins = dynamic_cast<const InstructionMul *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) * operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // UDIV
    else if (const InstructionUdiv * ins = dynamic_cast<const InstructionUdiv *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) / operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // UMOD
    else if (const InstructionUmod * ins = dynamic_cast<const InstructionUmod *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) % operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // AND
    else if (const InstructionAnd * ins = dynamic_cast<const InstructionAnd *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) & operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // OR
    else if (const InstructionOr * ins = dynamic_cast<const InstructionOr *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) | operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // XOR
    else if (const InstructionXor * ins = dynamic_cast<const InstructionXor *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) ^ operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // SHL
    else if (const InstructionShl * ins = dynamic_cast<const InstructionShl *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) << operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // SHR
    else if (const InstructionShr * ins = dynamic_cast<const InstructionShr *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_lhs()) >> operandValue(ins->g_rhs()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // CMPEQ
    else if (const InstructionCmpEq * ins = dynamic_cast<const InstructionCmpEq *>(instruction)) {
        unsigned int result = 0;
        if (operandValue(ins->g_lhs()) == operandValue(ins->g_rhs()))
            result = 1;
        s_variable_internal(MachineVariable(ins->g_dst()->g_name(), result, 1));
    }

    // CMPLTU
    else if (const InstructionCmpLtu * ins = dynamic_cast<const InstructionCmpLtu *>(instruction)) {
        unsigned int result = 0;
        if (operandValue(ins->g_lhs()) < operandValue(ins->g_rhs()))
            result = 1;
        s_variable_internal(MachineVariable(ins->g_dst()->g_name(), result, 1));
    }

    // CMPLTS
    else if (const InstructionCmpLts * ins = dynamic_cast<const InstructionCmpLts *>(instruction)) {
        unsigned int result = 0;
        int64_t lhs = signExtend(operandValue(ins->g_lhs()), 64, ins->g_lhs()->g_bits());
        int64_t rhs = signExtend(operandValue(ins->g_rhs()), 64, ins->g_rhs()->g_bits());
        if (lhs < rhs)
            result = 1;
        s_variable_internal(MachineVariable(ins->g_dst()->g_name(), result, 1));
    }

    // CMPLEU
    else if (const InstructionCmpLeu * ins = dynamic_cast<const InstructionCmpLeu *>(instruction)) {
        unsigned int result = 0;
        if (operandValue(ins->g_lhs()) <= operandValue(ins->g_rhs()))
            result = 1;
        s_variable_internal(MachineVariable(ins->g_dst()->g_name(), result, 1));
    }

    // CMPLES
    else if (const InstructionCmpLes * ins = dynamic_cast<const InstructionCmpLes *>(instruction)) {
        unsigned int result = 0;
        int64_t lhs = signExtend(operandValue(ins->g_lhs()), 64, ins->g_lhs()->g_bits());
        int64_t rhs = signExtend(operandValue(ins->g_rhs()), 64, ins->g_rhs()->g_bits());
        if (lhs <= rhs)
            result = 1;
        s_variable_internal(MachineVariable(ins->g_dst()->g_name(), result, 1));
    }

    std::list <Instruction *> :: const_iterator it;
    for (it = instruction->g_depth_instructions().begin();
         it != instruction->g_depth_instructions().end();
         it++) {
        concreteExecution(*it);
    }
}