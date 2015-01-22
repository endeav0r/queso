#include "machine.h"

#include <iostream>

#define INVALID_OPERAND_TYPE -100
//#define DEBUG_MACHINE
//#define DEBUG_MACHINE_MEMORY


Machine :: Machine () {
    pre_memReadHook = NULL;
    post_memReadHook = NULL;
    pre_memWriteHook = NULL;
    post_memWriteHook = NULL;
    pre_varReadHook = NULL;
    post_varReadHook = NULL;
    pre_varWriteHook = NULL;
    post_varWriteHook = NULL;
    pre_instructionHook = NULL;
    post_instructionHook = NULL;
}


Machine Machine :: fork () {
    Machine machine = *this;
    return machine;
}


void Machine :: s_variable_internal (const MachineVariable & machineVariable) {
    if (pre_varWriteHook != NULL)
        pre_varWriteHook(this, machineVariable, pre_varWriteHook_data);
    this->variables[machineVariable.g_name()] = machineVariable;
    if (post_varWriteHook != NULL)
        post_varWriteHook(this, machineVariable, post_varWriteHook_data);
}


void Machine :: s_variable (const MachineVariable & machineVariable) {
    this->variables[machineVariable.g_name()] = machineVariable;
}


void Machine :: s_memory (uint64_t address, uint8_t * bytes, size_t size) {
    for (size_t i = 0; i < size; i++) {
        #ifdef DEBUG_MACHINE_MEMORY
        char tmp[8];
        snprintf(tmp, 8, "%02x", bytes[i]);
        std::cout << "DEBUG_MACHINE_MEMORY s_memory " 
                  << std::hex << (address + i) << " = " << tmp << std::endl;
        #endif
        this->memoryModel.s_byte(address + i, bytes[i]);
    }
}


void Machine :: s_memory (uint64_t address, uint8_t value) {
    if (pre_memWriteHook != NULL)
        pre_memWriteHook(this, address, value, pre_memWriteHook_data);
    this->memoryModel.s_byte(address, value);
    if (post_memWriteHook != NULL)
        post_memWriteHook(this, address, value, post_memWriteHook_data);
}


uint8_t Machine :: g_memory (uint64_t address) {
    #ifdef DEBUG_MACHINE_MEMORY
    std::cout << "DEBUG_MACHINE_MEMORY g_memory " << std::hex << address << std::endl;
    #endif

    if (pre_memReadHook != NULL)
        pre_memReadHook(this, address, this->memoryModel.g_byte(address), pre_memReadHook_data);
    uint8_t value = this->memoryModel.g_byte(address);
    if (post_memReadHook != NULL)
        post_memReadHook(this, address, this->memoryModel.g_byte(address), post_memReadHook_data);
    return value;
}


MachineBuffer Machine :: g_memory (uint64_t address, size_t size) {
    uint8_t * buffer = new uint8_t [size];

    for (size_t i = 0; i < size; i++) {
        buffer[i] = this->memoryModel.g_byte(address + i);
    }

    return MachineBuffer(buffer, size, true);
}


int64_t Machine :: signExtend (uint64_t variable, unsigned int inBits, unsigned int outBits) {
    uint64_t outMask = (((uint64_t ) 1) << outBits) - 1;

    uint64_t signMask = ((uint64_t) -1) << inBits;

    uint64_t matchMask = (uint64_t) ((uint64_t) 1) << (inBits - (uint64_t) 1);

    #ifdef DEBUG_MACHINE
    std::cout << "DEBUG_MACHINE signExtend variable=" << std::hex << variable 
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
    if (operand->g_type() == CONSTANT) {
        return dynamic_cast<const Constant *>(operand)->g_value();
    }
    else if (operand->g_type() == VARIABLE) {
        if (pre_varReadHook != NULL)
            pre_varReadHook(this,
                            dynamic_cast<const Variable *>(operand),
                            pre_varReadHook_data);
        std::string variableName = dynamic_cast<const Variable *>(operand)->g_name();
        uint64_t value = variables[variableName].g_value();
        if (post_varReadHook != NULL)
            post_varReadHook(this,
                             variables[dynamic_cast<const Variable *>(operand)->g_name()],
                             post_varReadHook_data);
        return value;
    }

    throw INVALID_OPERAND_TYPE;
    return -1;
}


void Machine :: concreteExecution (Instruction * instruction) {
    this->stop_flag = false;

    if (pre_instructionHook != NULL)
        pre_instructionHook(this, instruction, pre_instructionHook_data);

    if (stop_flag)
        return;

    // ASSIGN
    if (const InstructionAssign * ins = dynamic_cast<const InstructionAssign *>(instruction)) {
        MachineVariable dst(ins->g_dst()->g_name(),
                            operandValue(ins->g_src()),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // STORE
    else if (const InstructionStore * ins = dynamic_cast<const InstructionStore *>(instruction)) {
        #ifdef DEBUG_MACHINE
        std::cout << "DEBUG_MACHINE store [" << std::hex << operandValue(ins->g_address())
                  << "] = " << std::hex << operandValue(ins->g_value()) << std::endl;
        #endif
        s_memory(operandValue(ins->g_address()), operandValue(ins->g_value()));
    }

    // LOAD
    else if (const InstructionLoad * ins = dynamic_cast<const InstructionLoad *>(instruction)) {
        #ifdef DEBUG_MACHINE
        std::cout << "DEBUG_MACHINE load " << ins->g_dst()->queso() << " = "
                  << "[" << std::hex << operandValue(ins->g_address()) << "]" << std::endl;
        #endif
        MachineVariable dst(ins->g_dst()->g_name(),
                            g_memory(operandValue(ins->g_address())),
                            ins->g_dst()->g_bits());
        s_variable_internal(dst);
    }

    // ITE
    else if (const InstructionIte * ins = dynamic_cast<const InstructionIte *>(instruction)) {
        #ifdef DEBUG_MACHINE
        std::cout << "DEBUG_MACHINE ite " << ins->g_dst()->queso() << " = "
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
        #ifdef DEBUG_MACHINE
        std::cout << "DEBUG_MACHINE " << ins->g_dst()->g_name() << " = "
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
    else if (const InstructionUrem * ins = dynamic_cast<const InstructionUrem *>(instruction)) {
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

    if (post_instructionHook != NULL)
        post_instructionHook(this, instruction, post_instructionHook_data);

    std::list <Instruction *> :: iterator it;
    for (it = instruction->g_depth_instructions().begin();
         it != instruction->g_depth_instructions().end();
         it++) {
        concreteExecution(*it);
    }
}