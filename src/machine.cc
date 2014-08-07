#include "machine.h"


void Machine :: s_memory (uint64_t address, const uint8_t * data, size_t size) {
    for (size_t i = 0; i < size; i++) {
        memory[address + i] = data[i];
    }
}


uint8_t Machine :: g_memory (uint64_t address) {
    return memory[address];
}


void Machine :: s_register (std::string name, uint64_t value) {
    if (registers.count(name) == 0)
        registers[name] = Register(name, value);
    else
        registers[name].s_value(value);
}


uint64_t Machine :: g_register (std::string name) {
    return registers[name];
}


void Machine :: concrete_step_instruction (Instruction * instruction) {
    if (instruction == NULL)
        return;

    if (instruction->g_type() == QUESO) {
        if (InstructionAssign * insAssign = dynamic_cast<InstructionAssign *>(instruction)) {
            s_register(insAssign->g_dst()->g_name(), g_register(insAssign->g_src()->g_name()));
        }
        else if (InstructionStore * insStore = dynamic_cast<InstructionStore *>(instruction)) {
            memory[insStore->]
        }
    }
}


void Machine :: concrete_step () {
    // build memory around instruction_pointer

    uint8_t buf[16];
    size_t buf_size = 0;
    uint64_t ip_value = registers[ip_name].g_value();
    for (uint64_t ip = 0; ip < 16; ip++) {
        if (memory.count(ip + ip_value) == 0)
            break;
        buf[buf_size++] = memory[ip + ip_value];
    }

    Instruction * instruction = translator.translate(buf, buf_size);

    concrete_step_instruction(instruction);

    delete instruction;
}