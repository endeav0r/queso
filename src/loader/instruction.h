#ifndef disassembler_HEADER
#define disassembler_HEADER

#include <inttypes.h>


enum ControlFlowType {
    CFT_NORMAL,
    CFT_JUMP,
    CFT_JCC_TRUE,
    CFT_JCC_FALSE,
    CFT_CALL
};

class InstructionSuccessor {
    private :
        ControlFlowType type;
        uint64_t address;
    public :
        InstructionSuccessor (ControlFlowType type, uint64_t address)
            : type (type), address (address) {}
        InstructionSuccessor () {}

        ControlFlowType g_type    () { return type; }
        ControlFlowType g_address () { return address; }
};

class Instruction {
    private :
        uint64_t  address;
        uint8_t * bytes;
        size_t    bytes_size;
        std::list <InstructionSuccessor> successors;
        std::string text;

    public :
        Instruction (uint64_t address,
                     uint8_t * bytes,
                     size_t bytes_size,
                     const std::string & text) {
            this->address = address;
            this->bytes = new uint8_t [bytes_size];
            memcpy(this->bytes, bytes, bytes_size);
            this->bytes_size = size;
            this->text = text;
        }

        Instruction () : bytes (NULL) {}

        ~Instruction () {
            if (this->bytes != NULL)
                delete[] this->bytes;
        }

        void push_successor (const InstructionSuccessor & instructionSuccessor) {
            this->successors.push_back(instructionSuccessor);
        }

        const std::list <InstructionSuccessor> & g_successors () {
            return this->successors;
        }

        const std::string & g_text       () { return text; }
        uint64_t            g_address    () { return address; }
        uint8_t *           g_bytes      () { return bytes; }
        size_t              g_bytes_size () { return bytes_size; }
};

#endif