#ifndef machine_HEADER
#define machine_HEADER

#include <cstring>
#include <inttypes.h>
#include <map>
#include <string>

#include "queso/queso.h"

class MachineBuffer {
    private :
        uint8_t * bytes;
        size_t size;
    public :
        MachineBuffer (uint8_t * bytes, size_t size, bool takeBuffer = false) {
            if (takeBuffer)
                this->bytes = bytes;
            else {
                this->bytes = new uint8_t[size];
                memcpy(this->bytes, bytes, size);
            }
            this->size = size;
        }

        ~MachineBuffer () {
            delete[] bytes;
        }

        const uint8_t * g_bytes() { return bytes; }
        size_t g_size () { return size; }
};


class MachineVariable {
    private :
        std::string name;
        uint64_t    value;
        uint8_t     bits;
    public :
        MachineVariable () {}
        MachineVariable (std::string name, uint64_t value, uint8_t bits)
            : name (name), value (value), bits (bits) {}

        const std::string & g_name () const { return name; }
        uint64_t g_value () const { return value; }
        uint8_t  g_bits  () const { return bits; }

        MachineVariable * copy () {
            return new MachineVariable(name, value, bits);
        }
};



class Machine {
    private :
        std::map <uint64_t, uint8_t> memory;
        std::map <std::string, MachineVariable> variables;

        int64_t  signExtend   (uint64_t variable, unsigned int inBits, unsigned int outBits);
        uint64_t operandValue (const Operand * operand);
    public :

        void          s_variable (const MachineVariable & machineVariable);
        void          s_memory   (uint64_t address, uint8_t * bytes, size_t size);
        uint8_t       g_memory   (uint64_t address);
        MachineBuffer g_memory   (uint64_t address, size_t size);

        const MachineVariable & g_variable (std::string name) {
            return variables[name];
        }

        void concreteExecution (const Instruction * instruction);
};

#endif