#ifndef machine_HEADER
#define machine_HEADER

#include <string>

#include "queso/queso.h"

class Buffer {
    private :
        uint8_t * bytes;
        size_t size;
    public :
        Buffer (uint8_t * bytes, size_t size) {
            this->bytes = new bytes[size];
            memcpy(this->bytes, bytes, size);
            this->size = size;
        }

        ~Buffer () {
            delete[] bytes;
        }

        const uint8_t * g_bytes() { return bytes; }
        size_t g_size () { return size; }
};


class Variable {
    private :
        std::string name;
        uint64_t    value;
        uint8_t     bits;
    public :
        Variable (std::string name, uint64_t value, uint8_t bits)
            : name (name), value (value), bits (bits) {}

        const std::string & g_name () { return name; }
        uint64_t g_value () { return value; }
        uint8_t  g_bits  () { return bits; }
};



class Machine {
    private :
        std::map <uint64_t, uint8_t> memory;
        std::map <std::string, Variable> variables;
    public :
        Machine ();

        void    s_memory (uint64_t address, uint8_t * bytes, size_t size);
        uint8_t g_memory (uint64_t address);
        Buffer  g_memory (uint64_t address, size_t size);

        void concreteExecution (Instruction * instruction);
};

#endif