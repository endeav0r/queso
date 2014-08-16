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
        MachineVariable (std::string name, uint64_t value, uint8_t bits) {
            this->name = name;
            this->value = value & ((((uint64_t) 1) << bits) - 1);
            this->bits = bits;
        }

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
        void     s_memory     (uint64_t address, uint8_t value);
        uint8_t  g_memory     (uint64_t address);
        void     s_variable_internal (const MachineVariable & machineVariable);

        void (* memReadHook)  (Machine * machine, uint64_t address, uint8_t value);
        void (* memWriteHook) (Machine * machine, uint64_t address, uint8_t value);
        void (* varReadHook)  (Machine * machine, const MachineVariable & machineVariable);
        void (* varWriteHook) (Machine * machine, const MachineVariable & machineVariable);
    public :
        Machine ();

        void          s_variable (const MachineVariable & machineVariable);
        void          s_memory   (uint64_t address, uint8_t * bytes, size_t size);
        MachineBuffer g_memory   (uint64_t address, size_t size);

        const MachineVariable & g_variable (std::string name) {
            return variables[name];
        }

        void s_memReadHook(void (* memReadHook) (Machine * machine,
                                                 uint64_t address,
                                                 uint8_t value)) {
            this->memReadHook = memReadHook;
        }

        void s_memWriteHook(void (* memWriteHook) (Machine * machine,
                                                   uint64_t address,
                                                   uint8_t value)) {
            this->memWriteHook = memWriteHook;
        }

        void s_varReadHook(void (* varReadHook) (Machine * machine,
                                                 const MachineVariable & machineVariable)) {
            this->varReadHook = varReadHook;
        }

        void s_varWriteHook(void (* varWriteHook) (Machine * machine,
                                                   const MachineVariable & machineVariable)) {
            this->varWriteHook = varWriteHook;
        }

        void concreteExecution (const Instruction * instruction);
};

#endif