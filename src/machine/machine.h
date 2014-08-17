#ifndef machine_HEADER
#define machine_HEADER

#include <cstring>
#include <inttypes.h>
#include <map>
#include <string>

#include "containers/memoryModel.h"
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
        bool stop_flag;

        MemoryModel memoryModel;
        std::map <std::string, MachineVariable> variables;

        int64_t  signExtend   (uint64_t variable, unsigned int inBits, unsigned int outBits);
        uint64_t operandValue (const Operand * operand);
        void     s_memory     (uint64_t address, uint8_t value);
        uint8_t  g_memory     (uint64_t address);
        void     s_variable_internal (const MachineVariable & machineVariable);

        void * pre_memReadHook_data = NULL;
        void * post_memReadHook_data = NULL;
        void * pre_memWriteHook_data = NULL;
        void * post_memWriteHook_data = NULL;
        void * pre_varReadHook_data = NULL;
        void * post_varReadHook_data = NULL;
        void * pre_varWriteHook_data = NULL;
        void * post_varWriteHook_data = NULL;
        void * pre_instructionHook_data = NULL;
        void * post_instructionHook_data = NULL;

        void (* pre_memReadHook)      (Machine * machine,
                                       uint64_t address,
                                       uint8_t value,
                                       void * data);
        void (* post_memReadHook)     (Machine * machine,
                                       uint64_t address,
                                       uint8_t value,
                                       void * data);
        void (* pre_memWriteHook)     (Machine * machine,
                                       uint64_t address,
                                       uint8_t value,
                                       void * data);
        void (* post_memWriteHook)    (Machine * machine,
                                       uint64_t address,
                                       uint8_t value,
                                       void * data);
        void (* pre_varReadHook)      (Machine * machine,
                                       const Variable * variable,
                                       void * data);
        void (* post_varReadHook)     (Machine * machine,
                                       const MachineVariable & machineVariable,
                                       void * data);
        void (* pre_varWriteHook)     (Machine * machine,
                                       const MachineVariable & MachineVariable,
                                       void * data);
        void (* post_varWriteHook)    (Machine * machine,
                                       const MachineVariable & machineVariable,
                                       void * data);
        void (* pre_instructionHook)  (Machine * machine,
                                       const Instruction * instruction,
                                       void * data);
        void (* post_instructionHook) (Machine * machine,
                                       const Instruction * instruction,
                                       void * data);

    public :
        Machine ();
        Machine fork ();

        void concreteExecution (const Instruction * instruction);

        void          s_variable (const MachineVariable & machineVariable);
        void          s_memory   (uint64_t address, uint8_t * bytes, size_t size);
        MachineBuffer g_memory   (uint64_t address, size_t size);
        bool          variable_exists (std::string name) {
            if (variables.count(name) > 0)
                return true;
            return false;
        }

        MemoryModel g_memoryModel () { return memoryModel; }

        void stop () { stop_flag = true; }

        const MachineVariable & g_variable (std::string name) {
            return variables[name];
        }

        void s_pre_memReadHook(void (* pre_memReadHook) (Machine * machine,
                                                         uint64_t address,
                                                         uint8_t value,
                                                         void * data),
                               void * data) {
            this->pre_memReadHook = pre_memReadHook;
            this->pre_memReadHook_data = data;
        }

        void s_post_memReadHook(void (* post_memReadHook) (Machine * machine,
                                                           uint64_t address,
                                                           uint8_t value,
                                                           void * data),
                                void * data) {
            this->post_memReadHook = post_memReadHook;
            this->post_memReadHook_data = data;
        }

        void s_pre_memWriteHook(void (* pre_memWriteHook) (Machine * machine,
                                                           uint64_t address,
                                                           uint8_t value,
                                                           void * data),
                                void * data) {
            this->pre_memWriteHook = pre_memWriteHook;
            this->pre_memWriteHook_data = data;
        }

        void s_post_memWriteHook(void (* post_memWriteHook) (Machine * machine,
                                                             uint64_t address,
                                                             uint8_t value,
                                                             void * data),
                                void * data) {
            this->post_memWriteHook = post_memWriteHook;
            this->post_memWriteHook_data = data;
        }

        void s_pre_varReadHook(void (* pre_varReadHook) (Machine * machine,
                                                         const Variable * variable,
                                                         void * data),
                               void * data) {
            this->pre_varReadHook = pre_varReadHook;
            this->pre_varReadHook_data = data;
        }

        void s_post_varReadHook(void (* post_varReadHook) (Machine * machine,
                                                           const MachineVariable & machineVariable,
                                                           void * data),
                                void * data) {
            this->post_varReadHook = post_varReadHook;
            this->post_varReadHook_data = data;
        }

        void s_pre_varWriteHook(void (* pre_varWriteHook) (Machine * machine,
                                                   const MachineVariable & machineVariable,
                                                   void * data),
                                void * data) {
            this->pre_varWriteHook = pre_varWriteHook;
            this->pre_varWriteHook_data = data;
        }

        void s_post_varWriteHook(void (* post_varWriteHook) (Machine * machine,
                                                   const MachineVariable & machineVariable,
                                                   void * data),
                                 void * data) {
            this->post_varWriteHook = post_varWriteHook;
            this->post_varWriteHook_data = data;
        }

        void s_pre_instructionHook(void (* pre_instructionHook) (Machine * machine,
                                                    const Instruction * instruction,
                                                    void * data),
                                   void * data) {
            this->pre_instructionHook = pre_instructionHook;
            this->pre_instructionHook_data = data;
        }

        void s_post_instructionHook(void (* post_instructionHook) (Machine * machine,
                                                    const Instruction * instruction,
                                                    void * data),
                                    void * data) {
            this->post_instructionHook = post_instructionHook;
            this->post_instructionHook_data = data;
        }
};

#endif