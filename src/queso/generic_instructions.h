#ifndef generic_instructions_HEADER
#define generic_instructions_HEADER

#include "queso.h"
#include <jansson.h>


class InstructionBlock : public Instruction {
    public :
        virtual ~InstructionBlock () {}

        const std::string queso () const { return "BLOCK"; }
        InstructionBlock * copy () const;

        json_t * json () const;
};


class InstructionPhi : public Instruction {
    private :
        Operand * dst;
        std::list <Operand *> src;

    public :
        InstructionPhi (const Operand * dst);
        virtual ~InstructionPhi ();

        void add_src (const Operand * operand);

        void set_src (const std::list <Operand *> operands) {
            clear_src();
            std::list <Operand *> :: const_iterator it;
            for (it = operands.begin(); it != operands.end(); it++) {
                add_src(*it);
            }
        }

        void clear_src () {
            std::list <Operand *> :: iterator it;
            for (it = src.begin(); it != src.end(); it++)
                delete *it;
            src.clear();
        }

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso () const;

        InstructionPhi * copy () const;

        const std::string smtlib2 () const;

        json_t * json () const;
};


class InstructionLoadLE16 : public Instruction {
    private :
        Variable * dst;
        Array * memory;
        Operand * address;

        void init();

    public :
        InstructionLoadLE16 (const Variable & dst,
                             const Array & memory,
                             const Operand & address);

        InstructionLoadLE16 (const Variable * dst,
                             const Array * memory,
                             const Operand * address);
        
        virtual ~InstructionLoadLE16 ();
        
        const std::string queso () const;

        InstructionLoadLE16 * copy () const;

        json_t * json () const;
};

class InstructionLoadLE32 : public Instruction {
    private :
        Variable * dst;
        Array * memory;
        Operand * address;

        void init();

    public :
        InstructionLoadLE32 (const Variable & dst,
                             const Array & memory,
                             const Operand & address);
        
        InstructionLoadLE32 (const Variable * dst,
                             const Array * memory,
                             const Operand * address);

        const Variable * g_dst     () { return dst; }
        const Array *    g_memory  () { return memory; }
        const Operand *  g_address () { return address; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        void s_memory (const Array * memory) {
            delete this->memory;
            this->memory = memory->copy();
        }

        void s_address (const Operand * address) {
            delete this->address;
            this->address = address->copy();
        }

        void s_dst     (const Variable & dst)    { s_dst(&dst); }
        void s_memory  (const Array & memory)    { s_memory(&memory); }
        void s_address (const Operand & address) { s_address(&address); }

        virtual ~InstructionLoadLE32 ();

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso () const;

        InstructionLoadLE32 * copy () const;

        const std::string smtlib2 () const;

        json_t * json () const;
};

class InstructionStoreLE16 : public Instruction {
    private :
        Array * memory;
        Operand * address;
        Operand * value;

        void init ();

    public :
        InstructionStoreLE16 (const Array & memory,
                              const Operand & address,
                              const Operand & value);
        InstructionStoreLE16 (const Array * memory,
                              const Operand * address,
                              const Operand * value);
        virtual ~InstructionStoreLE16 ();

        const std::string queso () const;

        InstructionStoreLE16 * copy () const;

        json_t * json () const;
};

class InstructionStoreLE32 : public Instruction {
    private :
        Array * mem_dst;
        Array * memory;
        Operand * address;
        Operand * value;

        void init();

    public :
        InstructionStoreLE32 (const Array & memory,
                              const Operand & address,
                              const Operand & value);
        InstructionStoreLE32 (const Array * memory,
                              const Operand * address,
                              const Operand * value);
        virtual ~InstructionStoreLE32 ();

        const Array *   g_mem_dst () { return mem_dst; }
        const Array *   g_memory  () { return memory; }
        const Operand * g_address () { return address; }
        const Operand * g_value   () { return value; }

        void s_mem_dst (const Array * mem_dst) {
            delete this->mem_dst;
            this->mem_dst = mem_dst->copy();
        }

        void s_memory (const Array * memory) {
            delete this->memory;
            this->memory = memory->copy();
        }

        void s_address (const Operand * address) {
            delete this->address;
            this->address = address->copy();
        }

        void s_value (const Operand * value) {
            delete this->value;
            this->value = value->copy();
        }

        void s_mem_dst (const Array & mem_dst)   { s_mem_dst(&mem_dst); }
        void s_memory  (const Array & memory)    { s_memory(&memory); }
        void s_address (const Operand & address) { s_address(&address); }
        void s_value   (const Operand & value)   { s_value(&value); }

        Operand * operand_written () { return mem_dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso () const;

        InstructionStoreLE32 * copy () const;

        const std::string smtlib2 () const;

        json_t * json () const;
};

#endif