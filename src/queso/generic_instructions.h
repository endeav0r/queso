#ifndef generic_instructions_HEADER
#define generic_instructions_HEADER

#include "queso.h"


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
            for (it = operands.begin(); it != operands.end(); it++)
                add_src((*it)->copy());
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

        virtual ~InstructionLoadLE32 ();

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso () const;

        InstructionLoadLE32 * copy () const;

        const std::string smtlib2 () const;
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

        Operand * operand_written () { return mem_dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso () const;

        InstructionStoreLE32 * copy () const;

        const std::string smtlib2 () const;
};

#endif