#ifndef generic_instructions_HEADER
#define generic_instructions_HEADER

#include "queso.h"

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
        
        ~InstructionLoadLE16 ();
        
        const std::string queso ();

        InstructionLoadLE16 * copy ();
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
        
        ~InstructionLoadLE32 ();

        const std::string queso ();

        InstructionLoadLE32 * copy ();
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
        ~InstructionStoreLE16 ();

        const std::string queso ();

        InstructionStoreLE16 * copy ();
};

class InstructionStoreLE32 : public Instruction {
    private :
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
        ~InstructionStoreLE32 ();

        const std::string queso ();

        InstructionStoreLE32 * copy ();
};

#endif