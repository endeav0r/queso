#ifndef quesoX86_HEADER
#define quesoX86_HEADER

#include "queso.h"

#include <udis86.h>

class InstructionX86 : public Instruction {
    private :
        std::string text;
    public :
        InstructionX86 (const std::string & text)
            : Instruction (), text (text) {}

        std::string queso   () { return text; }

        void pdi (Instruction * ins) { push_depth_instruction(ins); }
};

class QuesoX86 {
    private :
        InstructionX86 * ix86;
        ud_t ud_obj;
        uint64_t address;

        Variable  getRegister  (unsigned int reg);
        Constant  operand_lval (unsigned int bits, ud_operand operand);
        Operand * sib          (ud_operand operand);
        Operand * operandGet   (unsigned int place);
        void      operandSet   (unsigned int place, Operand * value);

        bool cmovcc (const Operand * condition);
        bool cmovcc (const Operand & condition) {
            return cmovcc(&condition);
        }

        bool add ();
        bool And ();
        bool cmova ();
        bool cmovb ();
        bool cmovbe ();
        bool cmovnz ();
        bool cmovs ();
        bool cmovz ();
        bool cmp ();
        bool cwde ();
    public :
        QuesoX86 () {ix86 = NULL;}
        Instruction * translate (const uint8_t * data, size_t size, uint64_t address);
};

#endif