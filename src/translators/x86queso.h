#ifndef quesoX86_HEADER
#define quesoX86_HEADER

#include "queso/queso.h"
#include "translator.h"

#include <cstring>
#include <udis86.h>

class InstructionX86 : public Instruction {
    private :
        std::string text;
        unsigned char * bytes;
        size_t size;
    public :
        InstructionX86 (const std::string & text,
                        const unsigned char * bytes,
                        size_t size)
            : Instruction (), text (text) {
                this->bytes = new unsigned char [size];
                memcpy(this->bytes, bytes, size);
                this->size = size;
            }

        InstructionX86 (const std::string & text,
                        const unsigned char * bytes,
                        size_t size,
                        uint64_t pc)
            : Instruction (pc), text (text) {
                this->bytes = new unsigned char [size];
                memcpy(this->bytes, bytes, size);
                this->size = size;
            }

        ~InstructionX86 () {
            delete[] bytes;
        }

        const unsigned char * g_bytes () { return bytes; }
        size_t g_size () { return size; }

        const std::string queso () const { return text; }

        void pdi (Instruction * ins) { push_depth_instruction(ins); }

        InstructionX86 * copy () {
            InstructionX86 * newIns;
            if (g_pc_set())
                newIns = new InstructionX86(text, bytes, size, g_pc());
            else
                newIns = new InstructionX86(text, bytes, size);
            newIns->copy_depth_instructions(this);
            return newIns;
        }
};

class QuesoX86 : public Translator {
    private :
        InstructionX86 * ix86;
        ud_t ud_obj;

        Variable  getRegister  (unsigned int reg);
        Constant  operand_lval (unsigned int bits, ud_operand operand);
        Operand * sib          (ud_operand operand);
        Operand * operandGet   (unsigned int place);
        void      operandSet   (unsigned int place, Operand * value);

        bool cmovcc (const Operand * condition);
        bool cmovcc (const Operand & condition) {
            return cmovcc(&condition);
        }

        bool jcc (const Operand * condition);
        bool jcc (const Operand & condition) {
            return jcc(&condition);
        }

        bool add ();
        bool And ();
        bool call ();
        bool cmova ();
        bool cmovb ();
        bool cmovbe ();
        bool cmovnz ();
        bool cmovs ();
        bool cmovz ();
        bool cmp ();
        bool cwde ();
        bool dec ();
        bool inc ();
        bool ja ();
        bool jae ();
        bool jb ();
        bool jbe ();
        bool jg ();
        bool jge ();
        bool jl ();
        bool jle ();
        bool jmp ();
        bool jns ();
        bool jnz ();
        bool js ();
        bool jz ();
        bool lea ();
        bool leave ();
        bool mov ();
        bool movd ();
        bool movsd ();
        bool movzx ();
        bool nop ();
        bool Not ();
        bool Or ();
        bool pop ();
        bool push ();
        bool ret ();
        bool shr ();
        bool sub ();
        bool test ();
        bool Xor ();

        Instruction * translate (const uint8_t * data,
                                 size_t size,
                                 uint64_t pc,
                                 bool set_pc);

    public :
        QuesoX86 () {ix86 = NULL;}
        Instruction * translate (const uint8_t * data, size_t size);
        Instruction * translate (const uint8_t * data, size_t size, uint64_t pc);
};

#endif