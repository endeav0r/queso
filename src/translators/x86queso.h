#ifndef quesoX86_HEADER
#define quesoX86_HEADER

#include "queso/queso.h"
#include "translator.h"

#include <cstring>
#include <jansson.h>
#include <sstream>
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

        virtual ~InstructionX86 () {
            delete[] bytes;
        }

        const unsigned char * g_bytes () { return bytes; }
        size_t g_size () { return size; }

        const std::string queso () const {
            std::stringstream ss;
            ss << std::hex << g_pc() << " " << text;
            return ss.str();
        }

        void pdi (Instruction * ins) { push_depth_instruction(ins); }

        InstructionX86 * copy () const {
            InstructionX86 * newIns;
            if (g_pc_set())
                newIns = new InstructionX86(text, bytes, size, g_pc());
            else
                newIns = new InstructionX86(text, bytes, size);
            newIns->copy_depth_instructions(this);
            return newIns;
        }

        const std::string smtlib2 () const {
            char tmp[128];
            snprintf(tmp, 128, "; %llx %s",
                     (unsigned long long) g_pc(),
                     text.c_str());
            return tmp;
        }

        json_t * json () const {
            json_t * json = Instruction::json();

            json_object_set(json, "instruction", json_string("x86"));
            json_object_set(json, "text", json_string(text.c_str()));

            return json;
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

        bool rep ();
        bool repe ();
        bool repne ();

        bool cmovcc (const Operand * condition);
        bool cmovcc (const Operand & condition) {
            return cmovcc(&condition);
        }

        bool jcc (const Operand * condition);
        bool jcc (const Operand & condition) {
            return jcc(&condition);
        }

        bool adc ();
        bool add ();
        bool And ();
        bool bsf ();
        bool call ();
        bool cld ();
        bool cmova ();
        bool cmovb ();
        bool cmovbe ();
        bool cmovnz ();
        bool cmovs ();
        bool cmovz ();
        bool cmp ();
        bool cmpsb ();
        bool cwde ();
        bool dec ();
        bool div ();
        bool inc ();
        bool imul ();
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
        bool movsb ();
        bool movsd ();
        bool movsx ();
        bool movzx ();
        bool mul ();
        bool neg ();
        bool nop ();
        bool Not ();
        bool Or ();
        bool pop ();
        bool push ();
        bool ret ();
        bool sar ();
        bool sbb ();
        bool scasb ();
        bool setnz ();
        bool setz ();
        bool shl ();
        bool shr ();
        bool stosb ();
        bool stosd ();
        bool sub ();
        bool test ();
        bool Xor ();

        InstructionX86 * translate (const uint8_t * data,
                                    size_t size,
                                    uint64_t pc,
                                    bool set_pc);

    public :
        QuesoX86 () {ix86 = NULL;}
        ~QuesoX86 () {
            if (ix86 != NULL)
                delete ix86;
        }

        // this instruction will be freed next time translate is called
        // user must copy result if they want to store it
        InstructionX86 * translate (const uint8_t * data, size_t size);
        InstructionX86 * translate (const uint8_t * data, size_t size, uint64_t pc);
};

#endif