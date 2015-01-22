#ifndef instruction_HEADER
#define instruction_HEADER

#include <stdexcept>
#include <inttypes.h>
#include <list>
#include <set>
#include <string>
#include <jansson.h>
#include "graph/graph.h"

enum OperandType { VARIABLE, CONSTANT, ARRAY };

enum QuesoOpcode {
    ASSIGN = 0,
    STORE,
    LOAD,
    ITE,
    SEXT,
    ADD,
    SUB,
    MUL,
    UDIV,
    UREM,
    AND,
    OR,
    XOR,
    SHL,
    SHR,
    CMPEQ,
    CMPLTU,
    CMPLEU,
    CMPLTS,
    CMPLES,
    USER
};

extern const char * QuesoOpcodeStrings [];

extern std::string operandEmptyString;

class Operand {
    protected :
        unsigned int bits;
        uint64_t ssa;
    public :
        Operand (unsigned int bits)
            : bits (bits), ssa (0) {}
        virtual ~Operand () {}

        unsigned int g_bits () const { return bits; }
        uint64_t g_ssa  () const { return ssa; }
        void s_ssa (uint64_t ssa) { this->ssa = ssa; }

        virtual const std::string & g_name () const { return operandEmptyString; }

        virtual std::string smtlib2             () const = 0;
        virtual std::string smtlib2_declaration () const = 0;
        virtual std::string queso               () const = 0;
        virtual OperandType g_type              () const = 0;
        virtual Operand *   copy                () const = 0;
        virtual json_t *    json                () const = 0;
};

class Variable : public Operand {
    private :
        std::string name;
    public :
        Variable (unsigned int bits, const std::string & name)
            : Operand (bits), name (name) {}

        OperandType g_type () const { return VARIABLE; }

        const std::string & g_name () const { return name; }
        virtual Variable * copy () const;

        virtual std::string smtlib2 () const;
        std::string smtlib2_declaration () const;
        virtual std::string queso () const;
        json_t *    json  () const;
};

class Array : public Operand {
    private :
        std::string name;
        unsigned int address_bits;
    public :
        Array (unsigned int bits, const std::string & name, unsigned int address_bits)
            : Operand (bits), name (name), address_bits (address_bits) {}

        OperandType g_type () const { return ARRAY; }

        const std::string & g_name  () const { return name; }
        unsigned int g_address_bits () const { return address_bits; }
        Array * copy () const;

        std::string smtlib2 () const;
        std::string smtlib2_declaration () const;
        std::string queso () const;
        json_t *    json  () const;
};

class Constant : public Operand {
    private :
        uint64_t value;
    public :
        Constant (unsigned int bits, uint64_t value)
            : Operand (bits), value (value) {}
        Constant ()
            : Operand (0), value (0) {}

        OperandType g_type  () const { return CONSTANT; }
        uint64_t    g_value () const { 
            switch (g_bits()) {
                case 1  : return value & 1;
                case 8  : return (uint8_t)  value;
                case 16 : return (uint16_t) value;
                case 32 : return (uint32_t) value;
                case 64 : return (uint64_t) value;
                default :
                    throw std::runtime_error("invalid Constant width");
                    return 0;
            }
        }

        Constant * copy () const;

        std::string smtlib2 () const;
        std::string smtlib2_declaration () const;
        std::string queso () const;
        json_t *    json  () const;
};

class Instruction : public GraphVertex {
    private :
        uint64_t pc;
        bool pc_set;
        std::list <Instruction *> depth_instructions;
        QuesoOpcode opcode;

        void var_dominators (std::list <std::string> & dominator_variables,
                             std::list <Instruction *> & dominator_instructions);

        void depthSmtlib2Declarations (std::stringstream & ss);
        void depthSmtlib2             (std::stringstream & ss);

        std::list <Instruction *> flattened;
    protected :
        void copy_depth_instructions (const Instruction * srcInstruction);
    public :
        Instruction (uint64_t pc)
            : pc (pc), pc_set (true), opcode (USER) {}
        Instruction ()
            : pc_set (false), opcode (USER) {}
        Instruction (uint64_t pc, QuesoOpcode opcode)
            : pc (pc), pc_set (true), opcode (opcode) {}
        Instruction (QuesoOpcode opcode)
            : pc_set (false), opcode (opcode) {}

        virtual ~Instruction () {
            std::list <Instruction *> ::iterator it;
            for (it = depth_instructions.begin(); it != depth_instructions.end(); it++) {
                delete *it;
            }
        };

        void s_pc (uint64_t pc) { this->pc = pc; }
        bool        g_pc_set () const { return pc_set; }
        uint64_t    g_pc     () const { return pc; }
        QuesoOpcode g_opcode () const { return opcode; }

        std::list <Instruction *> & g_depth_instructions ();
        void push_depth_instruction    (Instruction * instruction);
        bool remove_depth_instruction  (Instruction * instruction);
        bool replace_depth_instruction (Instruction * oldInstruction,
                                        Instruction * newInstruction);
        void remove_depth_instructions  (std::set <Instruction *> instructions);
        bool remove_depth_instructions_ (std::set <Instruction *> & instructions);
        
        virtual Operand * operand_written () { return NULL; }
        virtual std::list <Operand *> operands_read () { return std::list <Operand *>(); }
        virtual std::list <Operand *> operands () { return std::list <Operand *>(); }

        std::list <Instruction *> var_dominators (std::string name);

        std::list <Instruction *> & flatten ();
        
        virtual const std::string smtlib2 () const { return ""; }
        virtual const std::string queso   () const = 0;

        virtual Instruction * copy () const = 0;

        std::string depthSmtlib2Declarations ();
        std::string depthSmtlib2 ();

        virtual json_t * json () const;
};

class InstructionAssign : public Instruction {
    private :
        Variable * dst;
        Operand * src;
    public :
        InstructionAssign (const Variable * dst, const Operand * src)
            : Instruction (ASSIGN), dst (dst->copy()), src (src->copy()) {}
        InstructionAssign (const Variable & dst, const Operand & src)
            : Instruction (ASSIGN), dst (dst.copy()), src (src.copy()) {}
        ~InstructionAssign ();

        const Variable * g_dst () const { return dst; }
        const Operand  * g_src () const { return src; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        void s_src (const Operand * src) {
            delete this->src;
            this->src = src->copy();
        }

        inline void s_dst (const Variable & dst) { s_dst(&dst); }
        inline void s_src (const Operand & src) { s_src(&src); }

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string smtlib2 () const;
        const std::string queso   () const;

        InstructionAssign * copy () const;

        json_t * json () const;
};

class InstructionStore : public Instruction {
    private :
        Array * dstmem;
        Array * srcmem;
        Operand * address;
        Operand * value;
    public :
        InstructionStore (const Array *   mem,
                          const Operand * address,
                          const Operand * value);

        InstructionStore (const Array *   dstmem,
                          const Array *   srcmem,
                          const Operand * address,
                          const Operand * value);
        ~InstructionStore ();

        const Array *   g_dstmem  () const { return dstmem; }
        const Array *   g_srcmem  () const { return srcmem; }
        const Operand * g_address () const { return address; }
        const Operand * g_value   () const { return value; }

        void s_dstmem (const Array * dstmem) {
            delete this->dstmem;
            this->dstmem = dstmem->copy();
        }

        void s_srcmem (const Array * srcmem) {
            delete this->srcmem;
            this->srcmem = srcmem->copy();
        }

        void s_address (const Operand * address) {
            delete this->address;
            this->address = address->copy();
        }

        void s_value (const Operand * value) {
            delete this->value;
            this->value = value->copy();
        }

        inline void s_dstmem (const Array & dstmem) { s_dstmem(&dstmem); }
        inline void s_srcmem (const Array & srcmem) { s_srcmem(&srcmem); }
        inline void s_address (const Operand & address) { s_address(&address); }
        inline void s_value (const Operand & value) { s_value(&value); }

        Operand * operand_written () { return dstmem; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso   () const;
        const std::string smtlib2 () const;

        InstructionStore * copy () const;

        json_t * json () const;
};

class InstructionLoad : public Instruction {
    private :
        Variable * dst;
        Array *    mem;
        Operand *  address;
    public :
        InstructionLoad (const Variable * dst, const Array * mem, const Operand * address);
        ~InstructionLoad ();

        const Variable * g_dst     () const { return dst; }
        const Array *    g_mem     () const { return mem; }
        const Operand *  g_address () const { return address; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        void s_mem (const Array * mem) {
            delete this->mem;
            this->mem = mem->copy();
        }

        void s_address (const Operand * address) { 
            delete this->address;
            this->address = address->copy();
        }

        inline void s_dst (const Variable & dst) { s_dst(&dst); }
        inline void s_mem (const Array & mem) { s_mem(&mem); }
        inline void s_address (const Operand & address) { s_address(&address); }

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso   () const;
        const std::string smtlib2 () const;

        InstructionLoad * copy () const;
        
        json_t * json () const;
};

class InstructionIte : public Instruction {
    private :
        Variable * dst;
        Operand * condition;
        Operand * t;
        Operand * e;
    public :
        InstructionIte (const Variable * dst,
                        const Operand * condition,
                        const Operand * t,
                        const Operand * e);
        ~InstructionIte ();

        const Variable * g_dst ()       const { return dst; }
        const Operand  * g_condition () const { return condition; }
        const Operand  * g_t ()         const { return t; }
        const Operand  * g_e ()         const { return e; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        void s_condition (const Operand * condition) {
            delete this->condition;
            this->condition = condition->copy();
        }

        void s_t (const Operand * t) {
            delete this->t;
            this->t = t->copy();
        }

        void s_e (const Operand * e) {
            delete this->e;
            this->e = e->copy();
        }

        inline void s_dst (const Variable & dst) { s_dst(&dst); }
        inline void s_condition (const Operand & condition) { s_condition(&condition); }
        inline void s_t (const Operand & t) { s_t(&t); }
        inline void s_e (const Operand & e) { s_e(&e); }

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso   () const;
        const std::string smtlib2 () const;

        InstructionIte * copy () const;
        
        json_t * json () const;
};

class InstructionSignExtend : public Instruction {
    private :
        Variable * dst;
        Operand  * src;
    public :
        InstructionSignExtend (const Variable * dst, const Operand * src);
        InstructionSignExtend (const Variable & dst, const Operand & src);
        ~InstructionSignExtend ();

        const Variable * g_dst () const { return dst; }
        const Operand  * g_src () const { return src; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        void s_src (const Operand * src) {
            delete this->src;
            this->src = src->copy();
        }

        inline void s_dst (const Variable & dst) { s_dst(&dst); }
        inline void s_src (const Operand & src) { s_src(&src); }

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso   () const;
        const std::string smtlib2 () const;

        InstructionSignExtend * copy () const;
        
        json_t * json () const;
};

class InstructionArithmetic : public Instruction {
    private :
        std::string bvop;
    protected :
        Variable * dst;
        Operand *  lhs;
        Operand *  rhs;
    public :
        InstructionArithmetic (QuesoOpcode opcode,
                               const std::string & bvop,
                               const Variable * dst,
                               const Operand *  lhs,
                               const Operand *  rhs);
        InstructionArithmetic (QuesoOpcode opcode,
                               const std::string & bvop,
                               const Variable & dst,
                               const Operand &  lhs,
                               const Operand &  rhs);
        virtual ~InstructionArithmetic();

        const Variable * g_dst () const { return dst; }
        const Operand  * g_lhs () const { return lhs; }
        const Operand  * g_rhs () const { return rhs; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        void s_lhs (const Operand * lhs) {
            delete this->lhs;
            this->lhs = lhs->copy();
        }

        void s_rhs (const Operand * rhs) {
            delete this->rhs;
            this->rhs = rhs->copy();
        }

        inline void s_dst (const Variable & dst) { s_dst(&dst); }
        inline void s_lhs (const Operand & lhs) { s_lhs(&lhs); }
        inline void s_rhs (const Operand & rhs) { s_rhs(&rhs); }

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso   () const;
        const std::string smtlib2 () const;
        
        json_t * json () const;
};

class InstructionAdd : public InstructionArithmetic {
    public :
        InstructionAdd (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (ADD, "bvadd", dst, lhs, rhs) {}
        InstructionAdd (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (ADD, "bvadd", dst, lhs, rhs) {}

        InstructionAdd * copy () const { return new InstructionAdd(dst, lhs, rhs); }
};

class InstructionSub : public InstructionArithmetic {
    public :
        InstructionSub (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (SUB, "bvsub", dst, lhs, rhs) {}
        InstructionSub (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (SUB, "bvsub", dst, lhs, rhs) {}

        InstructionSub * copy () const { return new InstructionSub(dst, lhs, rhs); }
};

class InstructionMul : public InstructionArithmetic {
    public :
        InstructionMul (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (MUL, "bvmul", dst, lhs, rhs) {}
        InstructionMul (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (MUL, "bvmul", dst, lhs, rhs) {}

        InstructionMul * copy () const { return new InstructionMul(dst, lhs, rhs); }
};

class InstructionUdiv : public InstructionArithmetic {
    public :
        InstructionUdiv (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (UDIV, "bvudiv", dst, lhs, rhs) {}
        InstructionUdiv (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (UDIV, "bvudiv", dst, lhs, rhs) {}

        InstructionUdiv * copy () const { return new InstructionUdiv(dst, lhs, rhs); }
};

class InstructionUrem : public InstructionArithmetic {
    public :
        InstructionUrem (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (UREM, "bvurem", dst, lhs, rhs) {}
        InstructionUrem (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (UREM, "bvurem", dst, lhs, rhs) {}

        InstructionUrem * copy () const { return new InstructionUrem(dst, lhs, rhs); }
};

class InstructionAnd : public InstructionArithmetic {
    public :
        InstructionAnd (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (AND, "bvand", dst, lhs, rhs) {}
        InstructionAnd (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (AND, "bvand", dst, lhs, rhs) {}

        InstructionAnd * copy () const { return new InstructionAnd(dst, lhs, rhs); }
};

class InstructionOr : public InstructionArithmetic {
    public :
        InstructionOr (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (OR, "bvor", dst, lhs, rhs) {}
        InstructionOr (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (OR, "bvor", dst, lhs, rhs) {}

        InstructionOr * copy () const { return new InstructionOr(dst, lhs, rhs); }
};

class InstructionXor : public InstructionArithmetic {
    public :
        InstructionXor (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (XOR, "bvxor", dst, lhs, rhs) {}
        InstructionXor (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (XOR, "bvxor", dst, lhs, rhs) {}

        InstructionXor * copy () const { return new InstructionXor(dst, lhs, rhs); }
};

class InstructionShl : public InstructionArithmetic {
    public :
        InstructionShl (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (SHL, "bvshl", dst, lhs, rhs) {}
        InstructionShl (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (SHL, "bvshl", dst, lhs, rhs) {}

        InstructionShl * copy () const { return new InstructionShl(dst, lhs, rhs); }
};

class InstructionShr : public InstructionArithmetic {
    public :
        InstructionShr (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (SHR, "bvlshr", dst, lhs, rhs) {}
        InstructionShr (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (SHR, "bvlshr", dst, lhs, rhs) {}

        InstructionShr * copy () const { return new InstructionShr(dst, lhs, rhs); }
};

class InstructionCmp : public Instruction {
    private :
        std::string bvop;
    protected : 
        Variable * dst;
        Operand * lhs;
        Operand * rhs;
    public :
        InstructionCmp (QuesoOpcode opcode,
                        const std::string & bvop,
                        const Variable & dst,
                        const Operand & lhs,
                        const Operand & rhs);
        InstructionCmp (QuesoOpcode opcode,
                        const std::string & bvop,
                        const Variable * dst,
                        const Operand * lhs,
                        const Operand * rhs);
        ~InstructionCmp ();

        const Variable * g_dst () const { return dst; }
        const Operand *  g_lhs () const { return lhs; }
        const Operand *  g_rhs () const { return rhs; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        void s_lhs (const Operand * lhs) {
            delete this->lhs;
            this->lhs = lhs->copy();
        }

        void s_rhs (const Operand * rhs) {
            delete this->rhs;
            this->rhs = rhs->copy();
        }

        inline void s_dst (const Variable & dst) { s_dst(&dst); }
        inline void s_lhs (const Operand & lhs) { s_lhs(&lhs); }
        inline void s_rhs (const Operand & rhs) { s_rhs(&rhs); }

        Operand * operand_written () { return dst; }
        std::list <Operand *> operands_read ();
        std::list <Operand *> operands ();

        const std::string queso   () const;
        const std::string smtlib2 () const;
        
        json_t * json () const;
};

class InstructionCmpEq : public InstructionCmp {
    public :
        InstructionCmpEq (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPEQ, "=", dst, lhs, rhs) {}
        InstructionCmpEq (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPEQ, "=", dst, lhs, rhs) {}

        InstructionCmpEq * copy () const { return new InstructionCmpEq(dst, lhs, rhs); }
};

class InstructionCmpLtu : public InstructionCmp {
    public :
        InstructionCmpLtu (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLTU, "bvult", dst, lhs, rhs) {}
        InstructionCmpLtu (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLTU, "bvult", dst, lhs, rhs) {}

        InstructionCmpLtu * copy () const { return new InstructionCmpLtu(dst, lhs, rhs); }
};

class InstructionCmpLeu : public InstructionCmp {
    public :
        InstructionCmpLeu (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLEU, "bvule", dst, lhs, rhs) {}
        InstructionCmpLeu (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLEU, "bvule", dst, lhs, rhs) {}

        InstructionCmpLeu * copy () const { return new InstructionCmpLeu(dst, lhs, rhs); }
};

class InstructionCmpLts : public InstructionCmp {
    public :
        InstructionCmpLts (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLTS, "bvslt", dst, lhs, rhs) {}
        InstructionCmpLts (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLTS, "bvslt", dst, lhs, rhs) {}

        InstructionCmpLts * copy () const { return new InstructionCmpLts(dst, lhs, rhs); }
};

class InstructionCmpLes : public InstructionCmp {
    public :
        InstructionCmpLes (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLES, "bvsle", dst, lhs, rhs) {}
        InstructionCmpLes (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLES, "bvsle", dst, lhs, rhs) {}

        InstructionCmpLes * copy () const { return new InstructionCmpLes(dst, lhs, rhs); }
};

#endif