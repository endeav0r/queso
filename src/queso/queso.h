#ifndef instruction_HEADER
#define instruction_HEADER

#include <list>
#include <string>

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
    UMOD,
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

class Operand {
    protected :
        unsigned int bits;
        unsigned int ssa;
    public :
        Operand (unsigned int bits)
            : bits (bits), ssa (0) {}
        virtual ~Operand () {}

        unsigned int g_bits () { return bits; }
        unsigned int g_ssa  () { return ssa; }
        void s_ssa (unsigned int ssa) { this->ssa = ssa; }

        virtual std::string smtlib2             () = 0;
        virtual std::string smtlib2_declaration () = 0;
        virtual std::string queso               () = 0;
        virtual OperandType g_type              () = 0;
        virtual Operand *   copy                () const = 0;
};

class Variable : public Operand {
    private :
        std::string name;
    public :
        Variable (unsigned int bits, const std::string & name)
            : Operand (bits), name (name) {}

        OperandType g_type () { return VARIABLE; }

        const std::string & g_name () { return name; }
        Variable * copy () const;

        std::string smtlib2 ();
        std::string smtlib2_declaration ();
        std::string queso ();
};

class Array : public Operand {
    private :
        std::string name;
        unsigned int address_bits;
    public :
        Array (unsigned int bits, const std::string & name, unsigned int address_bits)
            : Operand (bits), name (name), address_bits (address_bits) {}

        OperandType g_type () { return ARRAY; }

        const std::string & g_name () { return name; }
        unsigned int g_address_bits () { return address_bits; }
        Array * copy () const;

        std::string smtlib2 ();
        std::string smtlib2_declaration ();
        std::string queso ();
};

class Constant : public Operand {
    private :
        uint64_t value;
    public :
        Constant (unsigned int bits, uint64_t value)
            : Operand (bits), value (value) {}

        OperandType g_type () { return CONSTANT; }

        uint64_t g_value () { return value; }
        Constant * copy () const;

        std::string smtlib2 ();
        std::string smtlib2_declaration ();
        std::string queso ();
};

class Instruction {
    private :
        uint64_t pc;
        bool pc_set;
        std::list <Instruction *> depth_instructions;
        QuesoOpcode opcode;
    protected :
        void copy_depth_instructions (const Instruction * srcInstruction);
    public :
        Instruction (uint64_t pc)
            : pc (pc), pc_set (false), opcode (USER) {}
        Instruction ()
            : pc_set (false), opcode (USER) {}
        Instruction (uint64_t pc, QuesoOpcode opcode)
            : pc (pc), pc_set (true), opcode (opcode) {}
        Instruction (QuesoOpcode opcode)
            : pc_set (false), opcode (opcode) {}

        virtual ~Instruction () {
            std::list <Instruction *> ::iterator it;
            for (it = depth_instructions.begin(); it != depth_instructions.end(); it++)
                delete *it;
        };

        bool        g_pc_set () { return pc_set; }
        uint64_t    g_pc     () { return pc; }
        QuesoOpcode g_opcode () { return opcode; }

        const std::list <Instruction *> & g_depth_instructions () const;
        void push_depth_instruction (Instruction * instruction);
        
        virtual const Operand * operand_written () { return NULL; }
        virtual const std::list <Operand *> operands_read () { return std::list <Operand *>(); }
        virtual const std::list <Operand *> operands () { return std::list <Operand *>(); }
        
        virtual const std::string smtlib2 () { return ""; }
        virtual const std::string queso   () = 0;

        virtual Instruction * copy () = 0;
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

        const Variable * g_dst () { return dst; }
        const Operand  * g_src () { return src; }

        const Operand * operand_written () { return dst; }
        const std::list <Operand *> operands_read ();
        const std::list <Operand *> operands ();

        const std::string smtlib2 ();
        const std::string queso   ();

        InstructionAssign * copy ();
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

        const Operand * operand_written () { return dstmem; }
        const std::list <Operand *> operands_read ();
        const std::list <Operand *> operands ();

        const std::string queso ();
        const std::string smtlib2 ();

        InstructionStore * copy ();
};

class InstructionLoad : public Instruction {
    private :
        Variable * dst;
        Array *    mem;
        Operand *  address;
    public :
        InstructionLoad (const Variable * dst, const Array * mem, const Operand * address);
        ~InstructionLoad ();

        const Operand * operand_written () { return dst; }
        const std::list <Operand *> operands_read ();
        const std::list <Operand *> operands ();

        const std::string queso ();
        const std::string smtlib2 ();

        InstructionLoad * copy ();
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

        const Operand * operand_written () { return dst; }
        const std::list <Operand *> operands_read ();
        const std::list <Operand *> operands ();

        const std::string queso ();
        const std::string smtlib2 ();

        InstructionIte * copy ();
};

class InstructionSignExtend : public Instruction {
    private :
        Variable * dst;
        Operand  * src;
    public :
        InstructionSignExtend (const Variable * dst, const Operand * src);
        InstructionSignExtend (const Variable & dst, const Operand & src);
        ~InstructionSignExtend ();

        const Operand * operand_written () { return dst; }
        const std::list <Operand *> operands_read ();
        const std::list <Operand *> operands ();

        const std::string queso ();
        const std::string smtlib2 ();

        InstructionSignExtend * copy ();
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
        ~InstructionArithmetic();

        const Operand * operand_written () { return dst; }
        const std::list <Operand *> operands_read ();
        const std::list <Operand *> operands ();

        const std::string queso ();
        const std::string smtlib2 ();
};

class InstructionAdd : public InstructionArithmetic {
    public :
        InstructionAdd (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (ADD, "bvadd", dst, lhs, rhs) {}
        InstructionAdd (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (ADD, "bvadd", dst, lhs, rhs) {}

        InstructionAdd * copy () { return new InstructionAdd(dst, lhs, rhs); }
};

class InstructionSub : public InstructionArithmetic {
    public :
        InstructionSub (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (SUB, "bvsub", dst, lhs, rhs) {}
        InstructionSub (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (SUB, "bvsub", dst, lhs, rhs) {}

        InstructionSub * copy () { return new InstructionSub(dst, lhs, rhs); }
};

class InstructionMul : public InstructionArithmetic {
    public :
        InstructionMul (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (MUL, "bvmul", dst, lhs, rhs) {}
        InstructionMul (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (MUL, "bvmul", dst, lhs, rhs) {}

        InstructionMul * copy () { return new InstructionMul(dst, lhs, rhs); }
};

class InstructionUdiv : public InstructionArithmetic {
    public :
        InstructionUdiv (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (UDIV, "bvudiv", dst, lhs, rhs) {}
        InstructionUdiv (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (UDIV, "bvudiv", dst, lhs, rhs) {}

        InstructionUdiv * copy () { return new InstructionUdiv(dst, lhs, rhs); }
};

class InstructionUmod : public InstructionArithmetic {
    public :
        InstructionUmod (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (UMOD, "bvumod", dst, lhs, rhs) {}
        InstructionUmod (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (UMOD, "bvumod", dst, lhs, rhs) {}

        InstructionUmod * copy () { return new InstructionUmod(dst, lhs, rhs); }
};

class InstructionAnd : public InstructionArithmetic {
    public :
        InstructionAnd (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (AND, "bvand", dst, lhs, rhs) {}
        InstructionAnd (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (AND, "bvand", dst, lhs, rhs) {}

        InstructionAnd * copy () { return new InstructionAnd(dst, lhs, rhs); }
};

class InstructionOr : public InstructionArithmetic {
    public :
        InstructionOr (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (OR, "bvor", dst, lhs, rhs) {}
        InstructionOr (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (OR, "bvor", dst, lhs, rhs) {}

        InstructionOr * copy () { return new InstructionOr(dst, lhs, rhs); }
};

class InstructionXor : public InstructionArithmetic {
    public :
        InstructionXor (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (XOR, "bvxor", dst, lhs, rhs) {}
        InstructionXor (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (XOR, "bvxor", dst, lhs, rhs) {}

        InstructionXor * copy () { return new InstructionXor(dst, lhs, rhs); }
};

class InstructionShl : public InstructionArithmetic {
    public :
        InstructionShl (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (SHL, "bvshl", dst, lhs, rhs) {}
        InstructionShl (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (SHL, "bvshl", dst, lhs, rhs) {}

        InstructionShl * copy () { return new InstructionShl(dst, lhs, rhs); }
};

class InstructionShr : public InstructionArithmetic {
    public :
        InstructionShr (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionArithmetic (SHR, "bvlshr", dst, lhs, rhs) {}
        InstructionShr (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionArithmetic (SHR, "bvlshr", dst, lhs, rhs) {}

        InstructionShr * copy () { return new InstructionShr(dst, lhs, rhs); }
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

        const Operand * operand_written () { return dst; }
        const std::list <Operand *> operands_read ();
        const std::list <Operand *> operands ();

        const std::string queso ();
        const std::string smtlib2 ();
};

class InstructionCmpEq : public InstructionCmp {
    public :
        InstructionCmpEq (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPEQ, "=", dst, lhs, rhs) {}
        InstructionCmpEq (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPEQ, "=", dst, lhs, rhs) {}

        InstructionCmpEq * copy () { return new InstructionCmpEq(dst, lhs, rhs); }
};

class InstructionCmpLtu : public InstructionCmp {
    public :
        InstructionCmpLtu (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLTU, "bvlt", dst, lhs, rhs) {}
        InstructionCmpLtu (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLTU, "bvlt", dst, lhs, rhs) {}

        InstructionCmpLtu * copy () { return new InstructionCmpLtu(dst, lhs, rhs); }
};

class InstructionCmpLeu : public InstructionCmp {
    public :
        InstructionCmpLeu (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLEU, "bvle", dst, lhs, rhs) {}
        InstructionCmpLeu (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLEU, "bvle", dst, lhs, rhs) {}

        InstructionCmpLeu * copy () { return new InstructionCmpLeu(dst, lhs, rhs); }
};

class InstructionCmpLts : public InstructionCmp {
    public :
        InstructionCmpLts (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLTS, "sbvlt", dst, lhs, rhs) {}
        InstructionCmpLts (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLTS, "sbvlt", dst, lhs, rhs) {}

        InstructionCmpLts * copy () { return new InstructionCmpLts(dst, lhs, rhs); }
};

class InstructionCmpLes : public InstructionCmp {
    public :
        InstructionCmpLes (const Variable & dst, const Operand & lhs, const Operand & rhs)
            : InstructionCmp (CMPLES, "sbvle", dst, lhs, rhs) {}
        InstructionCmpLes (const Variable * dst, const Operand * lhs, const Operand * rhs)
            : InstructionCmp (CMPLES, "sbvle", dst, lhs, rhs) {}

        InstructionCmpLes * copy () { return new InstructionCmpLes(dst, lhs, rhs); }
};

#endif