#include "queso.h"

#include <sstream>

/*********************************************
* Operand : Variable
**********************************************/

Variable * Variable :: copy () const {
    Variable * nv = new Variable(bits, name);
    nv->ssa = ssa;
    return nv;
}

std::string Variable :: smtlib2 () {
    std::stringstream ss;
    ss << name << "_" << ssa;
    return ss.str();
}

std::string Variable :: smtlib2_declaration () {
    std::stringstream ss;
    ss << "(declare-fun " << smtlib2() << " () (_ BitVec " << bits << "))";
    return ss.str();
}

std::string Variable :: queso () {
    std::stringstream ss;
    ss << bits << ":" << name << "_" << ssa;
    return ss.str();
}

/*********************************************
* Operand : Array
**********************************************/

Array * Array :: copy () const {
    Array * na = new Array(bits, name, address_bits);
    na->ssa = ssa;
    return na;
}

std::string Array :: smtlib2 () {
    std::stringstream ss;
    ss << name << "_" << ssa;
    return ss.str();
}

std::string Array :: smtlib2_declaration () {
    std::stringstream ss;
    ss << "(declare-fun " << smtlib2() << " () (Array (_ BitVec "
       << address_bits << ") (_ BitVec " << bits << ")))";
    return ss.str();
}

std::string Array :: queso () {
    std::stringstream ss;
    ss << "{" << address_bits << "->" << bits << "}" << name << "_" << ssa;
    return ss.str();
}

/*********************************************
* Operand : Constant
**********************************************/

Constant * Constant :: copy () const {
    Constant * nc = new Constant(bits, value);
    nc->ssa = ssa;
    return nc;
}

std::string Constant :: smtlib2 () {
    char tmp[64];

    switch (bits) {
    case 1  : snprintf(tmp, 64, "#b%d", (unsigned int) value); break;
    case 8  : snprintf(tmp, 64, "#x%02x", (unsigned int) value); break;
    case 16 : snprintf(tmp, 64, "#x%04x", (unsigned int) value); break;
    case 32 : snprintf(tmp, 64, "#x%08x", (unsigned int) value); break;
    case 64 : snprintf(tmp, 64, "#x%016llx", (unsigned long long) value); break;
    default : break;
    }

    return tmp;
}

std::string Constant :: smtlib2_declaration () {
    return "";
}

std::string Constant :: queso () {
    std::stringstream ss;
    ss << bits << ":" << std::hex << value;
    return ss.str();
}

/*********************************************
* Instruction
**********************************************/


std::list <Instruction *> Instruction :: g_depth_instructions () {
    return depth_instructions;
}

void Instruction :: push_depth_instruction (Instruction * instruction) {
    depth_instructions.push_back(instruction);
}

/*********************************************
* Instruction : InstructionAssign
**********************************************/

InstructionAssign :: InstructionAssign (const Variable * dst, const Operand * src)
: Instruction (QUESO) {
    this->dst = dst->copy();
    this->src = src->copy();
}


InstructionAssign :: ~InstructionAssign () {
    delete dst;
    delete src;
}


std::list <Operand *> InstructionAssign :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(src);
    return operands;
}


std::list <Operand *> InstructionAssign :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(src);
    return operands;
}


std::string InstructionAssign :: smtlib2 () {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " ";

    if (dst->g_bits() == src->g_bits())
        ss << src->smtlib2();
    else if (dst->g_bits() < src->g_bits())
        ss << "((_ extract " << dst->g_bits() - 1 << " 0) " << src->smtlib2() << ")";
    else if (dst->g_bits() > src->g_bits())
        ss << "(concat (_ bv0 " << (dst->g_bits() - src->g_bits()) << ") " << src->smtlib2() << ")";

    ss << "))";

    return ss.str();
}

std::string InstructionAssign :: queso () {
    std::stringstream ss;
    ss << "assign " << dst->queso() << " " << src->queso();
    return ss.str();
}

/*********************************************
* Instruction : InstructionStore
**********************************************/

InstructionStore :: InstructionStore (const Array * mem,
                                      const Operand * address,
                                      const Operand * value)
: Instruction (QUESO) {
    this->dstmem  = mem->copy();
    this->srcmem  = mem->copy();
    this->address = address->copy();
    this->value   = value->copy();
}


InstructionStore :: InstructionStore (const Array * dstmem,
                                      const Array * srcmem,
                                      const Operand * address,
                                      const Operand * value)
: Instruction (QUESO) {
    this->dstmem  = dstmem->copy();
    this->srcmem  = srcmem->copy();
    this->address = address->copy();
    this->value   = value->copy();
}


InstructionStore :: ~InstructionStore () {
    delete dstmem;
    delete srcmem;
    delete address;
    delete value;
}


std::list <Operand *> InstructionStore :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(srcmem);
    operands.push_back(address);
    operands.push_back(value);
    return operands;
}

std::list <Operand *> InstructionStore :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dstmem);
    operands.push_back(srcmem);
    operands.push_back(address);
    operands.push_back(value);
    return operands;
}

std::string InstructionStore :: smtlib2 () {
    std::stringstream ss;

    ss << "(assert (= " << dstmem->smtlib2() << " (store " << srcmem->smtlib2() << " "
       << address->smtlib2() << " " << value->smtlib2() << ")))";
    
    return ss.str();
}

std::string InstructionStore :: queso () {
    std::stringstream ss;
    ss << "store " << dstmem->queso() << "[" << address->queso() << "] " << value->queso();
    return ss.str();
}

/*********************************************
* Instruction : InstructionLoad
**********************************************/

InstructionLoad :: InstructionLoad (const Variable * dst,
                                    const Array * mem,
                                    const Operand * address)
: Instruction (QUESO) {
    this->dst = dst->copy();
    this->mem = mem->copy();
    this->address = address->copy();
}

InstructionLoad :: ~InstructionLoad () {
    delete dst;
    delete mem;
    delete address;
}

std::list <Operand *> InstructionLoad :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(mem);
    operands.push_back(address);
    return operands;
}

std::list <Operand *> InstructionLoad :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(mem);
    operands.push_back(address);
    return operands;
}

std::string InstructionLoad :: smtlib2 () {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (select " << mem->smtlib2() << " "
       << address->smtlib2() << ")))";
    
    return ss.str();
}

std::string InstructionLoad :: queso () {
    std::stringstream ss;
    ss << "load " << dst->queso() << " " << mem->queso() << "[" << address->queso() << "]";
    return ss.str();
}

/*********************************************
* Instruction : InstructionIte
**********************************************/

InstructionIte :: InstructionIte (const Variable * dst,
                                   const Operand * condition,
                                   const Operand * t,
                                   const Operand * e)
: Instruction (QUESO) {
    this->dst = dst->copy();
    this->condition = condition->copy();
    this->t = t->copy();
    this->e = e->copy();
}

InstructionIte :: ~InstructionIte () {
    delete dst;
    delete condition;
    delete t;
    delete e;
}

std::list <Operand *> InstructionIte :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(condition);
    operands.push_back(t);
    operands.push_back(e);
    return operands;
}

std::list <Operand *> InstructionIte :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(condition);
    operands.push_back(t);
    operands.push_back(e);
    return operands;
}

std::string InstructionIte :: smtlib2 () {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (ite (= " << condition->smtlib2() << " #b1) "
       << t->smtlib2() << " " << e->smtlib2() << ")))";
    
    return ss.str();
}

std::string InstructionIte :: queso () {
    std::stringstream ss;
    ss << "ite " << dst->queso() << " (" << condition->queso()
       << " ? " << t->queso() << " : " << e->queso() << ")";
    return ss.str();
}

/*********************************************
* Instruction : InstructionSignExtend
**********************************************/

InstructionSignExtend :: InstructionSignExtend (const Variable * dst,
                                                const Operand *  src)
: Instruction (QUESO) {
    this->dst = dst->copy();
    this->src = src->copy();
}

InstructionSignExtend :: InstructionSignExtend (const Variable & dst,
                                                const Operand &  src)
: Instruction (QUESO) {
    this->dst = dst.copy();
    this->src = src.copy();
}

InstructionSignExtend :: ~InstructionSignExtend () {
    delete dst;
    delete src;
}

std::list <Operand *> InstructionSignExtend :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(src);
    return operands;
}

std::list <Operand *> InstructionSignExtend :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(src);
    return operands;
}

std::string InstructionSignExtend :: smtlib2 () {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " ((_ sign_extend "
       << dst->g_bits() << ") " << src->smtlib2() << ")))";

    return ss.str();
}

std::string InstructionSignExtend :: queso () {
    std::stringstream ss;
    ss << "signextend " << dst->queso() << " " << src->queso();
    return ss.str();
}

/*********************************************
* Instruction : InstructionArithmetic
**********************************************/

InstructionArithmetic :: InstructionArithmetic (const std::string & bvop,
                                                const std::string & opstr,
                                                const Variable * dst,
                                                const Operand *  lhs,
                                                const Operand *  rhs)
: Instruction (QUESO) {
    this->bvop = bvop;
    this->opstr = opstr;
    this->dst = dst->copy();
    this->lhs = lhs->copy();
    this->rhs = rhs->copy();
}

InstructionArithmetic :: InstructionArithmetic (const std::string & bvop,
                                                const std::string & opstr,
                                                const Variable & dst,
                                                const Operand &  lhs,
                                                const Operand &  rhs)
: Instruction (QUESO) {
    this->bvop = bvop;
    this->opstr = opstr;
    this->dst = dst.copy();
    this->lhs = lhs.copy();
    this->rhs = rhs.copy();
}

InstructionArithmetic :: ~InstructionArithmetic () {
    delete dst;
    delete lhs;
    delete rhs;
}

std::list <Operand *> InstructionArithmetic :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

std::list <Operand *> InstructionArithmetic :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

std::string InstructionArithmetic :: smtlib2 () {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (" << bvop << " " << lhs->smtlib2() << " "
       << rhs->smtlib2() << ")))";

    return ss.str();
}

std::string InstructionArithmetic :: queso () {
    std::stringstream ss;
    ss << opstr << " " << dst->queso() << " " << lhs->queso() << " " << rhs->queso();
    return ss.str();
}

/*********************************************
* Instruction : InstructionCmp
**********************************************/

InstructionCmp :: InstructionCmp (const std::string & bvop,
                                  const std::string & opstr,
                                  const Variable * dst,
                                  const Operand *  lhs,
                                  const Operand *  rhs)
: Instruction (QUESO) {
    this->bvop = bvop;
    this->opstr = opstr;
    this->dst = dst->copy();
    this->lhs = lhs->copy();
    this->rhs = rhs->copy();
}

InstructionCmp :: InstructionCmp (const std::string & bvop,
                                  const std::string & opstr,
                                  const Variable & dst,
                                  const Operand &  lhs,
                                  const Operand &  rhs)
: Instruction (QUESO) {
    this->bvop = bvop;
    this->opstr = opstr;
    this->dst = dst.copy();
    this->lhs = lhs.copy();
    this->rhs = rhs.copy();
}

InstructionCmp :: ~InstructionCmp () {
    delete dst;
    delete lhs;
    delete rhs;
}

std::list <Operand *> InstructionCmp :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

std::list <Operand *> InstructionCmp :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

std::string InstructionCmp :: smtlib2 () {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (ite ("
       << bvop << " " << lhs->smtlib2() << " " << rhs->smtlib2() << ") #b1 #b0)))";

    return ss.str();
}

std::string InstructionCmp :: queso () {
    std::stringstream ss;
    ss << opstr << " " << dst->queso() << " " << lhs->queso() << " " << rhs->queso();
    return ss.str();
}