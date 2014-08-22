#include "queso.h"

#include <algorithm>
#include <cstdio>
#include <iostream>
#include <sstream>

const char * QuesoOpcodeStrings [] = {
    "assign",
    "store",
    "load",
    "ite",
    "sext",
    "add",
    "sub",
    "mul",
    "udiv",
    "umod",
    "and",
    "or",
    "xor",
    "shl",
    "shr",
    "cmpeq",
    "cmpltu",
    "cmpleu",
    "cmplts",
    "cmpltu",
    "USER"
};

/*********************************************
* Operand : Variable
**********************************************/

Variable * Variable :: copy () const {
    Variable * nv = new Variable(bits, name);
    nv->ssa = ssa;
    return nv;
}

std::string Variable :: smtlib2 () const {
    std::stringstream ss;
    ss << name << "_" << ssa;
    return ss.str();
}

std::string Variable :: smtlib2_declaration () const {
    std::stringstream ss;
    ss << "(declare-fun " << smtlib2() << " () (_ BitVec " << bits << "))";
    return ss.str();
}

std::string Variable :: queso () const {
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

std::string Array :: smtlib2 () const {
    std::stringstream ss;
    ss << name << "_" << ssa;
    return ss.str();
}

std::string Array :: smtlib2_declaration () const {
    std::stringstream ss;
    ss << "(declare-fun " << smtlib2() << " () (Array (_ BitVec "
       << address_bits << ") (_ BitVec " << bits << ")))";
    return ss.str();
}

std::string Array :: queso () const {
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

std::string Constant :: smtlib2 () const {
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

std::string Constant :: smtlib2_declaration () const {
    return "";
}

std::string Constant :: queso () const {
    std::stringstream ss;
    ss << bits << ":" << std::hex << value;
    return ss.str();
}

/*********************************************
* Instruction
**********************************************/

void Instruction :: copy_depth_instructions (const Instruction * srcInstructions) {
    this->depth_instructions.clear();

    std::list <Instruction *> :: const_iterator it;
    for (it = srcInstructions->g_depth_instructions().begin();
         it != srcInstructions->g_depth_instructions().end();
         it++) {
        Instruction * instruction = *it;
        this->depth_instructions.push_back(instruction->copy());
    }
}

const std::list <Instruction *> & Instruction :: g_depth_instructions () const {
    return depth_instructions;
}

void Instruction :: push_depth_instruction (Instruction * instruction) {
    depth_instructions.push_back(instruction);
}


void Instruction :: var_dominators (std::list <std::string> & dominator_variables,
                                    std::list <const Instruction *> & dominator_instructions) const {

    // if this is a queso variable
    if (opcode != USER) {
        // get name of operand written by this instruction
        std::string var_name = "";
        if (const Variable * variable = dynamic_cast<const Variable *>(operand_written()))
            var_name = variable->g_name();
        else if (const Array * array = dynamic_cast<const Array *>(operand_written()))
            var_name = array->g_name();

    /*
    std::cout << "dominator_variables" << std::endl;
    for (auto dvit = dominator_variables.begin(); dvit != dominator_variables.end(); dvit++) {
        std::cout << "\t" << *dvit << std::endl;
    }
    std::cout << "\tqueso: " << queso() << std::endl;
    std::cout << "\topcode: " << opcode << std::endl;
    std::cout << "\tvar_name: " << var_name << std::endl;
    std::cout << "\toperand_written(): " << operand_written() << std::endl;
    std::cout << "-------------------" << std::endl;
    */

        // if variable being written is a dominator
        std::list <std::string> :: iterator it;
        for (it = dominator_variables.begin(); it != dominator_variables.end(); it++) {
            if (*it == var_name) {
                // add this instruction to dominator_instructions
                dominator_instructions.push_back(this);
                // add all source variables to dominator variables
                const std::list <Operand *> op_read = operands_read();
                std::list <Operand *> :: const_iterator rit;
                for (rit = op_read.begin(); rit != op_read.end(); rit++) {
                    if (Variable * variable = dynamic_cast<Variable *>(*rit)) {
                        auto findIt = std::find(dominator_variables.begin(), dominator_variables.end(), variable->g_name());
                        if (findIt == dominator_variables.end())
                            dominator_variables.push_back(variable->g_name());
                    }
                    else if (Array * array = dynamic_cast<Array *>(*rit)) {
                        auto findIt = std::find(dominator_variables.begin(), dominator_variables.end(), array->g_name());
                        if (findIt == dominator_variables.end())
                            dominator_variables.push_back(array->g_name());
                    }
                }
            }
        }
    }
    else {
        std::list <Instruction *> :: const_reverse_iterator it;
        
        for (it = depth_instructions.rbegin(); it != depth_instructions.rend(); it++) {
            (*it)->var_dominators(dominator_variables, dominator_instructions);
        }
        
    }
}


const std::list <const Instruction *> Instruction :: var_dominators (std::string name) const {
    std::list <const Instruction *> dominator_instructions;
    std::list <std::string>   dominator_variables;

    dominator_variables.push_back(name);

    var_dominators(dominator_variables, dominator_instructions);

    dominator_instructions.reverse();

    return dominator_instructions;
}


/*********************************************
* Instruction : InstructionAssign
**********************************************/

InstructionAssign :: ~InstructionAssign () {
    delete dst;
    delete src;
}


const std::list <Operand *> InstructionAssign :: operands_read () const  {
    std::list <Operand *> operands;
    operands.push_back(src);
    return operands;
}


const std::list <Operand *> InstructionAssign :: operands () const  {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(src);
    return operands;
}


const std::string InstructionAssign :: smtlib2 () const {
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

const std::string InstructionAssign :: queso () const {
    std::stringstream ss;
    ss << "assign " << dst->queso() << " " << src->queso();
    return ss.str();
}


InstructionAssign * InstructionAssign :: copy () const {
    return new InstructionAssign(dst, src);
}

/*********************************************
* Instruction : InstructionStore
**********************************************/

InstructionStore :: InstructionStore (const Array * mem,
                                      const Operand * address,
                                      const Operand * value)
: Instruction (STORE) {
    this->dstmem  = mem->copy();
    this->srcmem  = mem->copy();
    this->address = address->copy();
    this->value   = value->copy();
}


InstructionStore :: InstructionStore (const Array * dstmem,
                                      const Array * srcmem,
                                      const Operand * address,
                                      const Operand * value)
: Instruction (STORE) {
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


const std::list <Operand *> InstructionStore :: operands_read () const {
    std::list <Operand *> operands;
    operands.push_back(srcmem);
    operands.push_back(address);
    operands.push_back(value);
    return operands;
}

const std::list <Operand *> InstructionStore :: operands () const {
    std::list <Operand *> operands;
    operands.push_back(dstmem);
    operands.push_back(srcmem);
    operands.push_back(address);
    operands.push_back(value);
    return operands;
}

const std::string InstructionStore :: smtlib2 () const {
    std::stringstream ss;

    ss << "(assert (= " << dstmem->smtlib2() << " (store " << srcmem->smtlib2() << " "
       << address->smtlib2() << " " << value->smtlib2() << ")))";
    
    return ss.str();
}

const std::string InstructionStore :: queso () const {
    std::stringstream ss;
    ss << "store " << dstmem->queso() << "[" << address->queso() << "] " << value->queso();
    return ss.str();
}

InstructionStore * InstructionStore :: copy () const {
    return new InstructionStore(dstmem, srcmem, address, value);
}

/*********************************************
* Instruction : InstructionLoad
**********************************************/

InstructionLoad :: InstructionLoad (const Variable * dst,
                                    const Array * mem,
                                    const Operand * address)
: Instruction (LOAD) {
    this->dst = dst->copy();
    this->mem = mem->copy();
    this->address = address->copy();
}

InstructionLoad :: ~InstructionLoad () {
    delete dst;
    delete mem;
    delete address;
}

const std::list <Operand *> InstructionLoad :: operands_read () const  {
    std::list <Operand *> operands;
    operands.push_back(mem);
    operands.push_back(address);
    return operands;
}

const std::list <Operand *> InstructionLoad :: operands () const  {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(mem);
    operands.push_back(address);
    return operands;
}

const std::string InstructionLoad :: smtlib2 () const {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (select " << mem->smtlib2() << " "
       << address->smtlib2() << ")))";
    
    return ss.str();
}

const std::string InstructionLoad :: queso () const {
    std::stringstream ss;
    ss << "load " << dst->queso() << " " << mem->queso() << "[" << address->queso() << "]";
    return ss.str();
}

InstructionLoad * InstructionLoad :: copy () const {
    return new InstructionLoad(dst, mem, address);
}

/*********************************************
* Instruction : InstructionIte
**********************************************/

InstructionIte :: InstructionIte (const Variable * dst,
                                   const Operand * condition,
                                   const Operand * t,
                                   const Operand * e)
: Instruction (ITE) {
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

const std::list <Operand *> InstructionIte :: operands_read () const  {
    std::list <Operand *> operands;
    operands.push_back(condition);
    operands.push_back(t);
    operands.push_back(e);
    return operands;
}

const std::list <Operand *> InstructionIte :: operands () const  {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(condition);
    operands.push_back(t);
    operands.push_back(e);
    return operands;
}

const std::string InstructionIte :: smtlib2 () const {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (ite (= " << condition->smtlib2() << " #b1) "
       << t->smtlib2() << " " << e->smtlib2() << ")))";
    
    return ss.str();
}

const std::string InstructionIte :: queso () const {
    std::stringstream ss;
    ss << "ite " << dst->queso() << " (" << condition->queso()
       << " ? " << t->queso() << " : " << e->queso() << ")";
    return ss.str();
}

InstructionIte * InstructionIte :: copy () const {
    return new InstructionIte(dst, condition, t, e);
}

/*********************************************
* Instruction : InstructionSignExtend
**********************************************/

InstructionSignExtend :: InstructionSignExtend (const Variable * dst,
                                                const Operand *  src)
: Instruction (SEXT) {
    this->dst = dst->copy();
    this->src = src->copy();
}

InstructionSignExtend :: InstructionSignExtend (const Variable & dst,
                                                const Operand &  src)
: Instruction (SEXT) {
    this->dst = dst.copy();
    this->src = src.copy();
}

InstructionSignExtend :: ~InstructionSignExtend () {
    delete dst;
    delete src;
}

const std::list <Operand *> InstructionSignExtend :: operands_read () const  {
    std::list <Operand *> operands;
    operands.push_back(src);
    return operands;
}

const std::list <Operand *> InstructionSignExtend :: operands () const  {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(src);
    return operands;
}

const std::string InstructionSignExtend :: smtlib2 () const {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " ((_ sign_extend "
       << dst->g_bits() << ") " << src->smtlib2() << ")))";

    return ss.str();
}

const std::string InstructionSignExtend :: queso () const {
    std::stringstream ss;
    ss << "signextend " << dst->queso() << " " << src->queso();
    return ss.str();
}

InstructionSignExtend * InstructionSignExtend :: copy () const {
    return new InstructionSignExtend(dst, src);
}

/*********************************************
* Instruction : InstructionArithmetic
**********************************************/

InstructionArithmetic :: InstructionArithmetic (QuesoOpcode opcode,
                                                const std::string & bvop,
                                                const Variable * dst,
                                                const Operand *  lhs,
                                                const Operand *  rhs)
: Instruction (opcode) {
    this->bvop = bvop;
    this->dst = dst->copy();
    this->lhs = lhs->copy();
    this->rhs = rhs->copy();
}

InstructionArithmetic :: InstructionArithmetic (QuesoOpcode opcode,
                                                const std::string & bvop,
                                                const Variable & dst,
                                                const Operand &  lhs,
                                                const Operand &  rhs)
: Instruction (opcode) {
    this->bvop = bvop;
    this->dst = dst.copy();
    this->lhs = lhs.copy();
    this->rhs = rhs.copy();
}

InstructionArithmetic :: ~InstructionArithmetic () {
    delete dst;
    delete lhs;
    delete rhs;
}

const std::list <Operand *> InstructionArithmetic :: operands_read () const  {
    std::list <Operand *> operands;
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

const std::list <Operand *> InstructionArithmetic :: operands () const  {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

const std::string InstructionArithmetic :: smtlib2 () const {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (" << bvop << " " << lhs->smtlib2() << " "
       << rhs->smtlib2() << ")))";

    return ss.str();
}

const std::string InstructionArithmetic :: queso () const {
    std::stringstream ss;
    ss << QuesoOpcodeStrings[g_opcode()] 
       << " " << dst->queso() << " " << lhs->queso() << " " << rhs->queso();
    return ss.str();
}

/*********************************************
* Instruction : InstructionCmp
**********************************************/

InstructionCmp :: InstructionCmp (QuesoOpcode opcode,
                                  const std::string & bvop,
                                  const Variable * dst,
                                  const Operand *  lhs,
                                  const Operand *  rhs)
: Instruction (opcode) {
    this->bvop = bvop;
    this->dst = dst->copy();
    this->lhs = lhs->copy();
    this->rhs = rhs->copy();
}

InstructionCmp :: InstructionCmp (QuesoOpcode opcode,
                                  const std::string & bvop,
                                  const Variable & dst,
                                  const Operand &  lhs,
                                  const Operand &  rhs)
: Instruction (opcode) {
    this->bvop = bvop;
    this->dst = dst.copy();
    this->lhs = lhs.copy();
    this->rhs = rhs.copy();
}

InstructionCmp :: ~InstructionCmp () {
    delete dst;
    delete lhs;
    delete rhs;
}

const std::list <Operand *> InstructionCmp :: operands_read () const  {
    std::list <Operand *> operands;
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

const std::list <Operand *> InstructionCmp :: operands () const  {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(lhs);
    operands.push_back(rhs);
    return operands;
}

const std::string InstructionCmp :: smtlib2 () const {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " (ite ("
       << bvop << " " << lhs->smtlib2() << " " << rhs->smtlib2() << ") #b1 #b0)))";

    return ss.str();
}

const std::string InstructionCmp :: queso () const {
    std::stringstream ss;
    ss << QuesoOpcodeStrings[g_opcode()]
       << " " << dst->queso() << " " << lhs->queso() << " " << rhs->queso();
    return ss.str();
}