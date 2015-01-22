#include "queso.h"

#include <algorithm>
#include <cstdio>
#include <iostream>
#include <sstream>
#include <queue>

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

std::string operandEmptyString("");

/*********************************************
* Operand : Variable
**********************************************/

Variable * Variable :: copy () const {
    Variable * nv = new Variable(bits, name);
    nv->ssa = this->ssa;
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

json_t * Variable :: json () const {
    json_t * json = json_object();

    json_object_set(json, "type", json_string("variable"));
    json_object_set(json, "name", json_string(name.c_str()));
    json_object_set(json, "bits", json_integer(bits));
    json_object_set(json, "ssa",  json_integer(ssa));

    return json;
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

json_t * Array :: json () const {
    json_t * json = json_object();

    json_object_set(json, "type", json_string("array"));
    json_object_set(json, "name", json_string(name.c_str()));
    json_object_set(json, "bits", json_integer(bits));
    json_object_set(json, "ssa",  json_integer(ssa));
    json_object_set(json, "address_bits", json_integer(address_bits));

    return json;
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

json_t * Constant :: json () const {
    json_t * json = json_object();

    json_object_set(json, "type", json_string("constant"));
    json_object_set(json, "bits", json_integer(bits));
    json_object_set(json, "value", json_integer(value));

    return json;
}

/*********************************************
* Instruction
**********************************************/

void Instruction :: copy_depth_instructions (const Instruction * srcInstructions) {
    this->depth_instructions.clear();

    std::list <Instruction *> :: const_iterator it;
    for (it = srcInstructions->depth_instructions.begin();
         it != srcInstructions->depth_instructions.end();
         it++) {
        const Instruction * instruction = *it;
        this->depth_instructions.push_back(instruction->copy());
    }
}

std::list <Instruction *> & Instruction :: g_depth_instructions () {
    return depth_instructions;
}

void Instruction :: push_depth_instruction (Instruction * instruction) {
    depth_instructions.push_back(instruction);
    flattened.clear();
}


bool Instruction :: remove_depth_instruction (Instruction * instruction) {
    std::list <Instruction *> :: iterator it;
    for (it = depth_instructions.begin(); it != depth_instructions.end(); it++) {
        if (*it == instruction) {
            it = depth_instructions.erase(it);
            flattened.clear();
            return true;
        }
        if ((*it)->remove_depth_instruction(instruction)) {
            flattened.clear();
            return true;
        }
    }
    return false;
}


bool Instruction :: replace_depth_instruction (Instruction * oldInstruction,
                                               Instruction * newInstruction) {
    std::list <Instruction *> :: iterator it;
    bool result = false;

    for (it = depth_instructions.begin(); it != depth_instructions.end(); it++) {
        if (*it = oldInstruction) {
            bool push_front = false;
            if (it == depth_instructions.begin())
                push_front = true;

            it = depth_instructions.erase(it);
            depth_instructions.insert(it, newInstruction->copy());
            result = true;
            break;
        }
        if ((*it)->replace_depth_instruction(oldInstruction, newInstruction)) {
            result = true;
            break;
        }
    }

    if (result)
        flattened.clear();

    return result;
}


bool Instruction :: remove_depth_instructions_ (std::set <Instruction *> & instructions) {
    std::list <Instruction *> :: iterator it;

    bool deleted = false;

    for (it = depth_instructions.begin(); it != depth_instructions.end(); it++) {
        while (    (it != depth_instructions.end()) 
                && (instructions.count(*it) > 0)) {
            deleted = true;
            delete *it;
            it = depth_instructions.erase(it);
        }

        if (it == depth_instructions.end())
            break;

        if ((*it)->remove_depth_instructions_(instructions))
            deleted = true;
    }

    if (deleted)
        flattened.clear();

    return deleted;
}


void Instruction :: remove_depth_instructions (std::set <Instruction *> instructions) {
    this->remove_depth_instructions_(instructions);
}


void Instruction :: var_dominators (std::list <std::string> & dominator_variables,
                                    std::list <Instruction *> & dominator_instructions) {

    // if this is a queso variable
    //if (opcode != USER) {
    if (true) {
        // get name of operand written by this instruction
        std::string var_name = "";
        if (Variable * variable = dynamic_cast<Variable *>(operand_written()))
            var_name = variable->g_name();
        else if (Array * array = dynamic_cast<Array *>(operand_written()))
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
    //else {
        std::list <Instruction *> :: const_reverse_iterator rit;
        
        for (rit = depth_instructions.rbegin(); rit != depth_instructions.rend(); rit++) {
            (*rit)->var_dominators(dominator_variables, dominator_instructions);
        }
    //}
}


std::list <Instruction *> Instruction :: var_dominators (std::string name) {
    std::list <Instruction *> dominator_instructions;
    std::list <std::string>   dominator_variables;

    dominator_variables.push_back(name);

    var_dominators(dominator_variables, dominator_instructions);

    dominator_instructions.reverse();

    return dominator_instructions;
}


void Instruction_flatten (std::list <Instruction *> & instructions,
                          Instruction * instruction) {
    instructions.push_back(instruction);

    std::list <Instruction *> :: iterator it;
    for (it = instruction->g_depth_instructions().begin();
         it != instruction->g_depth_instructions().end();
         it++) {
        Instruction_flatten(instructions, *it);
    }
}


std::list <Instruction *> & Instruction :: flatten () {
    if (flattened.size() == 0)
        Instruction_flatten(flattened, this);

    return flattened;
}


void Instruction :: depthSmtlib2Declarations (std::stringstream & ss) {
    std::list <Operand *> operands_ = operands();
    std::list <Operand *> :: iterator oit;
    for (oit = operands_.begin(); oit != operands_.end(); oit++) {
        ss << (*oit)->smtlib2_declaration() << std::endl;
    }

    std::list <Instruction *> :: iterator it;
    for (it = depth_instructions.begin(); it != depth_instructions.end(); it++) {
        (*it)->depthSmtlib2Declarations(ss);
    }
}


std::string Instruction :: depthSmtlib2Declarations () {
    std::stringstream ss;

    depthSmtlib2Declarations(ss);

    return ss.str();
}


void Instruction :: depthSmtlib2 (std::stringstream & ss) {
    ss << smtlib2() << std::endl;

    std::list <Instruction *> :: iterator it;
    for (it = depth_instructions.begin(); it != depth_instructions.end(); it++) {
        (*it)->depthSmtlib2(ss);
    }
}


std::string Instruction :: depthSmtlib2 () {
    std::stringstream ss;

    depthSmtlib2(ss);

    return ss.str();
}


json_t * Instruction :: json () const {
    json_t * json = json_object();

    if (pc_set) {
        json_object_set(json, "pc", json_integer(pc));
    }

    if (depth_instructions.size() > 0) {
        json_t * json_depth = json_array();
        std::list <Instruction *> :: const_iterator it;
        for (it = depth_instructions.begin(); it != depth_instructions.end(); it++) {
            json_array_append(json_depth, (*it)->json());
        }
        json_object_set(json, "depth_instructions", json_depth);
    }
    
    json_object_set(json, "queso", json_string(queso().c_str()));

    return json;
}


/*********************************************
* Instruction : InstructionAssign
**********************************************/

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

json_t * InstructionAssign :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("assign"));
    json_object_set(json, "dst", dst->json());
    json_object_set(json, "src", src->json());

    return json;
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

json_t * InstructionStore :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("store"));
    json_object_set(json, "dstmem", dstmem->json());
    json_object_set(json, "srcmem", srcmem->json());
    json_object_set(json, "address", address->json());
    json_object_set(json, "value", value->json());

    return json;
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

json_t * InstructionLoad :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("store"));
    json_object_set(json, "dst", dst->json());
    json_object_set(json, "mem", mem->json());
    json_object_set(json, "address", address->json());

    return json;
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

json_t * InstructionIte :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("ite"));
    json_object_set(json, "condition", condition->json());
    json_object_set(json, "t", t->json());
    json_object_set(json, "e", e->json());

    return json;
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

const std::string InstructionSignExtend :: smtlib2 () const {
    std::stringstream ss;

    ss << "(assert (= " << dst->smtlib2() << " ((_ sign_extend "
       << (dst->g_bits() - src->g_bits()) << ") " << src->smtlib2() << ")))";

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

json_t * InstructionSignExtend :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("signExtend"));
    json_object_set(json, "dst", dst->json());
    json_object_set(json, "src", src->json());

    return json;
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

json_t * InstructionArithmetic :: json () const {
    json_t * json = Instruction::json();

    switch (g_opcode()) {
    case ADD :
        json_object_set(json, "instruction", json_string("add"));
        break;
    case SUB :
        json_object_set(json, "instruction", json_string("sub"));
        break;
    case MUL :
        json_object_set(json, "instruction", json_string("mul"));
        break;
    case UDIV :
        json_object_set(json, "instruction", json_string("udiv"));
        break;
    case UREM :
        json_object_set(json, "instruction", json_string("urem"));
        break;
    case AND :
        json_object_set(json, "instruction", json_string("and"));
        break;
    case OR :
        json_object_set(json, "instruction", json_string("or"));
        break;
    case XOR :
        json_object_set(json, "instruction", json_string("xor"));
        break;
    case SHL :
        json_object_set(json, "instruction", json_string("shl"));
        break;
    case SHR :
        json_object_set(json, "instruction", json_string("shr"));
        break;
    }
    json_object_set(json, "dst", dst->json());
    json_object_set(json, "lhs", lhs->json());
    json_object_set(json, "rhs", rhs->json());

    return json;
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

json_t * InstructionCmp :: json () const {
    json_t * json = Instruction::json();

    switch (g_opcode()) {
    case CMPEQ :
        json_object_set(json, "instruction", json_string("cmpeq"));
        break;
    case CMPLTU :
        json_object_set(json, "instruction", json_string("cmpltu"));
        break;
    case CMPLEU :
        json_object_set(json, "instruction", json_string("cmpleu"));
        break;
    case CMPLTS :
        json_object_set(json, "instruction", json_string("cmplts"));
        break;
    case CMPLES :
        json_object_set(json, "instruction", json_string("cmples"));
        break;
    }
    json_object_set(json, "dst", dst->json());
    json_object_set(json, "lhs", lhs->json());
    json_object_set(json, "rhs", rhs->json());

    return json;
}