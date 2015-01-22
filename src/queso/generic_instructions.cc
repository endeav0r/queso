#include "generic_instructions.h"

#include <iostream>
#include <sstream>
#include <vector>


InstructionBlock * InstructionBlock :: copy () const {
    InstructionBlock * block = new InstructionBlock();

    block->copy_depth_instructions(this);

    return block;
}


json_t * InstructionBlock :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("block"));

    return json;
}



InstructionPhi :: InstructionPhi (const Operand * dst) {
    this->dst = dst->copy();
}


InstructionPhi :: ~InstructionPhi () {
    delete dst;

    std::list <Operand *> :: iterator it;
    for (it = src.begin(); it != src.end(); it++)
        delete *it;
}


void InstructionPhi :: add_src (const Operand * operand) {
    this->src.push_back(operand->copy());
}


std::list <Operand *> InstructionPhi :: operands_read () {
    return src;
}


std::list <Operand *> InstructionPhi :: operands () {

    std::list <Operand *> result;
    std::list <Operand *> :: iterator it;

    for (it = src.begin(); it != src.end(); it++) {
        result.push_back(*it);
    }

    result.push_back(dst);

    return result;
}


const std::string InstructionPhi :: queso () const {
    std::stringstream ss;

    ss << "Phi " << dst->queso() << " <- ( ";

    std::list <Operand *> :: const_iterator it;
    for (it = src.begin(); it != src.end(); it++) {
        ss << (*it)->queso() << " ";
    }

    ss << ")";

    return ss.str();
}


InstructionPhi * InstructionPhi :: copy () const {
    InstructionPhi * newPhi = new InstructionPhi(dst);

    std::list <Operand *> :: const_iterator it;
    for (it = src.begin(); it != src.end(); it++) {
        newPhi->add_src(*it);
    }

    return newPhi;
}


std::string phi_smtlib2 (Operand * dst, std::vector <Operand *> operands) {
    std::stringstream ss;
    if (operands.size() == 2) {
        ss << "(or " 
           << "(= " << dst->smtlib2() << " " << operands[0]->smtlib2() << ") "
           << "(= " << dst->smtlib2() << " " << operands[1]->smtlib2() << "))";
        return ss.str();
    }
    else if (operands.size() == 3) {
        ss << "(or (or "
           << "(= " << dst->smtlib2() << " " << operands[0]->smtlib2() << ") "
           << "(= " << dst->smtlib2() << " " << operands[1]->smtlib2() << ")) "
           << "(= " << dst->smtlib2() << " " << operands[2]->smtlib2() << ")) ";
        return ss.str();
    }
    else {
        std::vector <Operand *> first;
        std::vector <Operand *> second;
        for (size_t i = 0; i < operands.size(); i++) {
            if (i < operands.size() / 2)
                first.push_back(operands[i]);
            else
                second.push_back(operands[i]);
        }
        ss << "(or "
           << phi_smtlib2(dst, first) << " "
           << phi_smtlib2(dst, second) << ")";
        return ss.str();
    }
}


const std::string InstructionPhi :: smtlib2 () const {
    std::stringstream ss;
    if (src.size() == 0)
        return "";

    else if (src.size() == 1) {
        ss << "(assert (= " << dst->smtlib2() << " " << src.front()->smtlib2() << "))";
        return ss.str();
    }
    else {
        ss << "(assert " << phi_smtlib2(dst, std::vector <Operand *> (src.begin(), src.end())) << ")";
        return ss.str();
    }
}


json_t * InstructionPhi :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("phi"));

    json_object_set(json, "dst", dst->json());

    json_t * operands = json_array();

    std::list <Operand *> :: const_iterator it;
    for (it = src.begin(); it != src.end(); it++) {
        Operand * operand = *it;
        json_array_append(operands, operand->json());
    }

    json_object_set(json, "src", operands);

    return json;
}


/***********************************************
* InstructionLoadLE16
***********************************************/

InstructionLoadLE16 :: InstructionLoadLE16 (const Variable & dst,
                                            const Array & memory,
                                            const Operand & address)
: dst (dst.copy()), memory (memory.copy()), address (address.copy()) {
    init();
}


InstructionLoadLE16 :: InstructionLoadLE16 (const Variable * dst,
                                            const Array * memory,
                                            const Operand * address)
: dst (dst->copy()), memory (memory->copy()), address (address->copy()) {
    init();
}


void InstructionLoadLE16 :: init () {
    Variable load8h(8, "load8h");
    Variable tmpAddress(address->g_bits(), "tmpAddress");
    Constant one(32, 1);
    Variable load8l(8, "load8l");
    Variable load16(16, "load16");
    Constant eight(16, 8);

    push_depth_instruction(new InstructionLoad(&load8l, memory, address));
    push_depth_instruction(new InstructionAdd(&tmpAddress, address, &one));
    push_depth_instruction(new InstructionLoad(&load8h, memory, &tmpAddress));
    push_depth_instruction(new InstructionAssign(dst, &load8l));
    push_depth_instruction(new InstructionAssign(&load16, &load8h));
    push_depth_instruction(new InstructionShl(&load16, &load16, &eight));
    push_depth_instruction(new InstructionOr(dst, dst, &load16));
}


InstructionLoadLE16 :: ~InstructionLoadLE16 () {
    delete address;
    delete memory;
    delete dst;
}


const std::string InstructionLoadLE16 :: queso () const {
    std::stringstream ss;
    ss << "LoadLE16 " << dst->queso() << " = " 
       << memory->queso() << "[" << address->queso() << "]";
    return ss.str();
}


InstructionLoadLE16 * InstructionLoadLE16 :: copy () const { 
    return new InstructionLoadLE16(dst, memory, address);
}


json_t * InstructionLoadLE16 :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("loadle16"));

    json_object_set(json, "dst",     dst->json());
    json_object_set(json, "memory",  memory->json());
    json_object_set(json, "address", address->json());

    return json;
}


/***********************************************
* InstructionLoadLE32
***********************************************/


InstructionLoadLE32 :: InstructionLoadLE32 (const Variable & dst,
                                            const Array & memory,
                                            const Operand & address)
: dst (dst.copy()), memory (memory.copy()), address (address.copy()) {
    init();
}


InstructionLoadLE32 :: InstructionLoadLE32 (const Variable * dst,
                                            const Array * memory,
                                            const Operand * address)
: dst (dst->copy()), memory (memory->copy()), address (address->copy()) {
    init();
}


InstructionLoadLE32 :: ~InstructionLoadLE32 () {
    delete dst;
    delete memory;
    delete address;
}


void InstructionLoadLE32 :: init () {
    Variable load8_0(8, "load8_0");
    Variable load8_1(8, "load8_1");
    Variable load8_2(8, "load8_2");
    Variable load8_3(8, "load8_3");
    Variable load32(32, "load32");

    Variable tmpAddress(address->g_bits(), "tmpAddress");
    Constant one(address->g_bits(), 1);
    Variable tmp(dst->g_bits(), "tmpLoad");
    Constant eight(32, 8);

    push_depth_instruction(new InstructionLoad(&load8_0, memory, address));
    push_depth_instruction(new InstructionAdd(&tmpAddress, address, &one));

    push_depth_instruction(new InstructionLoad(&load8_1, memory, &tmpAddress));
    push_depth_instruction(new InstructionAdd(&tmpAddress, &tmpAddress, &one));

    push_depth_instruction(new InstructionLoad(&load8_2, memory, &tmpAddress));
    push_depth_instruction(new InstructionAdd(&tmpAddress, &tmpAddress, &one));

    push_depth_instruction(new InstructionLoad(&load8_3, memory, &tmpAddress));

    push_depth_instruction(new InstructionAssign(dst, &load8_3));
    push_depth_instruction(new InstructionShl(dst, dst, &eight));

    push_depth_instruction(new InstructionAssign(&load32, &load8_2));
    push_depth_instruction(new InstructionOr(dst, dst, &load32));
    push_depth_instruction(new InstructionShl(dst, dst, &eight));


    push_depth_instruction(new InstructionAssign(&load32, &load8_1));
    push_depth_instruction(new InstructionOr(dst, dst, &load32));
    push_depth_instruction(new InstructionShl(dst, dst, &eight));

    push_depth_instruction(new InstructionAssign(&load32, &load8_0));
    push_depth_instruction(new InstructionOr(dst, dst, &load32));
}

/*
std::list <Operand *> InstructionLoadLE32 :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(memory);
    operands.push_back(address);
    return operands;
}


std::list <Operand *> InstructionLoadLE32 :: operands () {
    std::list <Operand *> operands;
    operands.push_back(dst);
    operands.push_back(memory);
    operands.push_back(address);
    return operands;
}
*/

const std::string InstructionLoadLE32 :: queso () const {
    std::stringstream ss;
    ss << "LoadLE32 " << dst->queso() << " = " 
       << memory->queso() << "[" << address->queso() << "]";
    return ss.str();
}


InstructionLoadLE32 * InstructionLoadLE32 :: copy () const {
    return new InstructionLoadLE32(dst, memory, address);
}

/*
const std::string InstructionLoadLE32 :: smtlib2 () const {
    std::stringstream ss;
    ss << "(assert (= " << dst->smtlib2() << " "
       << "(concat "
       << "(select " << memory->smtlib2() << " (bvadd " << address->smtlib2() << " #x00000003)) "
       << "(select " << memory->smtlib2() << " (bvadd " << address->smtlib2() << " #x00000002)) "
       << "(select " << memory->smtlib2() << " (bvadd " << address->smtlib2() << " #x00000001)) "
       << "(select " << memory->smtlib2() << " " << address->smtlib2() << "))))";
    return ss.str();
}
*/

json_t * InstructionLoadLE32 :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("loadle32"));

    json_object_set(json, "dst",     dst->json());
    json_object_set(json, "memory",  memory->json());
    json_object_set(json, "address", address->json());

    return json;
}


/***********************************************
* InstructionStoreLE16
***********************************************/

InstructionStoreLE16 :: InstructionStoreLE16 (const Array & memory,
                                              const Operand & address,
                                              const Operand & value)
: memory (memory.copy()), address (address.copy()), value (value.copy()) {
    init();
}


InstructionStoreLE16 :: InstructionStoreLE16 (const Array * memory,
                                              const Operand * address,
                                              const Operand * value)
: memory (memory->copy()), address (address->copy()), value (value->copy()) {
    init();
}


InstructionStoreLE16 :: ~InstructionStoreLE16 () {
    delete memory;
    delete address;
    delete value;
}


void InstructionStoreLE16 :: init () {
    Variable tmpAddress(address->g_bits(), "tmpAddress");
    Constant one(address->g_bits(), 1);
    Variable tmpShift(16, "tmpShift");
    Variable tmp(8, "tmpEight");
    Constant eight(16, 8);

    push_depth_instruction(new InstructionAssign(&tmp, value));
    push_depth_instruction(new InstructionStore(memory, address, &tmp));

    push_depth_instruction(new InstructionAdd(&tmpAddress, address, &one));
    push_depth_instruction(new InstructionShr(&tmpShift, value, &eight));
    push_depth_instruction(new InstructionAssign(&tmp, &tmpShift));

    push_depth_instruction(new InstructionStore(memory, &tmpAddress, &tmp));
}


const std::string InstructionStoreLE16 :: queso () const {
    std::stringstream ss;
    ss << "StoreLE16 " << memory->queso() << "[" << address->queso() << "]"
       << " = " << value->queso();
    return ss.str();
}


InstructionStoreLE16 * InstructionStoreLE16 :: copy () const {
    return new InstructionStoreLE16(memory, address, value);
}


json_t * InstructionStoreLE16 :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("storele16"));

    json_object_set(json, "memory",  memory->json());
    json_object_set(json, "address", address->json());
    json_object_set(json, "value",   value->json());

    return json;
}


/***********************************************
* InstructionStoreLE32
***********************************************/


InstructionStoreLE32 :: InstructionStoreLE32 (const Array & memory,
                                              const Operand & address,
                                              const Operand & value)
: mem_dst (memory.copy()), memory (memory.copy()), address (address.copy()), value (value.copy()) {
    init();
}


InstructionStoreLE32 :: InstructionStoreLE32 (const Array * memory,
                                              const Operand * address,
                                              const Operand * value)
: mem_dst (memory->copy()), memory (memory->copy()), address (address->copy()), value (value->copy()) {
    init();
}


InstructionStoreLE32 :: ~InstructionStoreLE32 () {
    delete mem_dst;
    delete memory;
    delete address;
    delete value;
}


void InstructionStoreLE32 :: init () {
    Variable tmpAddress(address->g_bits(), "tmpAddress");
    Constant one(address->g_bits(), 1);
    Variable tmpShift(32, "tmpShift");
    Variable tmp(8, "tmpEight");
    Constant eight(32, 8);

    push_depth_instruction(new InstructionAssign(&tmp, value));
    push_depth_instruction(new InstructionStore(memory, address, &tmp));

    push_depth_instruction(new InstructionAdd(&tmpAddress, address, &one));
    push_depth_instruction(new InstructionShr(&tmpShift, value, &eight));
    push_depth_instruction(new InstructionAssign(&tmp, &tmpShift));
    push_depth_instruction(new InstructionStore(memory, &tmpAddress, &tmp));

    push_depth_instruction(new InstructionAdd(&tmpAddress, &tmpAddress, &one));
    push_depth_instruction(new InstructionShr(&tmpShift, &tmpShift, &eight));
    push_depth_instruction(new InstructionAssign(&tmp, &tmpShift));
    push_depth_instruction(new InstructionStore(memory, &tmpAddress, &tmp));

    push_depth_instruction(new InstructionAdd(&tmpAddress, &tmpAddress, &one));
    push_depth_instruction(new InstructionShr(&tmpShift, &tmpShift, &eight));
    push_depth_instruction(new InstructionAssign(&tmp, &tmpShift));
    push_depth_instruction(new InstructionStore(memory, &tmpAddress, &tmp));
}


const std::string InstructionStoreLE32 :: queso () const {
    std::stringstream ss;
    ss << "StoreLE32 " << memory->queso() << "[" << address->queso() << "]"
       << " = " << value->queso();
    return ss.str();
}


InstructionStoreLE32 * InstructionStoreLE32 :: copy () const {
    return new InstructionStoreLE32(memory, address, value);
}

/*
std::list <Operand *> InstructionStoreLE32 :: operands_read () {
    std::list <Operand *> operands;
    operands.push_back(memory);
    operands.push_back(address);
    operands.push_back(value);
    return operands;
}


std::list <Operand *> InstructionStoreLE32 :: operands () {
    std::list <Operand *> operands;
    operands.push_back(mem_dst);
    operands.push_back(memory);
    operands.push_back(address);
    operands.push_back(value);
    return operands;
}


const std::string InstructionStoreLE32 :: smtlib2 () const {
    std::stringstream ss;
    ss << "(assert (= " << mem_dst->smtlib2() << " "
       << "(store (store (store (store "
       << memory->smtlib2() << " " << address->smtlib2() << " ((_ extract 7 0) " << value->smtlib2() << ")) "
       << "(bvadd " << address->smtlib2() << " #x00000001) ((_ extract 15 8) " << value->smtlib2() << ")) "
       << "(bvadd " << address->smtlib2() << " #x00000002) ((_ extract 23 16) " << value->smtlib2() << ")) "
       << "(bvadd " << address->smtlib2() << " #x00000003) ((_ extract 31 24) " << value->smtlib2() << ")) "
       << "))";
    return ss.str();
}
*/

json_t * InstructionStoreLE32 :: json () const {
    json_t * json = Instruction::json();

    json_object_set(json, "instruction", json_string("storele32"));

    json_object_set(json, "mem_dst", mem_dst->json());
    json_object_set(json, "memory",  memory->json());
    json_object_set(json, "address", address->json());
    json_object_set(json, "value",   value->json());

    return json;
}