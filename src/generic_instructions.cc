#include "generic_instructions.h"

#include <sstream>


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
    Constant eight(dst->g_bits(), 8);

    push_depth_instruction(new InstructionLoad(&load8l, memory, address));
    push_depth_instruction(new InstructionAdd(&tmpAddress, address, &one));
    push_depth_instruction(new InstructionLoad(&load8h, memory, &tmpAddress));
    push_depth_instruction(new InstructionAssign(dst, &load8l));
    push_depth_instruction(new InstructionShl(dst, dst, &eight));
    push_depth_instruction(new InstructionOr(dst, dst, &load8h));
}


InstructionLoadLE16 :: ~InstructionLoadLE16 () {
    delete address;
    delete memory;
    delete dst;
}


const std::string InstructionLoadLE16 :: queso () {
    std::stringstream ss;
    ss << "LoadLE16 " << dst->queso() << " = " 
       << memory->queso() << "[" << address->queso() << "]";
    return ss.str();
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
    Variable load8(8, "load8");
    Variable tmpAddress(address->g_bits(), "tmpAddress");
    Constant one(address->g_bits(), 1);
    Variable tmp(dst->g_bits(), "tmpLoad");
    Constant eight(32, 8);

    push_depth_instruction(new InstructionLoad(&load8, memory, address));
    push_depth_instruction(new InstructionAssign(dst, &load8));
    push_depth_instruction(new InstructionShl(dst, dst, &eight));
    push_depth_instruction(new InstructionAdd(&tmpAddress, address, &one));

    push_depth_instruction(new InstructionLoad(&load8, memory, &tmpAddress));
    push_depth_instruction(new InstructionOr(dst, dst, &load8));
    push_depth_instruction(new InstructionShl(dst, dst, &eight));
    push_depth_instruction(new InstructionAdd(&tmpAddress, &tmpAddress, &one));

    push_depth_instruction(new InstructionLoad(&load8, memory, &tmpAddress));
    push_depth_instruction(new InstructionOr(dst, dst, &load8));
    push_depth_instruction(new InstructionShl(dst, dst, &eight));
    push_depth_instruction(new InstructionAdd(&tmpAddress, &tmpAddress, &one));

    push_depth_instruction(new InstructionLoad(&load8, memory, &tmpAddress));
    push_depth_instruction(new InstructionOr(dst, dst, &load8));
}


const std::string InstructionLoadLE32 :: queso () {
    std::stringstream ss;
    ss << "LoadLE32 " << dst->queso() << " = " 
       << memory->queso() << "[" << address->queso() << "]";
    return ss.str();
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


const std::string InstructionStoreLE16 :: queso () {
    std::stringstream ss;
    ss << "StoreLE16 " << memory->queso() << "[" << address->queso() << "]"
       << " = " << value->queso();
    return ss.str();
}


/***********************************************
* InstructionStoreLE32
***********************************************/


InstructionStoreLE32 :: InstructionStoreLE32 (const Array & memory,
                                              const Operand & address,
                                              const Operand & value)
: memory (memory.copy()), address (address.copy()), value (value.copy()) {
    init();
}


InstructionStoreLE32 :: InstructionStoreLE32 (const Array * memory,
                                              const Operand * address,
                                              const Operand * value)
: memory (memory->copy()), address (address->copy()), value (value->copy()) {
    init();
}


InstructionStoreLE32 :: ~InstructionStoreLE32 () {
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


const std::string InstructionStoreLE32 :: queso () {
    std::stringstream ss;
    ss << "StoreLE32 " << memory->queso() << "[" << address->queso() << "]"
       << " = " << value->queso();
    return ss.str();
}