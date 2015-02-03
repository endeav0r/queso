#include "lua.h"

#include "disassembler/x86Disassembler.h"
#include "translators/x86queso.h"
#include "queso/spicyQueso.h"

#include "luint64.h"

#include <iostream>
#include <jansson.h>
#include <memory>
#include <string>


struct _lqueso_gc_wrapper {
    unsigned int references;
    struct _lqueso_gc_wrapper * parent;
    void * object;
};


//#define LUA_DEBUG

static const struct luaL_Reg lqueso_lib_f [] = {
    {"machine",         lqueso_machine_new},
    {"x86translate",    lqueso_x86translate},
    {"x86disassemble",  lqueso_x86disassemble},
    {"x86acyclicDepth", lqueso_x86acyclicDepth},
    {"x86treeDepth",    lqueso_x86treeDepth},
    {"elf32",           lqueso_elf32_new},
    {"variable",        lqueso_variable},
    {"array",           lqueso_array},
    {"constant",        lqueso_constant},
    {"store",           lqueso_store},
    {"assign",          lqueso_assign},
    {"quesoGraph",      lqueso_quesoGraph},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_instruction_m [] = {
    {"__gc",                     lqueso_instruction_gc},
    {"depth_instructions",       lqueso_instruction_depth_instructions},
    {"opcode",                   lqueso_instruction_opcode},
    {"queso",                    lqueso_instruction_queso},
    {"g_pc",                     lqueso_instruction_g_pc},
    {"g_vIndex",                 lqueso_instruction_g_vIndex},
    {"flatten",                  lqueso_instruction_flatten},
    {"operand_written",          lqueso_instruction_operand_written},
    {"operands_read",            lqueso_instruction_operands_read},
    {"g_successors",             lqueso_instruction_g_successors},
    {"g_predecessors",           lqueso_instruction_g_predecessors},
    {"json",                     lqueso_instruction_json},
    {"ssa",                      lqueso_instruction_ssa},
    {"replace_operand",          lqueso_instruction_replace_operand},
    {"replace_with_assign",      lqueso_instruction_replace_with_assign},
    {"replace_with_instruction", lqueso_instruction_replace_with_instruction},
    {"address",                  lqueso_instruction_address},
    {"value",                    lqueso_instruction_value},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_operand_m [] = {
    {"__gc",    lqueso_operand_gc},
    {"type",    lqueso_operand_type},
    {"name",    lqueso_operand_name},
    {"ssa",     lqueso_operand_ssa},
    {"smtlib2", lqueso_operand_smtlib2},
    {"queso",   lqueso_operand_queso},
    {"value",   lqueso_operand_value},
    {"bits",    lqueso_operand_bits},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_machineVariable_m [] = {
    {"__gc",  lqueso_machineVariable_gc},
    {"name",  lqueso_machineVariable_name},
    {"value", lqueso_machineVariable_value},
    {"bits",  lqueso_machineVariable_bits},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_machine_m [] = {
    {"__gc",              lqueso_machine_gc},
    {"s_memory",          lqueso_machine_s_memory},
    {"g_memory",          lqueso_machine_g_memory},
    {"s_variable",        lqueso_machine_s_variable},
    {"g_variable",        lqueso_machine_g_variable},
    {"g_memoryModel",     lqueso_machine_g_memoryModel},
    {"concreteExecution", lqueso_machine_concreteExecution},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_quesoGraph_m [] = {
    {"__gc",                    lqueso_quesoGraph_gc},
    {"dotGraph",                lqueso_quesoGraph_dotGraph},
    {"g_vertices",              lqueso_quesoGraph_g_vertices},
    {"ssa",                     lqueso_quesoGraph_ssa},
    {"smtlib2Declarations",     lqueso_quesoGraph_smtlib2Declarations},
    {"smtlib2",                 lqueso_quesoGraph_smtlib2},
    {"slice_backward",          lqueso_quesoGraph_slice_backward},
    {"slice_backward_thin",     lqueso_quesoGraph_slice_backward_thin},
    {"blockize",                lqueso_quesoGraph_blockize},
    {"json",                    lqueso_quesoGraph_json},
    {"dead_code_elimination",   lqueso_quesoGraph_dead_code_elimination},
    {"constant_fold_propagate", lqueso_quesoGraph_constant_fold_propagate},
    {"replace_operand",         lqueso_quesoGraph_replace_operand},
    {"shadowGraph",             lqueso_quesoGraph_shadowGraph},
    {"absorbInstruction",       lqueso_quesoGraph_absorbInstruction},
    {"addEdge",                 lqueso_quesoGraph_addEdge},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_memoryModel_m [] = {
    {"__gc",   lqueso_memoryModel_gc},
    {"s_byte", lqueso_memoryModel_s_byte},
    {"g_byte", lqueso_memoryModel_g_byte},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_elf32_m [] = {
    {"__gc",        lqueso_elf32_gc},
    {"entry",       lqueso_elf32_entry},
    {"memoryModel", lqueso_elf32_memoryModel},
    {"symbols",     lqueso_elf32_symbols},
    {"relocs",      lqueso_elf32_relocs},
    {"sections",    lqueso_elf32_sections},
    {NULL, NULL}
};


LUALIB_API int luaopen_lqueso (lua_State * L) {
    luaL_newmetatable(L, "lqueso.instruction");
    luaL_setfuncs(L, lqueso_instruction_m, 0);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.operand");
    luaL_setfuncs(L, lqueso_operand_m, 0);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.machineVariable");
    luaL_setfuncs(L, lqueso_machineVariable_m, 0);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.machine");
    luaL_setfuncs(L, lqueso_machine_m, 0);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.quesoGraph");
    luaL_setfuncs(L, lqueso_quesoGraph_m, 0);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.memoryModel");
    luaL_setfuncs(L, lqueso_memoryModel_m, 0);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.elf32");
    luaL_setfuncs(L, lqueso_elf32_m, 0);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_requiref(L, "luint64", luaopen_luint64, 1);

    luaL_newlib(L, lqueso_lib_f);

    return 1;
}

int lqueso_x86translate (lua_State * L) {
    size_t size;
    const char * bytes = luaL_checklstring(L, 1, &size);

    if (bytes == NULL)
        return 0;

    QuesoX86 quesoX86;
    Instruction * instruction = NULL;
    if (lua_isuserdata(L, 2)) {
        uint64_t pc = luint64_check(L, 2);
        instruction = quesoX86.translate((const uint8_t *) bytes, size, pc);
    }
    else
        instruction = quesoX86.translate((const uint8_t *) bytes, size);

    if (instruction == NULL)
        return 0;

    lqueso_instruction_push(L, instruction);

    return 1;
}


int lqueso_x86disassemble (lua_State * L) {
    uint64_t entry = luint64_check(L, 1);
    MemoryModel * memoryModel = lqueso_memoryModel_check(L, 2);

    lua_pop(L, 2);

    QuesoGraph * quesoGraph = X86Disassembler::disassemble(entry, memoryModel);

    lqueso_quesoGraph_absorb(L, quesoGraph);

    return 1;
}


int lqueso_x86acyclicDepth (lua_State * L) {
    uint64_t entry = luint64_check(L, 1);
    MemoryModel * memoryModel = lqueso_memoryModel_check(L, 2);
    unsigned int depth = luaL_checknumber(L, 3);

    lua_pop(L, 3);

    QuesoGraph * quesoGraph = X86Disassembler::acyclicDepth(entry, memoryModel, depth);

    lqueso_quesoGraph_absorb(L, quesoGraph);

    return 1;
}


int lqueso_x86treeDepth (lua_State * L) {
    uint64_t entry = luint64_check(L, 1);
    MemoryModel * memoryModel = lqueso_memoryModel_check(L, 2);
    unsigned int depth = luaL_checknumber(L, 3);

    lua_pop(L, 3);

    QuesoGraph * quesoGraph = X86Disassembler::treeDepth(entry, memoryModel, depth);

    lqueso_quesoGraph_absorb(L, quesoGraph);

    return 1;
}


int lqueso_variable (lua_State * L) {
    unsigned int bits = luaL_checkinteger(L, 1);
    const char * name = luaL_checkstring(L, 2);

    Variable variable(bits, name);

    if (lua_isnumber(L, 3))
        variable.s_ssa(luaL_checkinteger(L, 3));

    lua_pop(L, 3);

    lqueso_operand_push(L, &variable);

    return 1;
}


int lqueso_array (lua_State * L) {
    unsigned int bits = luaL_checkinteger(L, 1);
    const char * name = luaL_checkstring(L, 2);
    unsigned int address_bits = luaL_checkinteger(L, 3);

    Array array(bits, name, address_bits);

    if (lua_isnumber(L, 4))
        array.s_ssa(luaL_checkinteger(L, 4));

    lqueso_operand_push(L, &array);

    return 1;
}


int lqueso_constant (lua_State * L) {
    unsigned int bits = luaL_checkinteger(L, 1);
    uint64_t value = luint64_check(L, 2);

    lua_pop(L, 2);

    Constant constant(bits, value);

    lqueso_operand_push(L, &constant);

    return 1;
}


int lqueso_quesoGraph (lua_State * L) {
    QuesoGraph * quesoGraph = new QuesoGraph;

    lqueso_quesoGraph_absorb(L, quesoGraph);

    return 1;
}


int lqueso_store (lua_State * L) {
    Operand * operand_0 = lqueso_operand_check(L, 1);
    Operand * operand_1 = lqueso_operand_check(L, 2);
    Operand * operand_2 = lqueso_operand_check(L, 3);

    Array * mem = dynamic_cast<Array *>(operand_0);
    if (mem == NULL)
        luaL_error(L, "first argument must be array");

    InstructionStore store(mem, operand_1, operand_2);

    lqueso_instruction_push(L, &store);

    return 1;
}


int lqueso_assign (lua_State * L) {
    Operand * dstOperand = lqueso_operand_check(L, 1);
    Operand * src = lqueso_operand_check(L, 2);

    Variable * dst = dynamic_cast<Variable *>(dstOperand);
    if (dst == NULL)
        luaL_error(L, "first argument must be variable");

    InstructionAssign assign(dst, src);

    lqueso_instruction_push(L, &assign);

    return 1;
}


/**********************************************************
* lqueso_instruction
**********************************************************/


int lqueso_instruction_push (lua_State * L, Instruction * instruction) {
    Instruction ** luaIns = (Instruction **) lua_newuserdata(L, sizeof(Instruction **));
    luaL_getmetatable(L, "lqueso.instruction");
    lua_setmetatable(L, -2);

    *luaIns = instruction->copy();

    return 1;
}


int lqueso_instruction_absorb (lua_State * L, Instruction * instruction) {
    Instruction ** luaIns = (Instruction **) lua_newuserdata(L, sizeof(Instruction **));
    luaL_getmetatable(L, "lqueso.instruction");
    lua_setmetatable(L, -2);

    *luaIns = instruction;

    return 1;
}


Instruction * lqueso_instruction_check (lua_State * L, int position) {
    Instruction * instruction;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.instruction");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.instruction expected");
    instruction = (Instruction *) *userdata;
    return instruction;
}


int lqueso_instruction_gc (lua_State * L) {
    #ifdef LUA_DEBUG
    printf("lqueso_instruction_gc\n");fflush(stdout);
    #endif

    lua_getuservalue(L, -1);
    if (lua_isnil(L, -1) == 0) {
        lua_pop(L, 2);
        return 0;
    }
    lua_pop(L, 1);

    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    delete instruction;

    #ifdef LUA_DEBUG
    printf("lqueso_instruction_gc done\n");fflush(stdout);
    #endif

    return 0;
}


int lqueso_instruction_queso (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    lua_pushstring(L, instruction->queso().c_str());

    return 1;
}


int lqueso_instruction_depth_instructions (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    lua_newtable(L);
    int i = 1;
    std::list <Instruction *> :: const_iterator it;
    for (it = instruction->g_depth_instructions().begin();
         it != instruction->g_depth_instructions().end();
         it++) {
        lua_pushinteger(L, i++);
        lqueso_instruction_absorb(L, *it);
        lua_newtable(L);
        lua_pushstring(L, "parent_instruction");
        lua_pushvalue(L, 1);
        lua_settable(L, -3);
        lua_setuservalue(L, -2);
        lua_settable(L, -3);
    }

    return 1;
}


int lqueso_instruction_opcode (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    lua_pushstring(L, QuesoOpcodeStrings[instruction->g_opcode()]);
    return 1;
}


int lqueso_instruction_g_pc (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);

    if (instruction->g_pc_set())
        luint64_push(L, instruction->g_pc());
    else
        lua_pushnil(L);

    return 1;
}


int lqueso_instruction_g_vIndex (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    luint64_push(L, instruction->g_vIndex());

    return 1;
}


int lqueso_instruction_flatten (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    //lua_pop(L, 1);

    std::list <Instruction *> flattened = instruction->flatten();
    std::list <Instruction *> :: iterator it;
    lua_newtable(L);
    int i = 1;
    for (it = flattened.begin(); it != flattened.end(); it++) {
        lua_pushinteger(L, i++);
        lqueso_instruction_absorb(L, *it);
        lua_newtable(L);
        lua_pushstring(L, "parent_instruction");
        lua_pushvalue(L, 1);
        lua_settable(L, -3);
        lua_setuservalue(L, -2);
        lua_settable(L, -3);
    }

    return 1;
}


int lqueso_instruction_operand_written (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    if (instruction->operand_written() == NULL)
        lua_pushnil(L);
    else
        lqueso_operand_push(L, instruction->operand_written());

    return 1;
}


int lqueso_instruction_operands_read (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    std::list <Operand *> operands = instruction->operands_read();
    lua_pop(L, 1);

    std::list <Operand *> :: iterator it;
    lua_newtable(L);
    int i = 1;
    for (it = operands.begin(); it != operands.end(); it++) {
        lua_pushinteger(L, i++);
        lqueso_operand_push(L, *it);
        lua_settable(L, -3);
    }

    return 1;
}


int lqueso_instruction_g_successors (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    const std::list <GraphEdge *> successors = instruction->g_successors();

    lua_pop(L, 1);
    lua_newtable(L);

    unsigned int i = 1;
    std::list <GraphEdge *> :: const_iterator it;
    for (it = successors.begin(); it != successors.end(); it++) {
        QuesoEdge * quesoEdge = (QuesoEdge *) dynamic_cast<QuesoEdge *>(*it);

        lua_pushinteger(L, i++);
        luint64_push(L, quesoEdge->g_tail()->g_vIndex());
        lua_settable(L, -3);
    }

    return 1;
}


int lqueso_instruction_g_predecessors (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    const std::list <GraphEdge *> predecessors = instruction->g_predecessors();

    lua_pop(L, 1);
    lua_newtable(L);

    unsigned int i = 1;
    std::list <GraphEdge *> :: const_iterator it;
    for (it = predecessors.begin(); it != predecessors.end(); it++) {
        QuesoEdge * quesoEdge = (QuesoEdge *) dynamic_cast<QuesoEdge *>(*it);

        lua_pushinteger(L, i++);
        luint64_push(L, quesoEdge->g_head()->g_vIndex());
        lua_settable(L, -3);
    }

    return 1;
}


int lqueso_instruction_json (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);

    json_t * json = instruction->json();

    lua_pop(L, 1);

    char * json_string = json_dumps(json, JSON_COMPACT);

    lua_pushstring(L, json_string);

    free(json_string);
    json_decref(json);

    return 1;
}


int lqueso_instruction_ssa (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);

    SpicyQueso::ssa_instruction(instruction);

    lua_pop(L, 1);

    return 0;
}


int lqueso_instruction_replace_operand (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, 1);
    const Operand * needle     = lqueso_operand_check(L, 2);
    const Operand * newOperand = lqueso_operand_check(L, 3);

    //printf("needle: %s\n", needle->queso().c_str());

    std::list <Instruction *> flattened = instruction->flatten();
    std::list <Instruction *> :: iterator it;
    bool result = false;
    for (it = flattened.begin(); it != flattened.end(); it++) {
        if (SpicyQueso::replace_operand_instruction(*it, needle->queso(), newOperand)) {
            //printf("replaced %s\n", (*it)->queso().c_str());
            result = true;
        }
    }

    if (result)
        lua_pushboolean(L, 1);
    else
        lua_pushboolean(L, 0);

    return 1;
}


int lqueso_instruction_replace_with_assign (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, 1);
    const Operand * needle = lqueso_operand_check(L, 2);
    const Operand * value  = lqueso_operand_check(L, 3);

    const Variable * needleVar = dynamic_cast<const Variable *>(needle);
    if (needleVar == NULL)
        luaL_error(L, "first argument needs to be a queso variable");

    lua_pushboolean(L, SpicyQueso::replace_with_assign(instruction, needleVar, value));

    return 1;
}


int lqueso_instruction_replace_with_instruction (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, 1);
    const Operand * needle = lqueso_operand_check(L, 2);
    const Instruction * newInstruction = lqueso_instruction_check(L, 3);

    lua_pushboolean(L, SpicyQueso::replace_with_instruction(instruction, needle, newInstruction));

    return 1;
}


int lqueso_instruction_address (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, 1);

    if (InstructionLoad * load = dynamic_cast<InstructionLoad *>(instruction))
        lqueso_operand_push(L, load->g_address());
    else if (InstructionStore * store = dynamic_cast<InstructionStore *>(instruction))
        lqueso_operand_push(L, store->g_address());
    else
        luaL_error(L, "instruction:address must be called over a load or store");

    return 1;
}


int lqueso_instruction_value (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, 1);

    if (InstructionStore * store = dynamic_cast<InstructionStore *>(instruction))
        lqueso_operand_push(L, store->g_value());
    else
        luaL_error(L, "instruction:value must be called over a store");

    return 1;
}


/**********************************************************
* lqueso_operand
**********************************************************/


int lqueso_operand_push (lua_State * L, const Operand * operand) {
    Operand ** oper = (Operand **) lua_newuserdata(L, sizeof(Operand **));
    luaL_getmetatable(L, "lqueso.operand");
    lua_setmetatable(L, -2);

    *oper = operand->copy();

    return 1;
}


Operand * lqueso_operand_check (lua_State * L, int position) {
    Operand * operand;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.operand");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.operand expected");
    operand = (Operand *) *userdata;
    return operand;
}


int lqueso_operand_gc (lua_State * L) {
    #ifdef LUA_DEBUG
    printf("lqueso_operand_gc\n");fflush(stdout);
    #endif

    Operand * operand = lqueso_operand_check(L, -1);
    lua_pop(L, 1);

    delete operand;

    #ifdef LUA_DEBUG
    printf("lqueso_operand_gc done\n");fflush(stdout);
    #endif
    return 0;
}


int lqueso_operand_type (lua_State * L) {
    Operand * operand = lqueso_operand_check(L, -1);
    lua_pop(L, 1);

    switch (operand->g_type()) {
    case VARIABLE : lua_pushstring(L, "VARIABLE"); break;
    case CONSTANT : lua_pushstring(L, "CONSTANT"); break;
    case ARRAY    : lua_pushstring(L, "ARRAY");    break;
    default :
        lua_pushnil(L);
        break;
    }

    return 1;
}


int lqueso_operand_name (lua_State * L) {
    Operand * operand = lqueso_operand_check(L, -1);
    lua_pop(L, 1);

    if (Variable * variable = dynamic_cast<Variable *>(operand))
        lua_pushstring(L, variable->g_name().c_str());
    else if (Array * array = dynamic_cast<Array *>(operand))
        lua_pushstring(L, array->g_name().c_str());
    else
        lua_pushnil(L);

    return 1;
}


int lqueso_operand_ssa (lua_State * L) {
    Operand * operand = lqueso_operand_check(L, -1);
    lua_pop(L, 1);

    luint64_push(L, operand->g_ssa());

    return 1;
}


int lqueso_operand_smtlib2 (lua_State * L) {
    Operand * operand = lqueso_operand_check(L, -1);
    lua_pop(L, 1);

    lua_pushstring(L, operand->smtlib2().c_str());

    return 1;
}


int lqueso_operand_queso (lua_State * L) {
    Operand * operand = lqueso_operand_check(L, -1);
    lua_pop(L, 1);

    lua_pushstring(L, operand->queso().c_str());

    return 1;
}


int lqueso_operand_value (lua_State * L) {
    Operand * operand = lqueso_operand_check(L, -1);
    
    if (operand->g_type() != CONSTANT)
        luaL_error(L, "operand:value() can only be called on operands of type CONSTANT");

    // oh wow that was slightly dangerous
    Constant * constant = dynamic_cast<Constant *>(operand);
    luint64_push(L, constant->g_value());

    return 1;
}


int lqueso_operand_bits (lua_State * L) {
    Operand * operand = lqueso_operand_check(L, -1);
    
    lua_pushinteger(L, operand->g_bits());

    return 1;
}


/**********************************************************
* lqueso_machineVariable
**********************************************************/


int lqueso_machineVariable_push (lua_State * L, MachineVariable * machineVariable) {
    MachineVariable ** mVar = (MachineVariable **) lua_newuserdata(L, sizeof(MachineVariable **));
    luaL_getmetatable(L, "lqueso.machineVariable");
    lua_setmetatable(L, -2);

    *mVar = machineVariable->copy();

    return 1;
}


MachineVariable * lqueso_machineVariable_check (lua_State * L, int position) {
    MachineVariable * machineVariable;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.machineVariable");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.machineVariable expected");
    machineVariable = (MachineVariable *) *userdata;
    return machineVariable;
}


int lqueso_machineVariable_gc (lua_State * L) {
    #ifdef LUA_DEBUG
    printf("lqueso_machineVariable_gc\n");fflush(stdout);
    #endif

    MachineVariable * machineVariable = lqueso_machineVariable_check(L, -1);
    lua_pop(L, 1);

    delete machineVariable;

    #ifdef LUA_DEBUG
    printf("lqueso_machineVariable_gc done\n");fflush(stdout);
    #endif
    return 0;
}


int lqueso_machineVariable_name (lua_State * L) {
    MachineVariable * machineVariable = lqueso_machineVariable_check(L, -1);
    lua_pop(L, 1);

    lua_pushstring(L, machineVariable->g_name().c_str());

    return 1;
}


int lqueso_machineVariable_value (lua_State * L) {
    MachineVariable * machineVariable = lqueso_machineVariable_check(L, -1);
    lua_pop(L, 1);

    luint64_push(L, machineVariable->g_value());

    return 1;
}


int lqueso_machineVariable_bits (lua_State * L) {
    MachineVariable * machineVariable = lqueso_machineVariable_check(L, -1);
    lua_pop(L, 1);

    lua_pushnumber(L, machineVariable->g_bits());

    return 1;
}


/**********************************************************
* lqueso_machine
**********************************************************/


int lqueso_machine_new (lua_State * L) {
    Machine ** luaMachine = (Machine **) lua_newuserdata(L, sizeof(Machine **));
    luaL_getmetatable(L, "lqueso.machine");
    lua_setmetatable(L, -2);

    *luaMachine = new Machine;

    return 1;
}


Machine * lqueso_machine_check (lua_State * L, int position) {
    Machine * machine;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.machine");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.machine expected");
    machine = (Machine *) *userdata;
    return machine;
}


int lqueso_machine_gc (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, -1);
    lua_pop(L, 1);

    delete machine;

    return 0;
}


int lqueso_machine_s_memory (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    uint64_t address = luint64_check(L, 2);
    size_t size;
    const char * buf = luaL_checklstring(L, 3, &size);

    machine->s_memory(address, (uint8_t *) buf, size);

    lua_pop(L, 3);

    return 0;
}


int lqueso_machine_g_memory (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    uint64_t address = (uint64_t) luint64_check(L, 2);
    size_t size = (size_t) luaL_checknumber(L, 3);

    MachineBuffer machineBuffer = machine->g_memory(address, size);

    lua_pop(L, 3);

    lua_pushlstring(L,
                    (const char *) machineBuffer.g_bytes(),
                    machineBuffer.g_size());

    return 1;
}


int lqueso_machine_s_variable (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    const char * name = luaL_checkstring(L, 2);
    uint64_t value = (uint64_t) luint64_check(L, 3);
    uint8_t  bits  = (uint8_t)  luaL_checknumber(L, 4);

    uint64_t mask = (((uint64_t) 1) << bits) - 1;

    machine->s_variable(MachineVariable(name, value & mask, bits));

    lua_pop(L, 4);

    return 0;
}


int lqueso_machine_g_variable (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    const char * name = luaL_checkstring(L, 2);

    MachineVariable machineVariable = machine->g_variable(name);

    lua_pop(L, 2);

    lqueso_machineVariable_push(L, &machineVariable);

    return 1;
}


int lqueso_machine_g_memoryModel (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    lua_pop(L, 1);

    MemoryModel memoryModel = machine->g_memoryModel();
    lqueso_memoryModel_push(L, &memoryModel);

    return 1;
}


int lqueso_machine_concreteExecution (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    Instruction * instruction = lqueso_instruction_check(L, 2);

    machine->concreteExecution(instruction);

    lua_pop(L, 2);

    return 0;
}


/**********************************************************
* lqueso_quesoGraph
**********************************************************/


int lqueso_quesoGraph_absorb (lua_State * L, QuesoGraph * quesoGraph) {
    QuesoGraph ** qGraph = (QuesoGraph **) lua_newuserdata(L, sizeof(QuesoGraph **));
    luaL_getmetatable(L, "lqueso.quesoGraph");
    lua_setmetatable(L, -2);

    *qGraph = quesoGraph;

    return 1;
}


QuesoGraph * lqueso_quesoGraph_check (lua_State * L, int position) {
    QuesoGraph * quesoGraph;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.quesoGraph");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.quesoGraph expected");
    quesoGraph = (QuesoGraph *) *userdata;
    return quesoGraph;
}


int lqueso_quesoGraph_gc (lua_State * L) {
    #ifdef LUA_DEBUG
    printf("lqueso_quesoGraph_gc\n");fflush(stdout);
    #endif

    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, -1);
    lua_pop(L, 1);

    delete quesoGraph;

    #ifdef LUA_DEBUG
    printf("lqueso_quesoGraph_gc\n");fflush(stdout);
    #endif

    return 0;
}


int lqueso_quesoGraph_dotGraph (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, -1);
    lua_pop(L, 1);

    std::string dotGraph = quesoGraph->dotGraph();
    lua_pushstring(L, dotGraph.c_str());

    return 1;
}


int lqueso_quesoGraph_g_vertices (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, -1);

    lua_newtable(L);

    int i = 1;

    std::map <uint64_t, GraphVertex *> :: iterator it;
    for (it = quesoGraph->g_vertices().begin(); it != quesoGraph->g_vertices().end(); it++) {
        Instruction * instruction = dynamic_cast<Instruction *>(it->second);
        if (instruction == NULL)
            continue;

        lua_pushinteger(L, i++);
        lqueso_instruction_absorb(L, instruction);
        lua_newtable(L);
        lua_pushstring(L, "quesoGraph");
        lua_pushvalue(L, 1);
        lua_settable(L, -3);
        lua_setuservalue(L, -2);
        lua_settable(L, -3);
    }

    return 1;
}


int lqueso_quesoGraph_ssa (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);

    SpicyQueso::ssa2(quesoGraph);

    lua_pop(L, 1);

    return 0;
}


int lqueso_quesoGraph_smtlib2Declarations (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);

    std::string smtlib2Declarations = quesoGraph->smtlib2Declarations();

    lua_pop(L, 1);

    lua_pushstring(L, smtlib2Declarations.c_str());

    return 1;
}


int lqueso_quesoGraph_smtlib2 (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);

    std::string smtlib2 = quesoGraph->smtlib2();

    lua_pop(L, 1);

    lua_pushstring(L, smtlib2.c_str());

    return 1;
}


int lqueso_quesoGraph_slice_backward (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);
    Operand * operand = lqueso_operand_check(L, 2);

    QuesoGraph * result = quesoGraph->slice_backward(operand);

    lua_pop(L, 2);

    if (result == NULL)
        lua_pushnil(L);
    else
        lqueso_quesoGraph_absorb(L, result);

    return 1;
}


int lqueso_quesoGraph_slice_backward_thin (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);
    Operand * operand = lqueso_operand_check(L, 2);

    QuesoGraph * result = quesoGraph->slice_backward_thin(operand);

    lua_pop(L, 2);

    if (result == NULL)
        lua_pushnil(L);
    else
        lqueso_quesoGraph_absorb(L, result);

    return 1;
}


int lqueso_quesoGraph_blockize (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);

    SpicyQueso::blockize(quesoGraph);

    lua_pop(L, 1);

    return 0;
}


int lqueso_quesoGraph_json (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, -1);

    json_t * json = quesoGraph->json();

    lua_pop(L, 1);

    char * json_string = json_dumps(json, JSON_COMPACT);

    lua_pushstring(L, json_string);

    free(json_string);
    json_decref(json);

    return 1;
}


int lqueso_quesoGraph_dead_code_elimination (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, -1);

    SpicyQueso::dead_code_elimination(quesoGraph);

    lua_pop(L, 1);

    return 0;
}


int lqueso_quesoGraph_constant_fold_propagate (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, -1);

    SpicyQueso::constant_fold_propagate(quesoGraph);

    lua_pop(L, 1);

    return 0;
}


int lqueso_quesoGraph_replace_operand (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);
    Operand * needle = lqueso_operand_check(L, 2);
    Operand * operand = lqueso_operand_check(L, 3);

    SpicyQueso::replace_operand(quesoGraph, needle, operand);

    lua_pop(L, 3);

    return 0;
}


int lqueso_quesoGraph_shadowGraph (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);

    lqueso_quesoGraph_absorb(L, SpicyQueso::shadowGraph(quesoGraph));

    return 1;
}


int lqueso_quesoGraph_absorbInstruction (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);
    Instruction * instruction = lqueso_instruction_check(L, 2);

    if (lua_isnumber(L, 3)) {
        uint64_t vIndex = (uint64_t) luaL_checkinteger(L, 3);
        quesoGraph->absorbInstruction(instruction, vIndex);
    }
    else
        quesoGraph->absorbInstruction(instruction);

    lua_newtable(L);
    lua_pushstring(L, "quesoGraph");
    lua_pushvalue(L, 1);
    lua_settable(L, -3);
    lua_setuservalue(L, 2);

    return 0;
}


int lqueso_quesoGraph_addEdge (lua_State * L) {
    QuesoGraph * quesoGraph = lqueso_quesoGraph_check(L, 1);
    uint64_t head = luint64_check(L, 2);
    uint64_t tail = luint64_check(L, 3);

    quesoGraph->absorbEdge(new QuesoEdge(quesoGraph, head, tail, CFT_NORMAL));

    return 0;
}


/**********************************************************
* lqueso_memoryModel
**********************************************************/


int lqueso_memoryModel_push (lua_State * L, MemoryModel * memoryModel) {
    MemoryModel ** mModel = (MemoryModel **) lua_newuserdata(L, sizeof(MemoryModel **));
    luaL_getmetatable(L, "lqueso.memoryModel");
    lua_setmetatable(L, -2);

    *mModel = memoryModel->copy();

    return 1;
}


MemoryModel * lqueso_memoryModel_check (lua_State * L, int position) {
    MemoryModel * memoryModel;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.memoryModel");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.memoryModel expected");
    memoryModel = (MemoryModel *) *userdata;
    return memoryModel;
}


int lqueso_memoryModel_gc (lua_State * L) {
    #ifdef LUA_DEBUG
    printf("lqueso_memoryModel_gc\n");fflush(stdout);
    #endif

    MemoryModel * memoryModel = lqueso_memoryModel_check(L, -1);
    lua_pop(L, 1);

    delete memoryModel;

    #ifdef LUA_DEBUG
    printf("lqueso_memoryModel_gc done\n");fflush(stdout);
    #endif
    return 0;
}


int lqueso_memoryModel_s_byte (lua_State * L) {
    MemoryModel * memoryModel = lqueso_memoryModel_check(L, 1);
    uint64_t address = luint64_check(L, 2);
    int byte = luaL_checknumber(L, 3);

    lua_pop(L, 3);

    memoryModel->s_byte(address, byte);

    return 0;
}


int lqueso_memoryModel_g_byte (lua_State * L) {
    MemoryModel * memoryModel = lqueso_memoryModel_check(L, 1);
    uint64_t address = luint64_check(L, 2);

    lua_pop(L, 2);

    lua_pushinteger(L, (unsigned int) memoryModel->g_byte(address));

    return 1;
}


/**********************************************************
* lqueso_elf32
**********************************************************/


int lqueso_elf32_new (lua_State * L) {
    const char * filename = luaL_checkstring(L, 1);
    lua_pop(L, 1);

    Elf32 * elf32 = Elf32::load(filename);
    if (elf32 == NULL)
        luaL_error(L, "invalid elf32 file");

    Elf32 ** eelf32 = (Elf32 **) lua_newuserdata(L, sizeof(Elf32 **));
    luaL_getmetatable(L, "lqueso.elf32");
    lua_setmetatable(L, -2);

    *eelf32 = elf32;

    return 1;
}


Elf32 * lqueso_elf32_check (lua_State * L, int position) {
    Elf32 * elf32;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.elf32");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.elf32 expected");
    elf32 = (Elf32 *) *userdata;
    return elf32;
}


int lqueso_elf32_gc (lua_State * L) {
    #ifdef LUA_DEBUG
    printf("lqueso_elf32_gc\n");fflush(stdout);
    #endif

    Elf32 * elf32 = lqueso_elf32_check(L, -1);
    lua_pop(L, 1);

    delete elf32;

    #ifdef LUA_DEBUG
    printf("lqueso_elf32_gc done\n");fflush(stdout);
    #endif
    return 0;
}


int lqueso_elf32_entry (lua_State * L) {
    Elf32 * elf32 = lqueso_elf32_check(L, -1);
    lua_pop(L, 1);

    luint64_push(L, elf32->entry());

    return 1;
}


int lqueso_elf32_memoryModel (lua_State * L) {
    Elf32 * elf32 = lqueso_elf32_check(L, -1);
    lua_pop(L, 1);

    MemoryModel memoryModel = elf32->memoryModel();
    lqueso_memoryModel_push(L, &memoryModel);

    return 1;
}


int lqueso_elf32_parse_sym_list (lua_State * L, std::list <LoaderSymbol> symbols) {
    lua_newtable(L);

    std::list <LoaderSymbol> :: iterator it;
    for (it = symbols.begin(); it != symbols.end(); it++) {
        LoaderSymbol & loaderSymbol = *it;

        lua_pushstring(L, loaderSymbol.g_symbol().c_str());
        lua_newtable(L);

        lua_pushstring(L, "symbol");
        lua_pushstring(L, loaderSymbol.g_symbol().c_str());
        lua_settable(L, -3);

        lua_pushstring(L, "address");
        luint64_push(L, loaderSymbol.g_address());
        lua_settable(L, -3);

        switch (loaderSymbol.g_type()) {
        case LST_FUNCTION :
            lua_pushstring(L, "type");
            lua_pushstring(L, "function");
            lua_settable(L, -3);
            break;
        case LST_RELOC :
            lua_pushstring(L, "type");
            lua_pushstring(L, "reloc");
            lua_settable(L, -3);
            break;
        }

        lua_settable(L, -3);
    }

    return 1;
}


int lqueso_elf32_symbols (lua_State * L) {
    Elf32 * elf32 = lqueso_elf32_check(L, -1);
    lua_pop(L, 1);

    return lqueso_elf32_parse_sym_list(L, elf32->symbols());
}


int lqueso_elf32_relocs (lua_State * L) {
    Elf32 * elf32 = lqueso_elf32_check(L, -1);
    lua_pop(L, 1);

    return lqueso_elf32_parse_sym_list(L, elf32->relocs());
}


int lqueso_elf32_sections (lua_State * L) {
    Elf32 * elf32 = lqueso_elf32_check(L, -1);

    std::list <Elf32Section> sections = elf32->sections();
    lua_pop(L, 1);

    lua_newtable(L);

    std::list <Elf32Section> :: iterator it;
    for (it = sections.begin(); it != sections.end(); it++) {
        Elf32Section & section = *it;

        lua_pushstring(L, section.g_name().c_str());
        lua_newtable(L);

        lua_pushstring(L, "address");
        luint64_push(L, section.g_address());
        lua_settable(L, -3);

        lua_pushstring(L, "size");
        luint64_push(L, section.g_size());
        lua_settable(L, -3);

        lua_settable(L, -3);
    }

    return 1;
}