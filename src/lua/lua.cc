#include "lua.h"

#include "disassembler/x86Disassembler.h"
#include "translators/x86queso.h"
#include "queso/spicyQueso.h"

#include "luint64.h"

#include <memory>
#include <string>


struct _lqueso_gc_wrapper {
    unsigned int references;
    struct _lqueso_gc_wrapper * parent;
    void * object;
};


//#define LUA_DEBUG

static const struct luaL_Reg lqueso_lib_f [] = {
    {"machine",        lqueso_machine_new},
    {"x86translate",   lqueso_x86translate},
    {"x86disassemble", lqueso_x86disassemble},
    {"elf32",          lqueso_elf32_new},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_instruction_m [] = {
    {"__gc",               lqueso_instruction_gc},
    {"depth_instructions", lqueso_instruction_depth_instructions},
    {"opcode",             lqueso_instruction_opcode},
    {"queso",              lqueso_instruction_queso},
    {"g_pc",               lqueso_instruction_g_pc},
    {"g_vIndex",           lqueso_instruction_g_vIndex},
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
    {"__gc",                lqueso_quesoGraph_gc},
    {"dotGraph",            lqueso_quesoGraph_dotGraph},
    {"g_vertices",          lqueso_quesoGraph_g_vertices},
    {"ssa",                 lqueso_quesoGraph_ssa},
    {"smtlib2Declarations", lqueso_quesoGraph_smtlib2Declarations},
    {"smtlib2",             lqueso_quesoGraph_smtlib2},
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
    {NULL, NULL}
};


LUALIB_API int luaopen_lqueso (lua_State * L) {
    luaL_newmetatable(L, "lqueso.instruction");
    luaL_setfuncs(L, lqueso_instruction_m, 0);
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
    const char * bytes = luaL_checklstring(L, -1, &size);

    if (bytes == NULL)
        return 0;

    QuesoX86 quesoX86;
    Instruction * instruction = quesoX86.translate((const uint8_t *) bytes, size);
    lua_pop(L, 1);

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
        lqueso_instruction_push(L, *it);
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
    lua_pop(L, 1);

    luint64_push(L, instruction->g_pc());
    return 1;
}


int lqueso_instruction_g_vIndex (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    luint64_push(L, instruction->g_vIndex());

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
    uint64_t entry_vId = luint64_check(L, 2);

    SpicyQueso::ssa(quesoGraph, entry_vId);

    lua_pop(L, 2);

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

    lua_pushinteger(L, memoryModel->g_byte(address));

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


int lqueso_elf32_symbols (lua_State * L) {
    Elf32 * elf32 = lqueso_elf32_check(L, -1);
    lua_pop(L, 1);

    lua_newtable(L);

    std::list <LoaderSymbol> symbols = elf32->symbols();
    std::list <LoaderSymbol> :: iterator it;
    printf("got %d symbols\n", (int) symbols.size());fflush(stdout);
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
        }

        lua_settable(L, -3);
    }

    printf("done with symbols\n");fflush(stdout);

    return 1;
}