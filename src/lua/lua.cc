#include "lua.h"

#include "translators/x86queso.h"

static const struct luaL_Reg lqueso_instruction_m [] = {
    {"__gc", lqueso_instruction_gc},
    {"depth_instructions", lqueso_instruction_depth_instructions},
    {"opcode", lqueso_instruction_opcode},
    {"queso", lqueso_instruction_queso},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_machineVariable_m [] = {
    {"__gc", lqueso_machineVariable_gc},
    {"name", lqueso_machineVariable_name},
    {"value", lqueso_machineVariable_value},
    {"bits", lqueso_machineVariable_bits},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_machine_m [] = {
    {"__gc", lqueso_machine_gc},
    {"s_memory", lqueso_machine_s_memory},
    {"g_memory", lqueso_machine_g_memory},
    {"s_variable", lqueso_machine_s_variable},
    {"g_variable", lqueso_machine_g_variable},
    {"concreteExecution", lqueso_machine_concreteExecution},
    {NULL, NULL}
};

static const struct luaL_Reg lqueso_lib_f [] = {
    {"x86translate", lqueso_x86translate},
    {NULL, NULL}
};

LUALIB_API int luaopen_lqueso (lua_State * L) {
    luaL_register(L, "lqueso", lqueso_lib_f);

    luaL_newmetatable(L, "lqueso.instruction");
    luaL_register(L, NULL, lqueso_instruction_m);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.machineVariable");
    luaL_register(L, NULL, lqueso_machineVariable_m);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    luaL_newmetatable(L, "lqueso.machine");
    luaL_register(L, NULL, lqueso_machine_m);
    lua_pushstring(L, "__index");
    lua_pushvalue(L, -2);
    lua_settable(L, -3);

    return 4;
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


Instruction * lqueso_instruction_check (lua_State * L, int position) {
    Instruction * instruction;
    void ** userdata = (void **) luaL_checkudata(L, position, "lqueso.instruction");
    luaL_argcheck(L, userdata != NULL, position, "lqueso.instruction expected");
    instruction = (Instruction *) *userdata;
    return instruction;
}


int lqueso_instruction_gc (lua_State * L) {
    Instruction * instruction = lqueso_instruction_check(L, -1);
    lua_pop(L, 1);

    delete instruction;

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
    MachineVariable * machineVariable = lqueso_machineVariable_check(L, -1);
    lua_pop(L, 1);

    delete machineVariable;

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

    lua_pushinteger(L, machineVariable->g_value());

    return 1;
}


int lqueso_machineVariable_bits (lua_State * L) {
    MachineVariable * machineVariable = lqueso_machineVariable_check(L, -1);
    lua_pop(L, 1);

    lua_pushinteger(L, machineVariable->g_bits());

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
    uint64_t address = (uint64_t) luaL_checkinteger(L, 2);
    size_t size;
    const char * buf = luaL_checklstring(L, 3, &size);

    machine->s_memory(address, (uint8_t *) buf, size);

    lua_pop(L, 3);

    return 0;
}


int lqueso_machine_g_memory (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    uint64_t address = (uint64_t) luaL_checkinteger(L, 2);
    size_t size = (size_t) luaL_checkinteger(L, 3);

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
    uint64_t value = (uint64_t) luaL_checkinteger(L, 3);
    uint8_t  bits  = (uint8_t)  luaL_checkinteger(L, 4);

    machine->s_variable(MachineVariable(name, value, bits));

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


int lqueso_machine_concreteExecution (lua_State * L) {
    Machine * machine = lqueso_machine_check(L, 1);
    Instruction * instruction = lqueso_instruction_check(L, 2);

    machine->concreteExecution(instruction);

    lua_pop(L, 2);

    return 0;
}