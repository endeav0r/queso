#include "lua.h"

#include "translators/x86queso.h"

static const struct luaL_Reg lqueso_instruction_m [] = {
    {"__gc",  lqueso_instruction_gc},
    {"depth_instructions", lqueso_instruction_depth_instructions},
    {"opcode", lqueso_instruction_opcode},
    {"queso", lqueso_instruction_queso},
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

    return 2;
}

/*
void lqueso_push_instruction_table (lua_State * L, Instruction * instruction) {
    lua_newtable(L);

    lua_pushstring(L, "queso");
    lua_pushstring(L, instruction->queso().c_str());
    lua_settable(L, -3);

    std::list <Instruction *> instructions = instruction->g_depth_instructions();
    if (instructions.size() > 0) {
        lua_pushstring(L, "depth_instructions");
        lua_newtable(L);

        int i = 1;
        std::list <Instruction *> :: iterator it;
        for (it = instructions.begin(); it != instructions.end(); it++) {
            lua_pushinteger(L, i++);
            lqueso_push_instruction_table(L, *it);
            lua_settable(L, -3);
        }

        lua_settable(L, -3);
    }
}
*/


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