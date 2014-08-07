#include "lua.h"

#include "x86queso.h"

static const struct luaL_Reg lqueso_lib_f [] = {
    {"x86translate", lqueso_x86translate},
    {NULL, NULL}
};

LUALIB_API int luaopen_lqueso (lua_State * L) {
    luaL_register(L, "lqueso", lqueso_lib_f);

    return 0;
}


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

    lqueso_push_instruction_table(L, instruction);

    return 1;
}