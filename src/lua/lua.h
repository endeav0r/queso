#ifndef lua_HEADER
#define lua_HEADER

#include <lua5.1/lua.h>
#include <lua5.1/lualib.h>
#include <lua5.1/lauxlib.h>

#include "queso/queso.h"

LUALIB_API int luaopen_lqueso (lua_State * L);

int lqueso_x86translate (lua_State * L);

Instruction * lqueso_instruction_check (lua_State * L, int position);
int lqueso_instruction_push   (lua_State * L, Instruction * instruction);
int lqueso_instruction_gc     (lua_State * L);
int lqueso_instruction_queso  (lua_State * L);
int lqueso_instruction_depth_instructions (lua_State * L);
int lqueso_instruction_opcode (lua_State * L);

#endif