#ifndef lua_HEADER
#define lua_HEADER

#include <lua5.1/lua.h>
#include <lua5.1/lualib.h>
#include <lua5.1/lauxlib.h>

LUALIB_API int luaopen_lqueso (lua_State * L);

int lqueso_x86translate (lua_State * L);

#endif