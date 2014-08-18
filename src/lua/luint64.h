#ifndef lua_uint64_HEADER
#define lua_uin64_HEADER

extern "C" {
#include <lua.h>
#include <lualib.h>
#include <lauxlib.h>
}

#include <inttypes.h>

int luaopen_luint64 (lua_State * L);

int      luint64_push  (lua_State * L, uint64_t value);
uint64_t luint64_check (lua_State * L, int position);

int luint32          (lua_State * L);
int luint64          (lua_State * L);
int luint64_add      (lua_State * L);
int luint64_sub      (lua_State * L);
int luint64_mul      (lua_State * L);
int luint64_div      (lua_State * L);
int luint64_mod      (lua_State * L);
int luint64_eq       (lua_State * L);
int luint64_lt       (lua_State * L);
int luint64_le       (lua_State * L);
int luint64_tostring (lua_State * L);
int luint64_number   (lua_State * L);


#endif