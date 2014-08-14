#include "luint64.h"

#include <cstdlib>

static const struct luaL_Reg luint64_lib_m [] = {
    {"__add",      luint64_add},
    {"__sub",      luint64_sub},
    {"__mul",      luint64_mul},
    {"__div",      luint64_div},
    {"__mod",      luint64_mod},
    {"__eq",       luint64_eq},
    {"__lt",       luint64_lt},
    {"__le",       luint64_le},
    {"__tostring", luint64_tostring},
    {"string",     luint64_tostring},
    {"number",     luint64_number},
    {NULL, NULL}
};



LUALIB_API int luaopen_luint64 (lua_State * L)
{
    luaL_newmetatable(L, "luint64.uint64_t");
    luaL_register    (L, NULL, luint64_lib_m);
    lua_pushstring   (L, "__index");
    lua_pushvalue    (L, -2);
    lua_settable     (L, -3);

    lua_register(L, "luint32", luint32);
    lua_register(L, "luint64", luint64);
    
    return 1;
}


int luint32 (lua_State * L)
{
    uint32_t uint32 = luaL_checknumber(L, -1);

    lua_pop(L, 1);
    return luint64_push(L, uint32);
}


int luint64 (lua_State * L)
{
    uint64_t uint64_value = 0;

    if (lua_isnumber(L, -1)) {
        uint64_value = luaL_checknumber(L, -1);
        lua_pop(L, -1);
    }
    else if (lua_isstring(L, -1)) {
        const char * s = luaL_checkstring(L, -1);
        uint64_value = strtoull(s, NULL, 0);
        lua_pop(L, -1);
    }
    else {
        luaL_error(L, "uint64 must be called with a number or string");
    }

    return luint64_push(L, uint64_value);
}


int luint64_push (lua_State * L, uint64_t value)
{
    uint64_t * value_ptr = (uint64_t *) lua_newuserdata(L, sizeof(uint64_t));
    luaL_getmetatable(L, "luint64.uint64_t");
    lua_setmetatable(L, -2);

    *value_ptr = value;

    return 1;
}


uint64_t luint64_check (lua_State * L, int position)
{
    if (lua_isnumber(L, position))
        return (uint64_t) luaL_checknumber(L, position);

    void * data = luaL_checkudata(L, position, "luint64.uint64_t");
    luaL_argcheck(L, data != NULL, position, "expected uint64");
    return *((uint64_t *) data);
}


int luint64_add (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);
    
    luint64_push(L, lhs + rhs);

    return 1;
}


int luint64_sub (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);
    
    luint64_push(L, lhs - rhs);

    return 1;
}


int luint64_mul (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);
    
    luint64_push(L, lhs * rhs);

    return 1;
}


int luint64_div (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);
    
    luint64_push(L, lhs / rhs);

    return 1;
}


int luint64_mod (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);
    
    luint64_push(L, lhs % rhs);

    return 1;
}


int luint64_eq  (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);

    if (lhs == rhs)
        lua_pushboolean(L, 1);
    else
        lua_pushboolean(L, 0);

    return 1;
}


int luint64_lt  (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);

    if (lhs < rhs)
        lua_pushboolean(L, 1);
    else
        lua_pushboolean(L, 0);

    return 1;
}


int luint64_le  (lua_State * L)
{
    uint64_t lhs = luint64_check(L, -2);
    uint64_t rhs = luint64_check(L, -1);
    lua_pop(L, 2);

    if (lhs <= rhs)
        lua_pushboolean(L, 1);
    else
        lua_pushboolean(L, 0);

    return 1;
}


int luint64_tostring (lua_State * L)
{
    char tmp[64];

    uint64_t value = luint64_check(L, -1);
    lua_pop(L, -1);

    snprintf(tmp, 64, "0x%llx", (unsigned long long) value);

    lua_pushstring(L, tmp);

    return 1;
}


int luint64_number (lua_State * L)
{
    uint64_t value = luint64_check(L, -1);
    lua_pop(L, -1);

    lua_pushnumber(L, (lua_Number) value);

    return 1;
}

