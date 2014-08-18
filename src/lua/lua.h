#ifndef lua_HEADER
#define lua_HEADER

extern "C" {
#include <lua.h>
#include <lualib.h>
#include <lauxlib.h>
}

#include "graph/quesoGraph.h"
#include "loader/elf32.h"
#include "machine/machine.h"
#include "queso/queso.h"

LUALIB_API int luaopen_lqueso (lua_State * L);

int lqueso_x86translate   (lua_State * L);
int lqueso_x86disassemble (lua_State * L);

Instruction * lqueso_instruction_check (lua_State * L, int position);
int lqueso_instruction_push               (lua_State * L, Instruction * instruction);
int lqueso_instruction_gc                 (lua_State * L);
int lqueso_instruction_queso              (lua_State * L);
int lqueso_instruction_depth_instructions (lua_State * L);
int lqueso_instruction_opcode             (lua_State * L);

MachineVariable * lqueso_machineVariable_check (lua_State * L, int position);
int lqueso_machineVariable_push  (lua_State * L, MachineVariable * machineVariable);
int lqueso_machineVariable_gc    (lua_State * L);
int lqueso_machineVariable_name  (lua_State * L);
int lqueso_machineVariable_value (lua_State * L);
int lqueso_machineVariable_bits  (lua_State * L);

Machine * lqueso_machine_check (lua_State * L, int position);
int lqueso_machine_new               (lua_State * L);
int lqueso_machine_gc                (lua_State * L);
int lqueso_machine_s_memory          (lua_State * L);
int lqueso_machine_g_memory          (lua_State * L);
int lqueso_machine_s_variable        (lua_State * L);
int lqueso_machine_g_variable        (lua_State * L);
int lqueso_machine_g_memoryModel     (lua_State * L);
int lqueso_machine_concreteExecution (lua_State * L);

QuesoGraph * lqueso_quesoGraph_check (lua_State * L, int position);
int lqueso_quesoGraph_push     (lua_State * L, QuesoGraph * quesoGraph);
int lqueso_quesoGraph_gc       (lua_State * L);
int lqueso_quesoGraph_dotGraph (lua_State * L);

MemoryModel * lqueso_memoryModel_check (lua_State * L, int position);
int lqueso_memoryModel_push   (lua_State * L, MemoryModel * memoryModel);
int lqueso_memoryModel_gc     (lua_State * L);
int lqueso_memoryModel_s_byte (lua_State * L);
int lqueso_memoryModel_g_byte (lua_State * L);

Elf32 * lqueso_elf32_check (lua_State * L, int position);
int lqueso_elf32_push		 (lua_State * L, Elf32 * elf32);
int lqueso_elf32_new         (lua_State * L);
int lqueso_elf32_gc			 (lua_State * L);
int lqueso_elf32_entry		 (lua_State * L);
int lqueso_elf32_memoryModel (lua_State * L);

#endif