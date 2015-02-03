#ifndef lua_HEADER
#define lua_HEADER

extern "C" {
#ifdef CYGWIN
#include <lua.h>
#include <lualib.h>
#include <lauxlib.h>
#else
#include <lua5.2/lua.h>
#include <lua5.2/lualib.h>
#include <lua5.2/lauxlib.h>
#endif
}

#include <memory>

#include "graph/quesoGraph.h"
#include "loader/elf32.h"
#include "machine/machine.h"
#include "queso/queso.h"

extern "C" {

LUALIB_API int luaopen_lqueso (lua_State * L);

int lqueso_x86translate    (lua_State * L);
int lqueso_x86disassemble  (lua_State * L);
int lqueso_x86acyclicDepth (lua_State * L);
int lqueso_x86treeDepth    (lua_State * L);
int lqueso_variable        (lua_State * L);
int lqueso_array           (lua_State * L);
int lqueso_constant        (lua_State * L);
int lqueso_store           (lua_State * L);
int lqueso_assign          (lua_State * L);
int lqueso_quesoGraph      (lua_State * L);

Instruction * lqueso_instruction_check (lua_State * L, int position);
int lqueso_instruction_push                     (lua_State * L, Instruction * instruction);
int lqueso_instruction_absorb                   (lua_State * L, Instruction * instruction);
int lqueso_instruction_gc                       (lua_State * L);
int lqueso_instruction_queso                    (lua_State * L);
int lqueso_instruction_depth_instructions       (lua_State * L);
int lqueso_instruction_opcode                   (lua_State * L);
int lqueso_instruction_g_pc                     (lua_State * L);
int lqueso_instruction_g_vIndex                 (lua_State * L);
int lqueso_instruction_flatten                  (lua_State * L);
int lqueso_instruction_operand_written          (lua_State * L);
int lqueso_instruction_operands_read            (lua_State * L);
int lqueso_instruction_g_successors             (lua_State * L);
int lqueso_instruction_g_predecessors           (lua_State * L);
int lqueso_instruction_json                     (lua_State * L);
int lqueso_instruction_ssa                      (lua_State * L);
int lqueso_instruction_replace_operand          (lua_State * L);
int lqueso_instruction_replace_with_assign      (lua_State * L);
int lqueso_instruction_replace_with_instruction (lua_State * L);
int lqueso_instruction_address                  (lua_State * L);
int lqueso_instruction_value                    (lua_State * L);

Operand * lqueso_operand_check (lua_State * L, int position);
int lqueso_operand_push    (lua_State * L, const Operand * operand);
int lqueso_operand_gc      (lua_State * L);
int lqueso_operand_type    (lua_State * L);
int lqueso_operand_name    (lua_State * L);
int lqueso_operand_ssa     (lua_State * L);
int lqueso_operand_smtlib2 (lua_State * L);
int lqueso_operand_queso   (lua_State * L);
int lqueso_operand_value   (lua_State * L);
int lqueso_operand_bits    (lua_State * L);

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
int lqueso_quesoGraph_absorb                  (lua_State * L, QuesoGraph * quesoGraph);
int lqueso_quesoGraph_gc                      (lua_State * L);
int lqueso_quesoGraph_dotGraph                (lua_State * L);
int lqueso_quesoGraph_g_vertices              (lua_State * L);
int lqueso_quesoGraph_ssa                     (lua_State * L);
int lqueso_quesoGraph_smtlib2Declarations     (lua_State * L);
int lqueso_quesoGraph_smtlib2                 (lua_State * L);
int lqueso_quesoGraph_slice_backward          (lua_State * L);
int lqueso_quesoGraph_slice_backward_thin     (lua_State * L);
int lqueso_quesoGraph_blockize                (lua_State * L);
int lqueso_quesoGraph_json                    (lua_State * L);
int lqueso_quesoGraph_dead_code_elimination   (lua_State * L);
int lqueso_quesoGraph_constant_fold_propagate (lua_State * L);
int lqueso_quesoGraph_replace_operand         (lua_State * L);
int lqueso_quesoGraph_shadowGraph             (lua_State * L);
int lqueso_quesoGraph_absorbInstruction       (lua_State * L);
int lqueso_quesoGraph_addEdge                 (lua_State * L);

MemoryModel * lqueso_memoryModel_check (lua_State * L, int position);
int lqueso_memoryModel_push   (lua_State * L, MemoryModel * memoryModel);
int lqueso_memoryModel_gc     (lua_State * L);
int lqueso_memoryModel_s_byte (lua_State * L);
int lqueso_memoryModel_g_byte (lua_State * L);

Elf32 * lqueso_elf32_check (lua_State * L, int position);
int lqueso_elf32_new         (lua_State * L);
int lqueso_elf32_gc          (lua_State * L);
int lqueso_elf32_entry       (lua_State * L);
int lqueso_elf32_memoryModel (lua_State * L);
int lqueso_elf32_symbols     (lua_State * L);
int lqueso_elf32_relocs      (lua_State * L);
int lqueso_elf32_sections    (lua_State * L);

}

#endif