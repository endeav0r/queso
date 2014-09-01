#ifndef x86Disassembler_HEADER
#define x86Disassembler_HEADER

#include "disassembler.h"
#include "graph/quesoGraph.h"
#include "machine/machine.h"
#include "translators/x86queso.h"

class X86Disassembler : public Disassembler {
    private :
        static std::list <uint64_t> evalEip (InstructionX86 * ix86);

    public :
        static QuesoGraph * disassemble (uint64_t entry,
               			                 const MemoryModel * memoryModel);
};

#endif