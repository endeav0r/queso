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

        // disassembles to an acyclic graph for graph exploration
        static QuesoGraph * treeDepth (uint64_t entry,
                                       const MemoryModel * memoryModel,
                                       uint64_t depth);

        // disassembles to an acyclic graph for graph exploration
        static QuesoGraph * acyclicDepth (uint64_t entry,
                                          const MemoryModel * memoryModel,
                                          uint64_t depth);
};

#endif