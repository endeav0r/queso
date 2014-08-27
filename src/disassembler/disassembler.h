#ifndef disassembler_HEADER
#define disassembler_HEADER

#include "graph/quesoGraph.h"
#include "containers/memoryModel.h"

class Disassembler {
    public :
        virtual QuesoGraph * disassemble (uint64_t entry,
                                          const MemoryModel & memoryModel) = 0;
};

#endif