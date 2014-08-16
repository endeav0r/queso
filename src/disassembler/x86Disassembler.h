#ifndef x86Disassembler_HEADER
#define x86Disassembler_HEADER

#include "disassembler.h"

class X86Disassembler : public Disassembler {
    private :
        QuesoCfg quesoCfg;
    public :
        QuesoCfg disassemble (uint64_t entry,
                              const MemoryModel & memoryModel);
};

#endif