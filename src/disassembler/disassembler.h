#ifndef disassembler_HEADER
#define disassembler_HEADER

class Diassembler {
    public :
        virtual QuesoCfg disassemble (uint64_t entry,
                                      const MemoryModel & memoryModel);
};

#endif