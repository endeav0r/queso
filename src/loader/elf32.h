#ifndef elf32_HEADER
#define elf32_HEADER

#include "loader.h"

class Elf32 : public Loader {
    private :
        unsigned char * data;
        size_t size;
        MemoryModel memoryModel;
    public :
        static Elf32 * load (const std::string filename);
        std::string label (uint64_t address);
        const MemoryModel & g_memoryModel ();
};

#endif