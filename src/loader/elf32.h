#ifndef elf32_HEADER
#define elf32_HEADER

#include "loader.h"

#include <elf.h>

class Elf32 : public Loader {
    private :
        unsigned char * data;
        size_t size;

        const Elf32_Ehdr * ehdr ();
        const Elf32_Phdr * phdr (unsigned int index);

    public :
        static Elf32 * load (const std::string filename);
        uint64_t    entry ();
        std::string label (uint64_t address);
        MemoryModel memoryModel ();
};

#endif