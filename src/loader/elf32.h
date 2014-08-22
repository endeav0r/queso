#ifndef elf32_HEADER
#define elf32_HEADER

#include "loader.h"

#include <elf.h>

class Elf32 : public Loader {
    private :
        unsigned char * data;
        size_t size;

        const Elf32_Ehdr * _ehdr     ();
        const Elf32_Phdr * _phdr     (unsigned int index);
        const Elf32_Shdr * _shdr     (unsigned int index);
        const void *       _shdr_ent (const Elf32_Shdr * shdr, unsigned int index);

    public :
        ~Elf32 () {
            delete data;
        }
        static Elf32 * load (const std::string filename);
        uint64_t    entry ();
        std::string label (uint64_t address);
        std::list <LoaderSymbol> symbols ();
        MemoryModel memoryModel ();
};

#endif