#ifndef elf32_HEADER
#define elf32_HEADER

#include "elf.h"

#include "loader.h"

class Elf32Section {
    private :
        std::string name;
        uint32_t address;
        uint32_t size;
    public :
        Elf32Section (std::string name, uint32_t address, uint32_t size)
            : name (name), address (address), size (size) {}

        std::string & g_name    () { return name; }
        uint32_t      g_address () { return address; }
        uint32_t      g_size    () { return size;}
};

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
            delete[] data;
        }
        static Elf32 * load (const std::string filename);
        uint64_t    entry ();
        std::string label (uint64_t address);
        std::list <LoaderSymbol> symbols ();
        std::list <LoaderSymbol> relocs  ();
        std::list <Elf32Section> sections ();
        MemoryModel memoryModel ();
};

#endif