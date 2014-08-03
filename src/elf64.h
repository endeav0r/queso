#ifndef elf64_HEADER
#define elf64_HEADER

#include <elf.h>

class Elf64Phdr {
    private :
        Elf64_Phdr phdr;
    public :
        Elf64Phdr (const Elf64 & elf64, uint64_t offset);

        uint64_t p_type   () { return phdr.p_type; }
        uint64_t p_flags  () { return phdr.p_flags; }
        uint64_t p_offset () { return phdr.p_offset; }
        uint64_t p_vaddr  () { return phdr.p_vaddr; }
        uint64_t p_paddr  () { return phdr.p_paddr; }
        uint64_t p_filesz () { return phdr.p_filesz; }
        uint64_t p_memsz  () { return phdr.p_memsz; }
        uint64_t p_align  () { return phdr.p_align; }
};

class Elf64 {
    private :
        Elf64_Ehdr * ehdr;
        uint8_t * bytes;
    public :
        Elf64 (const std::string filename);

        std::list <Elf64Phdr> phdrs ();
};


#endif