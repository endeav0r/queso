#include "elf32.h"

#include <cstdio>
#include <elf.h>


const Elf32_Ehdr * Elf32 :: ehdr () {
    return (Elf32_Ehdr *) data;
}


const Elf32_Phdr * Elf32 :: phdr (unsigned int index) {
    return (Elf32_Phdr *) &(data[ehdr()->e_phoff + (ehdr()->e_phentsize * index)]);
}


Elf32 * Elf32 :: load (const std::string filename) {
    FILE * fh = fopen(filename.c_str(), "rb");
    if (fh == NULL)
        return NULL;

    fseek(fh, 0, SEEK_END);
    size_t size = ftell(fh);
    fseek(fh, 0, SEEK_SET);

    if (size < 32) {
        fclose(fh);
        return NULL;
    }

    unsigned char tmp[32];
    fread(tmp, 1, 32, fh);

    if (    (tmp[EI_MAG0] != ELFMAG0)
         || (tmp[EI_MAG1] != ELFMAG1)
         || (tmp[EI_MAG2] != ELFMAG2)
         || (tmp[EI_MAG3] != ELFMAG3)
         || (tmp[EI_CLASS] != ELFCLASS32)) {
        fclose(fh);
        return NULL;
    }

    fseek(fh, 0, SEEK_SET);

    Elf32 * elf32 = new Elf32;
    elf32->data = new unsigned char[size];
    elf32->size = size;

    size_t totalRead = 0;
    while (true) {
        int bytesRead = fread(&(elf32->data[totalRead]), 1, size - totalRead, fh);
        if (bytesRead == EOF)
            break;
        totalRead += bytesRead;
        if (totalRead == size)
            break;
    }

    fclose(fh);

    return elf32;
}


uint64_t Elf32 :: entry () {
    return ehdr()->e_entry;
}


std::string Elf32 :: label (uint64_t address) {
    char tmp[32];
    snprintf(tmp, 32, "%08x", (unsigned int) address);
    return tmp;
}


MemoryModel Elf32 :: memoryModel () {
    MemoryModel memoryModel;

    for (size_t phdr_i = 0; phdr_i < ehdr()->e_phnum; phdr_i++) {
        const Elf32_Phdr * phdr_ = phdr(phdr_i);
        for (size_t i = 0; i < phdr_->p_memsz; i++) {
            if (i < phdr_->p_filesz)
                memoryModel.s_byte(phdr_->p_vaddr + i, data[phdr_->p_offset + i]);
            else
                memoryModel.s_byte(phdr_->p_vaddr + i, 0);
        }
    }

    return memoryModel;
}