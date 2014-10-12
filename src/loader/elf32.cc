#include "elf32.h"

#include <cstdio>
#include <iostream>


const Elf32_Ehdr * Elf32 :: _ehdr () {
    return (Elf32_Ehdr *) data;
}


const Elf32_Phdr * Elf32 :: _phdr (unsigned int index) {
    if (index >= _ehdr()->e_phnum)
        return NULL;
    if ((index + 1) * _ehdr()->e_phentsize + _ehdr()->e_phoff > size)
        return NULL;
    return (Elf32_Phdr *) &(data[_ehdr()->e_phoff + (_ehdr()->e_phentsize * index)]);
}


const Elf32_Shdr * Elf32 :: _shdr (unsigned int index) {
    if (index > _ehdr()->e_shnum)
        return NULL;
    if ((index + 1) * _ehdr()->e_shentsize + _ehdr()->e_shoff > size)
        return NULL;
    return (Elf32_Shdr *) &(data[_ehdr()->e_shoff + (_ehdr()->e_shentsize * index)]);
}


const void * Elf32 :: _shdr_ent (const Elf32_Shdr * shdr, unsigned int index) {
    if ((index + 1) * shdr->sh_entsize > shdr->sh_size)
        return NULL;
    if ((index + 1) * shdr->sh_entsize + shdr->sh_offset > size)
        return NULL;
    return (void *) &(data[shdr->sh_offset + (shdr->sh_entsize * index)]);
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
    size_t tmpBytesRead = fread(tmp, 1, 32, fh);

    if (    (tmpBytesRead != 32)
         || (tmp[EI_MAG0] != ELFMAG0)
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
    return _ehdr()->e_entry;
}


std::string Elf32 :: label (uint64_t address) {
    char tmp[32];
    snprintf(tmp, 32, "%08x", (unsigned int) address);
    return tmp;
}


std::list <LoaderSymbol> Elf32 :: symbols () {
    std::list <LoaderSymbol> symbols;

    for (unsigned int shdr_i = 0; shdr_i < _ehdr()->e_shnum; shdr_i++) {
        const Elf32_Shdr * shdr = _shdr(shdr_i);
        if (shdr == NULL)
            break;

        if (    (shdr->sh_type != SHT_SYMTAB)
             && (shdr->sh_type != SHT_DYNSYM))
            continue;

        const Elf32_Shdr * link = _shdr(shdr->sh_link);

        for (unsigned int sym_i = 0; sym_i < shdr->sh_size / shdr->sh_entsize; sym_i++) {
            const Elf32_Sym * sym = (const Elf32_Sym *) _shdr_ent(shdr, sym_i);
            if (ELF32_ST_TYPE(sym->st_info) == STT_FUNC) {
                LoaderSymbol symbol((const char *) &(data[link->sh_offset + sym->st_name]),
                                    sym->st_value, LST_FUNCTION);
                symbols.push_back(symbol);
            }
        }
    }

    return symbols;
}


std::list <LoaderSymbol> Elf32 :: relocs () {
    std::list <LoaderSymbol> relocs;

    for (unsigned int shdr_i = 0; shdr_i < _ehdr()->e_shnum; shdr_i++) {
        const Elf32_Shdr * shdr = _shdr(shdr_i);
        if (shdr == NULL)
            break;

        if (shdr->sh_type != SHT_REL)
            continue;

        const Elf32_Shdr * link = _shdr(shdr->sh_link);
        if (link == NULL)
            continue;

        const Elf32_Shdr * strtab = _shdr(link->sh_link);
        if (strtab == NULL)
            continue;

        for (unsigned int rel_i = 0; rel_i < shdr->sh_size / shdr->sh_entsize; rel_i++) {
            const Elf32_Rel * rel = (Elf32_Rel *) _shdr_ent(shdr, rel_i);
            if (rel == NULL)
                break;

            const Elf32_Sym * sym = (Elf32_Sym *) _shdr_ent (link, ELF32_R_SYM(rel->r_info));

            relocs.push_back(LoaderSymbol((const char*) &(data[strtab->sh_offset + sym->st_name]),
                                          rel->r_offset, LST_RELOC));
        }
    }

    return relocs;
}


std::list <Elf32Section> Elf32 :: sections () {
    std::list <Elf32Section> sections;

    const Elf32_Shdr * strtab = _shdr(_ehdr()->e_shstrndx);

    for (unsigned int shdr_i = 1; shdr_i < _ehdr()->e_shnum; shdr_i++) {
        const Elf32_Shdr * shdr = _shdr(shdr_i);
        if (shdr == NULL)
            break;

        std::string name = "";
        if ((strtab != NULL) && (strtab->sh_offset + shdr->sh_name < size)) {
            name = (char *) &(data[strtab->sh_offset + shdr->sh_name]);
        }

        sections.push_back(Elf32Section(name, shdr->sh_addr, shdr->sh_size));
    }

    return sections;
}


MemoryModel Elf32 :: memoryModel () {
    MemoryModel memoryModel;

    for (size_t phdr_i = 0; phdr_i < _ehdr()->e_phnum; phdr_i++) {
        const Elf32_Phdr * phdr = _phdr(phdr_i);
        for (size_t i = 0; i < phdr->p_memsz; i++) {
            if (i < phdr->p_filesz)
                memoryModel.s_byte(phdr->p_vaddr + i, data[phdr->p_offset + i]);
            else
                memoryModel.s_byte(phdr->p_vaddr + i, 0);
        }
    }

    return memoryModel;
}
