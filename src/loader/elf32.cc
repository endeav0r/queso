#include "elf32.h"

#include <cstdio>
#include <elf.h>

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
    }

    fclose(fh);

    return elf32;
}