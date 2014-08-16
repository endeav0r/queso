#include "loader.h"

#include "elf32.h"

Loader * Loader :: load (const std::string filename) {
    Elf32 * elf32 = Elf32::load(filename);
    if (elf32 != NULL)
        return elf32;

    return NULL;
}