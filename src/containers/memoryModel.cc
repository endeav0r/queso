#include "memoryModel.h"

MemoryBuffer MemoryModel :: g_bytes (uint64_t address, size_t size) const {
    unsigned char * data = new unsigned char [size];

    for (size_t i = 0; i < size; i++) {
        data[i] = memory.at(address + i);
    }

    return MemoryBuffer(data, size);
}