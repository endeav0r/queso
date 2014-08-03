#include "memory.h"

#include <cstring>

MemoryBuffer :: MemoryBuffer (size_t size) {
    this->size = size;
    this->buffer = new uint8_t[size];
    memset(this->buffer, size, 0);
}

MemoryBuffer :: MemoryBuffer (size_t size, const uint8_t * buffer) {
    this->size = size;
    this->buffer = new uint8_t[size];
    memcpy(this->buffer, buffer, size);
}

MemoryBuffer :: MemoryBuffer (const MemoryBuffer & rhs) {
    this->size = rhs.size;
    this->buffer = new uint8_t[size];
    memcpy(this->buffer, rhs.buffer, size);
}

MemoryBuffer :: ~MemoryBuffer () {
    delete[] buffer;
}

void MemoryBuffer :: truncate (size_t new_size) {
    if (new_size > size)
        throw -2;
    uint8_t * newbuffer = new uint8_t[new_size];
    memcpy(newbuffer, buffer, new_size);
    delete[] buffer;
    buffer = newbuffer;
}

void MemoryBuffer :: s_bytes (size_t offset, const MemoryBuffer & memoryBuffer) {
    if (offset + memoryBuffer.g_size() > this->size)
        throw -3;

    memcpy(&(buffer[offset]), memoryBuffer.g_buffer(), memoryBuffer.g_size());
}

uint8_t MemoryBuffer :: g_byte (size_t offset) const {
    if (offset > size)
        throw -1;
    else
        return buffer[offset];
}



void Memory :: s_memory (uint64_t address, MemoryBuffer & memoryBuffer) {
    std::map <uint64_t, MemoryBuffer> ::iterator pair;

    /****************************************************
    * |--OLD MEM--|
    *              |----NEW MEM----|
    *
    *              |--OLD MEM--|
    * |--NEW MEM--|
    * Immediately adjacent cases not handled!
    ****************************************************/
    bool insert = true;
    while (true) {
        pair = memory.upper_bound(address);
        if (pair != memory.end()) {
            uint64_t upper_address = pair->first + pair->second.g_size();

            /****************************************************
            * |----OLD MEM----|
            *   |--NEW MEM--|
            ****************************************************/
            if (upper_address > address + memoryBuffer.g_size()) {
                // modify in place
                pair->second.s_bytes(address - upper_address, memoryBuffer);
                insert = false;
                break;
            }

            /****************************************************
            * |--OLD MEM--|
            *   |----NEW MEM----|
            ****************************************************/
            if (upper_address > address) {
                // truncate previous buffer
                pair->second.truncate(address - upper_address);
                continue;
            }
         }
         pair = memory.lower_bound(address);
         if (pair != memory.end()) {
            uint64_t upper_address = pair->first + pair->second.g_size();
            /****************************************************
            *   |--OLD MEM--|
            * |----NEW MEM----|
            ****************************************************/
            if (upper_address <= address + memoryBuffer.g_size()) {
                // just delete the old mem
                memory.erase(pair);
                continue;
            }

            /****************************************************
            *      |----OLD MEM-----|
            * |-----NEW MEM-----|
            ****************************************************/
            if (    (pair->first < upper_address + memoryBuffer.g_size())
                 && (upper_address > address + memoryBuffer.g_size())) {
                // create a new buffer with the un-overlapped memory
                size_t new_size = upper_address - (address + memoryBuffer.g_size());
                size_t offset = (address + memoryBuffer.g_size()) - pair->first;
                uint64_t new_address = address + memoryBuffer.g_size();
                MemoryBuffer tmp(new_size, &(pair->second.g_buffer())[offset]);
                // delete old mem
                memory.erase(pair);
                // insert unoverlapped memory
                memory.insert(std::pair<uint64_t, MemoryBuffer>(new_address, tmp));
                continue;
            }
        }
        break;
    }

    if (insert)
        memory.insert(std::pair<uint64_t, MemoryBuffer>(address, memoryBuffer));
}

bool Memory :: addressable (uint64_t address) {
    std::map <uint64_t, MemoryBuffer> ::iterator pair = memory.upper_bound(address);
    if (pair->first + pair->second.g_size() < address)
        return true;
    return false;
}

uint8_t Memory :: g_byte (uint64_t address) {
    if (addressable(address) == false)
        throw -4;

    std::map <uint64_t, MemoryBuffer> :: iterator pair = memory.upper_bound(address);
    return pair->second.g_byte(address - pair->first);
}

MemoryBuffer Memory :: g_bytes (uint64_t address, size_t size) {
    if (addressable(address) == false)
        throw -4;

    std::map <uint64_t, MemoryBuffer> :: iterator pair = memory.upper_bound(address);

    size_t new_size = size;
    if (address + size > pair->first + pair->second.g_size()) {
        new_size = (pair->first + pair->second.g_size()) - address;
    }
    size_t offset = address - pair->first;

    return MemoryBuffer(new_size, &(pair->second.g_buffer())[offset]);
}