#ifndef memoryModel_HEADER
#define memoryModel_HEADER

#include <cstring>
#include <inttypes.h>
#include <map>

class MemoryBuffer {
    private :
        const unsigned char * data;
        size_t size;
    public :
        MemoryBuffer (const unsigned char * data, size_t size, bool absorb = true) {
            if (absorb)
                this->data = data;
            else {
                this->data = new unsigned char [size];
                memcpy((void *) this->data, data, size);
            }
            this->size = size;
        }
        ~MemoryBuffer () {
            delete[] this->data;
        }

        const unsigned char * g_data () { return data; }
        size_t g_size () { return size; }
};


class MemoryModel {
    private :
        std::map <uint64_t, unsigned char> memory;
    public :
        void s_byte (uint64_t address, unsigned char byte) {
            memory[address] = byte;
        }

        MemoryBuffer g_bytes (uint64_t address, size_t size) const;

        uint8_t g_byte (uint64_t address) { return memory[address]; }

};

#endif