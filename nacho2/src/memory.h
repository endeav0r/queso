#ifndef memory_HEADER
#define memory_HEADER

#include <cstdlib>
#include <inttypes.h>
#include <map>

class MemoryBuffer {
    private :
        uint8_t * buffer;
        size_t size;
    public :
        MemoryBuffer (size_t size);
        MemoryBuffer (size_t size, const uint8_t * buffer);
        MemoryBuffer (const MemoryBuffer & rhs);
        ~MemoryBuffer ();

        void truncate (size_t new_size);
        void s_bytes  (size_t offset, const MemoryBuffer & memoryBuffer);

        size_t          g_size   () const { return size; } ;
        uint8_t         g_byte   (size_t offset) const;
        const uint8_t * g_buffer () const { return buffer; }
};

class Memory {
    private :
        std::map <uint64_t, MemoryBuffer> memory;
    public :
        
        void s_memory (uint64_t address, MemoryBuffer & memoryBuffer);
        bool addressable (uint64_t address);
        uint8_t g_byte (uint64_t address);

        MemoryBuffer g_bytes (uint64_t address, size_t size);
};

#endif