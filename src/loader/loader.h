#ifndef loader_HEADER
#define loader_HEADER

#include "containers/memoryModel.h"

#include <inttypes.h>
#include <string>

class Loader {
    public :
        static  Loader *    load  (const std::string filename);
        virtual std::string label (uint64_t address) = 0;
        virtual MemoryModel g_memoryModel () = 0;
};

#endif