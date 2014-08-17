#ifndef loader_HEADER
#define loader_HEADER

#include "containers/memoryModel.h"

#include <inttypes.h>
#include <string>

class Loader {
    public :
    	virtual ~Loader () {}
        static  Loader *    load  (const std::string filename);
        virtual uint64_t    entry () = 0;
        virtual std::string label (uint64_t address) = 0;
        virtual MemoryModel memoryModel () = 0;
};

#endif