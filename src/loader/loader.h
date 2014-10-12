#ifndef loader_HEADER
#define loader_HEADER

#include "containers/memoryModel.h"

#include <inttypes.h>
#include <list>
#include <string>

enum LoaderSymbolType {
    LST_FUNCTION,
    LST_RELOC
};

class LoaderSymbol {
    private :
        std::string symbol;
        uint64_t address;
        LoaderSymbolType type;
    public :
        LoaderSymbol (const std::string & symbol, uint64_t address, LoaderSymbolType type)
            : symbol (symbol), address (address), type (type) {}

        const std::string & g_symbol  () { return symbol; }
        uint64_t            g_address () { return address; }
        LoaderSymbolType    g_type    () { return type; }
};


class Loader {
    public :
    	virtual ~Loader () {}
        static  Loader *    load  (const std::string filename);
        virtual uint64_t    entry () = 0;
        virtual std::string label (uint64_t address) = 0;
        virtual std::list <LoaderSymbol> symbols () = 0;
        virtual MemoryModel memoryModel () = 0;
};

#endif