#ifndef spicyQueso_HEADER
#define spicyQueso_HEADER

#include "queso.h"
#include "graph/quesoGraph.h"
#include <list>
#include <inttypes.h>


class SpicyQueso {
    public :
        static void ssa (std::list <Instruction *> & instructions);
        static void ssa (QuesoGraph * quesoGraph, uint64_t entry_vId);
};

#endif