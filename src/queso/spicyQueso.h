#ifndef spicyQueso_HEADER
#define spicyQueso_HEADER

#include "queso.h"
#include "graph/quesoGraph.h"
#include <inttypes.h>
#include <list>
#include <map>
#include <set>


class SpicyQueso {
    public :
        static void ssa (std::list <Instruction *> & instructions);
        static void ssa (QuesoGraph * quesoGraph);

        static void ssa2 (QuesoGraph * quesoGraph);

        static void blockize   (QuesoGraph * quesoGraph);
        static void unblockize (QuesoGraph * quesoGraph);

        static void dead_code_elimination (QuesoGraph * quesoGraph);
        static void constant_fold_propagate (QuesoGraph * quesoGraph);

        static void replace_operand (QuesoGraph * quesoGraph,
                                     const Operand * needle,
                                     const Operand * newOperand);

        // returns a map of dominators for every vertex in the graph
        static std::map <uint64_t, std::set <uint64_t>> dominator_map (QuesoGraph * quesoGraph);

        // returns a map of predecessors for every vertex in the graph
        static std::map <uint64_t, std::set <uint64_t>> predecessor_map (QuesoGraph * quesoGraph);
};

#endif