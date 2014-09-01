#ifndef spicyQueso_HEADER
#define spicyQueso_HEADER

#include "queso.h"
#include <list>


class SpicyQueso {
    public :
        static void ssa (std::list <Instruction *> & instructions);
};

#endif