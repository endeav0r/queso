#ifndef guiGraph_HEADER
#define guiGraph_HEADER

#include "widget.h"
#include "graph/quesoGraph.h"
#include "queso/queso.h"

#include <map>

class GuiVertex {

};

class GuiEdge : public QuesoEdge {

};

class GuiGraph : public Widget {
    private :
        QuesoGraph * quesoGraph;
    public :
        GuiGraph (QuesoGraph * quesoGraph);
};


#endif