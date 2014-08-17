#ifndef graph_HEADER
#define graph_HEADER

#include <cstdlib>
#include <list>
#include <map>

class GraphEdge;

class GraphVertex {
    private :
        std::list <GraphEdge *> edges;
    public :
        virtual ~GraphVertex ();

        void deleteEdge (GraphEdge * edge);
        void insertEdge (GraphEdge * edge);

        const std::list <GraphEdge *> & g_edges () const { return edges; }
        const std::list <GraphEdge *>   g_successors () const;
        const std::list <GraphEdge *>   g_predecessors () const;
};


class GraphEdge {
    protected :
        GraphVertex * head;
        GraphVertex * tail;
    public :
        GraphEdge (GraphVertex * head, GraphVertex * tail)
            : head (head), tail (tail) {}
        GraphEdge () : head (NULL), tail (NULL) {}

        virtual ~GraphEdge () {
            if (head != NULL)
                head->deleteEdge(this);
            if (tail != NULL)
                tail->deleteEdge(this);
        }

        const GraphVertex * g_head () const { return head; }
        const GraphVertex * g_tail () const { return tail; }
};


class Graph {
    protected :
        std::map <const GraphVertex *, GraphVertex *> vertices;
    public :
        ~Graph ();
        const GraphVertex * absorbVertex (GraphVertex * graphVertex);
        const GraphEdge *   absorbEdge   (GraphEdge * graphEdge);

        const std::map <const GraphVertex *, GraphVertex *> g_vertices () {
            return vertices;
        }
};

#endif