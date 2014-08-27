#ifndef graph_HEADER
#define graph_HEADER

#include <cstdio>
#include <cstdlib>
#include <inttypes.h>
#include <list>
#include <map>

class GraphEdge;
class GraphVertex;


class Graph {
    protected :
        std::map <uint64_t, GraphVertex *> vertices;
        uint64_t _nextVIndex;
    public :
        Graph () {
            _nextVIndex = 0;
        }

        ~Graph ();
        const GraphVertex * absorbVertex (GraphVertex * graphVertex);
        const GraphEdge *   absorbEdge   (GraphEdge * graphEdge);

        uint64_t nextVIndex () { return _nextVIndex++; }

        GraphVertex * g_vertex (uint64_t vIndex) {
            if (vertices.count(vIndex) > 0)
                return vertices[vIndex];
            return NULL;
        }
        std::map <uint64_t, GraphVertex *> & g_vertices () {
            return vertices;
        }
};


class GraphVertex {
    private :
        std::list <GraphEdge *> edges;
        uint64_t vIndex;
        Graph * graph;
    public :
        GraphVertex () {
            graph = NULL;
            vIndex = -1;
        }
        virtual ~GraphVertex ();

        void setGraph (Graph * graph) {
            this->graph = graph;
            this->vIndex = graph->nextVIndex();
        }

        uint64_t g_vIndex () { return vIndex; }

        void removeEdge (GraphEdge * edge);
        void insertEdge (GraphEdge * edge);

        const std::list <GraphEdge *> & g_edges () const { return edges; }
        const std::list <GraphEdge *>   g_successors () const;
        const std::list <GraphEdge *>   g_predecessors () const;
};


class GraphEdge {
    protected :
        Graph * graph;
        uint64_t head;
        uint64_t tail;
    public :
        GraphEdge (Graph * graph, uint64_t head, uint64_t tail)
            : graph (graph), head (head), tail (tail) {}
        GraphEdge () : graph (NULL), head (-1), tail (-1) {}

        virtual ~GraphEdge () {
            if (graph != NULL) {
                graph->g_vertex(head)->removeEdge(this);
                graph->g_vertex(tail)->removeEdge(this);
            }
        }

        virtual GraphVertex * g_head () { return graph->g_vertex(head); }
        virtual GraphVertex * g_tail () { return graph->g_vertex(tail); }
};

#endif