#ifndef graph_HEADER
#define graph_HEADER

class GraphNode;
class GraphEdge;

class GraphEdge {
    private :
        GraphNode * head_node;
        GraphNode * tail_node;
    public :
        GraphEdge (GraphNode * head_node, GraphNode * tail_node)
            : head_node (head_node), tail_node (tail_node);

        GraphNode * head           () { return head; }
        GraphNode * tail           () { return tail; }
        uint64_t    head_identifer () { return head->g_identifier(); }
        uint64_t    tail_identifer () { return tail->g_identifier(); }

        virtual GraphEdge * copy ();
};

class GraphNode {
    private :
        uint64_t identifier;
        std::list <uint64_t, GraphEdge *> edges;
    public :
        GraphNode (uint64_t identifier);
        std::list <GraphEdge *> successor_edges   ();
        std::list <GraphEdge *> predecessor_edges ();
        std::list <GraphNode *> successors   ();
        std::list <GraphNode *> predecessors ();

        inline uint64_t g_identifier();

        virtual GraphNode * copy ();
};

class Graph {
    private :
        std::map <uint64_t, GraphNode *> nodes;
        std::map <uint64_t, GraphEdge *> edges;
    public :
        Graph ();
};

#endif