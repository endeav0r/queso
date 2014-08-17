#include "graph.h"

/**********************************************************
* GraphVertex
**********************************************************/

GraphVertex :: ~GraphVertex () {
    std::list <GraphEdge *> :: iterator it;
    for (it = edges.begin(); it != edges.end(); it++) {
        GraphEdge * graphEdge = *it;
        it = edges.erase(it);

        delete graphEdge;
    }
}


void GraphVertex :: deleteEdge (GraphEdge * edge) {
    std::list <GraphEdge *> :: iterator it;
    for (it = edges.begin(); it != edges.end(); it++) {
        if (*it == edge) {
            GraphEdge * graphEdge = *it;
            it = edges.erase(it);

            delete graphEdge;

            break;
        }
    }
}


const std::list <GraphEdge *> GraphVertex :: g_successors () const {
    std::list <GraphEdge *> successors;
    std::list <GraphEdge *> :: const_iterator it;
    for (it = edges.begin(); it != edges.end(); it++) {
        GraphEdge * edge = *it;
        if (edge->g_head() == this)
            successors.push_back(edge);
    }
    return successors;
}


const std::list <GraphEdge *> GraphVertex :: g_predecessors () const {
    std::list <GraphEdge *> predecessors;
    std::list <GraphEdge *> :: const_iterator it;
    for (it = edges.begin(); it != edges.end(); it++) {
        GraphEdge * edge = *it;
        if (edge->g_tail() == this)
            predecessors.push_back(edge);
    }
    return predecessors;
}



/**********************************************************
* Graph
**********************************************************/

Graph :: ~Graph () {
    std::map<const GraphVertex *, GraphVertex *> :: iterator it;
    for (it = vertices.begin(); it != vertices.end(); it++) {
        GraphVertex * graphVertex = it->second;
        it = vertices.erase(it);
        delete graphVertex;
    }
}


const GraphVertex * Graph :: absorbVertex (GraphVertex * graphVertex) {
    vertices[graphVertex] = graphVertex;
    return graphVertex;
}


const GraphEdge * Graph :: absorbEdge (GraphEdge * graphEdge) {
    vertices[graphEdge->g_head()]->insertEdge(graphEdge);
    vertices[graphEdge->g_tail()]->insertEdge(graphEdge);

    return graphEdge;
}