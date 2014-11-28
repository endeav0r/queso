#include "graph.h"

#include <cstdio>
#include <iostream>

/**********************************************************
* GraphVertex
**********************************************************/

GraphVertex :: ~GraphVertex () {
    while (edges.size() > 0) {
        delete edges.front();
    }
}


void GraphVertex :: removeEdge (GraphEdge * edge) {
    std::list <GraphEdge *> :: iterator it;
    for (it = edges.begin(); it != edges.end(); it++) {
        if (*it == edge) {
            it = edges.erase(it);

            break;
        }
    }
}


void GraphVertex :: insertEdge (GraphEdge * edge) {
    this->edges.push_back(edge);
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
    std::map<uint64_t, GraphVertex *> :: iterator it;
    for (it = vertices.begin(); it != vertices.end(); it++) {
        GraphVertex * graphVertex = it->second;
        delete graphVertex;
    }
}


void Graph :: removeVertex (uint64_t vIndex) {
    if (vertices.count(vIndex) > 0) {
        while (vertices[vIndex]->g_edges().size() > 0)
            delete vertices[vIndex]->g_edges().front();
        vertices.erase(vIndex);
    }
    else
        printf("Graph :: removeVertex %llx not found\n", vIndex);
}


const GraphVertex * Graph :: absorbVertex (GraphVertex * graphVertex) {
    graphVertex->setGraph(this);
    vertices[graphVertex->g_vIndex()] = graphVertex;
    return graphVertex;
}


const GraphVertex * Graph :: absorbVertex (GraphVertex * graphVertex, uint64_t vIndex) {
    graphVertex->setGraph(this, vIndex);
    vertices[graphVertex->g_vIndex()] = graphVertex;
    return graphVertex;
}


const GraphEdge * Graph :: absorbEdge (GraphEdge * graphEdge) {
    graphEdge->g_head()->insertEdge(graphEdge);
    graphEdge->g_tail()->insertEdge(graphEdge);

    return graphEdge;
}