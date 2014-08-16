#include "quesoGraph.h"

#include <queue>
#include <sstream>
#include <unordered_set>

const QuesoVertex * QuesoCfg :: absorbQuesoVertex (QuesoVertex * quesoVertex) {
    return dynamic_cast<const QuesoVertex *>(cfg.absorbVertex(quesoVertex));
}


const QuesoEdge * QuesoCfg :: absorbQuesoEdge (QuesoEdge * quesoEdge) {
    return dynamic_cast<const QuesoEdge *>(cfg.absorbEdge(quesoEdge));
}


std::string quesoVertexDotName (const QuesoVertex * quesoVertex) {
    char tmp[64];
    snprintf(tmp, 64, "%p", quesoVertex);
    return tmp;
}


std::string dotGraph (const QuesoVertex * quesoVertex) {
    std::stringstream ss;
    
    std::unordered_set <const QuesoVertex *> queuedOrDrawn;
    std::queue <const QuesoVertex *> drawQueue;

    queuedOrDrawn.insert(quesoVertex);
    drawQueue.push(quesoVertex);

    ss << "digraph G {" << std::endl;

    while (drawQueue.size() > 0) {
        const QuesoVertex * quesoVertex = drawQueue.front();
        drawQueue.pop();

        // draw this vertex
        ss << quesoVertexDotName(quesoVertex) << " [label=\""
           << quesoVertex->queso() << "\"];" << std::endl;

        // for all edges
        std::list <GraphEdge *> :: const_iterator it;
        for (it = quesoVertex->g_edges().begin();
             it != quesoVertex->g_edges().end();
             it++) {
            const QuesoEdge * quesoEdge = dynamic_cast<const QuesoEdge *>(*it);
            const QuesoVertex * head = dynamic_cast<const QuesoVertex *>(quesoEdge->g_head());
            const QuesoVertex * tail = dynamic_cast<const QuesoVertex *>(quesoEdge->g_tail());

            // add unqueued vertices to queue
            if (queuedOrDrawn.count(head) == 0) {
                queuedOrDrawn.insert(head);
                drawQueue.push(head);
            }
            if (queuedOrDrawn.count(tail) == 0) {
                queuedOrDrawn.insert(tail);
                drawQueue.push(tail);
            }

            // we draw successor edges
            if (head == quesoVertex) {
                ss << quesoVertexDotName(head) << " -> " << quesoVertexDotName(tail)
                   << ";" << std::endl;
            }
        }
    }

    ss << "}";
    return ss.str();
}