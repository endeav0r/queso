#ifndef gui_HEADER
#define gui_HEADER

#include <SDL.h>

#include <list>

#include "widget.h"

class Gui {
    private :
        std::list <Widget *> widgets;
        SDL_Window * window;
    public :
        Gui ();
        ~Gui ();

        void draw ();

        void addWidget (Widget * widget);
};

#endif