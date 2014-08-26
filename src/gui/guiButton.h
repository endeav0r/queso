#ifndef guiButton_HEADER
#define guiButton_HEADER

#include "widget.h"

#include <string>

class GuiButton : public Widget {
    private :
        std::string text;
        SDL_Surface * textSurface;
    public :
        GuiButton (const std::string & text);

        void draw (SDL_Surface * surface);
};

#endif