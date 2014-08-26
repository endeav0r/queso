#include "gui.h"

#include <stdexcept>

Gui :: Gui () {
    if (SDL_Init(SDL_INIT_EVERYTHING) != 0)
        throw std::runtime_error(std::string("sdl init failed: ") + SDL_GetError());

    window = SDL_CreateWindow("queso", 100, 100, 800, 600, SDL_WINDOW_SHOWN);
    if (window == NULL)
        throw std::runtime_error("failed to create window");


}


Gui :: ~Gui () {
    std::list <Widget *> :: iterator it;
    for (it = widgets.begin(); it != widgets.end(); it++) {
        delete *it;
    }

    SDL_DestroyWindow (window);
    SDL_Quit();
}


void Gui :: draw () {
    SDL_Surface * windowSurface = SDL_GetWindowSurface(window);

    std::list <Widget *> :: iterator it;
    for (it = widgets.begin(); it != widgets.end(); it++) {
        (*it)->draw(windowSurface);
    }
}


void Gui :: addWidget (Widget * widget) {
    this->widgets.push_back(widget);
}