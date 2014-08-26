#include "gui.h"

#include <stdexcept>

#include <iostream>

Gui :: Gui () {
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER | SDL_INIT_EVENTS) != 0) {
        std::string error = "sdl init failed: ";
        error += SDL_GetError();
        std::cerr << error << std::endl;
        throw std::runtime_error(error);
    }

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

    SDL_FillRect(windowSurface, NULL, 0);

    std::list <Widget *> :: iterator it;
    for (it = widgets.begin(); it != widgets.end(); it++) {
        (*it)->draw(windowSurface);
    }

    SDL_UpdateWindowSurface(window);
}


void Gui :: addWidget (Widget * widget) {
    this->widgets.push_back(widget);
}