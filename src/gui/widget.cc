#include "widget.h"

#include <stdexcept>


TTF_Font * staticTTF_Font = NULL;
SDL_Window * _window = NULL;

void widgetInit (SDL_Window * window) {
    _window = window;
    WidgetFont::getTTF_Font();
}

TTF_Font * WidgetFont :: getTTF_Font () {
    if (staticTTF_Font == NULL)
        staticTTF_Font = TTF_OpenFont("ProggyClean.ttf", 11);
    if (staticTTF_Font == NULL)
        throw std::runtime_error("error loading font");
    return staticTTF_Font;
}


Widget :: Widget () {
    this->x = 0;
    this->y = 0;
    this->width = 0;
    this->height = 0;
    this->padding = 2;

    setTextColor(0xff, 0xff, 0xff, 0);
    setBackgroundColor(0x0, 0x0, 0x0, 0x40);
    setBorderColor(0x80, 0x80, 0x80, 0);

    this->_clicked = false;
}


void Widget :: setColor (SDL_Color * sdl_color,
                         uint32_t * mappedColor,
                         uint8_t r,
                         uint8_t g,
                         uint8_t b,
                         uint8_t a) {
    sdl_color->r = r;
    sdl_color->g = g;
    sdl_color->b = b;
    sdl_color->a = a;

    SDL_Surface * windowSurface = SDL_GetWindowSurface(_window);
    *mappedColor = SDL_MapRGBA(windowSurface->format, r, g, b, a);
}


void Widget :: setTextColor (uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    setColor(&textColor, &textColorMapped, r, g, b, a);
}


void Widget :: setBackgroundColor (uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    setColor(&backgroundColor, &backgroundColorMapped, r, g, b, a);
}


void Widget :: setBorderColor (uint8_t r, uint8_t g, uint8_t b, uint8_t a) {
    setColor(&borderColor, &borderColorMapped, r, g, b, a);
}


void Widget :: drawOutline (SDL_Surface * surface) {
    SDL_Rect rect;

    rect.x = x;
    rect.x = y;
    rect.w = width;
    rect.h = height;

    SDL_FillRect(surface, &rect, borderColorMapped);

    rect.x += 1;
    rect.y += 1;
    rect.w -= 2;
    rect.h -= 2;

    SDL_FillRect(surface, &rect, backgroundColorMapped);
}


bool Widget :: click (int x, int y) {
    if (    (x >= this->x)
         && (x <= this->x + this->width)
         && (y >= this->y)
         && (y <= this->y + this->height)) {
        this->_clicked = true;
    }
    else
        this->_clicked = false;
    return this->_clicked;
}

