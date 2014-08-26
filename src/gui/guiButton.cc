#include "guiButton.h"

GuiButton :: GuiButton (const std::string & text) {
    this->text = text;
    textSurface = TTF_RenderText_Blended(WidgetFont::getTTF_Font(),
                                          text.c_str(),
                                          textColor);
    this->width = textSurface->w + (padding * 2);
    this->height = textSurface->h + (padding * 2);
}


void GuiButton :: draw (SDL_Surface * surface) {
    drawOutline(surface);

    SDL_Rect rect;
    rect.x = x + padding;
    rect.y = y + padding;
    rect.w = textSurface->w;
    rect.h = textSurface->h;

    SDL_BlitSurface(textSurface, NULL, surface, &rect);
}