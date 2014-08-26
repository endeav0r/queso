#ifndef widget_HEADER
#define widget_HEADER

#include <SDL.h>
#include <SDL_ttf.h>

void widgetInit (SDL_Window * window);

class WidgetFont {
    private :
        TTF_Font * font;
    public :
        static TTF_Font * getTTF_Font ();
};

class Widget {
    protected :
        int x, y, height, width;
        int padding;
        SDL_Color textColor;
        SDL_Color backgroundColor;
        SDL_Color borderColor;

        uint32_t textColorMapped;
        uint32_t backgroundColorMapped;
        uint32_t borderColorMapped;

        void setColor (SDL_Color * sdl_color,
                       uint32_t * mappedColor,
                       uint8_t r,
                       uint8_t g,
                       uint8_t b,
                       uint8_t a);
        void setTextColor       (uint8_t r, uint8_t g, uint8_t b, uint8_t a);
        void setBackgroundColor (uint8_t r, uint8_t g, uint8_t b, uint8_t a);
        void setBorderColor     (uint8_t r, uint8_t g, uint8_t b, uint8_t a);

        bool     _clicked;

    public :
        Widget ();
        virtual ~Widget () {}

        virtual void draw        (SDL_Surface * surface) = 0;
        virtual void drawOutline (SDL_Surface * surface);
        virtual bool click       (int x, int y);
        virtual bool clicked     () { return this->_clicked; }

        void s_x (int x) { this->x = x; }
        void s_y (int y) { this->y = y; }
        void s_height (int height) { this->height = height; }
        void s_width  (int width)  { this->width = width; }

        int g_x () { return x; }
        int g_y () { return y; }
        int g_height () { return height; }
        int g_width  () { return width; }
};


#endif