#include "gui.h"

#include <unistd.h>

int main (int argc, char * argv[]) {
    Gui gui;

    gui.draw();

    sleep(5);

    return 0;
}