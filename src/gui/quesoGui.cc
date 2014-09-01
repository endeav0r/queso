#include "gui.h"

#include "disassembler/x86Disassembler.h"
#include "loader/elf32.h"

#include <iostream>
#include <unistd.h>

int main (int argc, char * argv[]) {
    Gui gui;

    gui.draw();

    Elf32 * elf32 = Elf32::load("../test/test0");

    MemoryModel memoryModel = elf32->memoryModel();

    QuesoGraph * quesoGraph = X86Disassembler::disassemble(elf32->entry(), &memoryModel);

    std::cout << quesoGraph->dotGraph() << std::endl;

    delete elf32;
    delete quesoGraph;

    return 0;
}