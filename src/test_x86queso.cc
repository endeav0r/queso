
#include "x86queso.h"

#include <iostream>

struct _test {
    const char * text;
    const uint8_t data[16];
    size_t data_size;
};

struct _test TESTS [] = {
    {"add eax, 8", {0x83, 0xc0, 0x03}, 3},
    {"add [ebx], 7", {0x83, 0x03, 0x07}, 3},
    {"add [ecx+0x4], 2", {0x83, 0x41, 0x01, 0x02}, 4},
    {NULL, {0}, 0}
};

void print_instructions (int depth, std::list <Instruction *> instructions) {
    std::list <Instruction *> :: iterator it;
    for (it = instructions.begin(); it != instructions.end(); it++) {
        for (int i = 0; i < depth; i++)
            std::cout << " ";
        std::cout << (*it)->queso() << std::endl;
        print_instructions(depth + 2, (*it)->g_depth_instructions());
    }
}

int main () {
    QuesoX86 quesoX86;


    for (int i = 0; TESTS[i].text != NULL; i++) {
        Instruction * ins = quesoX86.translate(TESTS[i].data, TESTS[i].data_size);
        std::cout << ins->queso() << std::endl;
        print_instructions(2, ins->g_depth_instructions());
        std::cout << "--------------------------------------------------" << std::endl;
    }

    return 0;
}