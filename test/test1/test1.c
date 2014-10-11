#include <stdio.h>

int main (int argc, char * argv[]) {
    char * test = "aha";
    int i;
    for (i = 0; test[i] != '\0'; i++) {
        if (argv[1][i] != test[i])
            return -1;
    }
    printf("win!\n");
    return 0;
}