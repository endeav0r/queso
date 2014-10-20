#include <stdio.h>

char * astrcpy (char * dst, char * src) {
    while (*src != '\0')
        *dst++ = *src++;
}


int main (int argc, char * argv[]) {
    char buf[8];

    printf("%s\n", astrcpy(buf, argv[1]));
    return 1;
}