int main (int argc, char * argv[]) {
    unsigned char buf[32];

    int i;
    for (i = 0; argv[1][i] != '\0'; i++) {
        unsigned char a = argv[1][i];
        unsigned char b = a;
        unsigned char c = a;
        if (i > 0)
            b = buf[i - 1] + a;
        if (i > 1)
            c = buf[i - 2] ^ b;
        if (a & 1) {
            if (b & 1) {
                c ^= b;
            }
            else
                c ^= a;
        }
        else if (c + b > 0x80)
            if ((b > 0x80) || (a < 0x40))
                b += c ^ a;

        buf[i] = a ^ b ^ c;
    }

    return 1;
}