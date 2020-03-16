#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int test(uint64_t i)
{
    uint64_t y = 0;
    if (i < 10) {
        for (; i < 11; i++) {
            if (i % 2) {
                y = y * 2 + 1;
            } else {
                y = y - 12;
            }
        }
    }
    return y;
}

int main(int argc, char **argv)
{
    int res = test(strtoull(argv[1], NULL, 10));
    printf("%u\n", res);
    return 0;
}
