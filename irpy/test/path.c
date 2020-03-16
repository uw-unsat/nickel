#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int test(uint64_t x, uint64_t y)
{
    uint64_t z = 123;
    if (y < 10 && x < y) {
        for (; x < y; x++) {
            z += x * y + z;
        }
    }

    return z;
}

int main(int argc, char **argv)
{
    int res = test(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10));
    printf("%u\n", res);
    return 0;
}
