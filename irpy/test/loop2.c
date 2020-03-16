#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int test(uint64_t x, uint64_t y)
{
    for (int i = 0; i < 5; i++) {
        y *= x;
        if (y > 1337)
            break;
    }
    return y;
}

int main(int argc, char **argv)
{
    int res = test(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10));
    printf("%u\n", res);
    return 0;
}
