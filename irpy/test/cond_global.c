#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

uint32_t global = 0;

void test2(uint32_t x, uint32_t y)
{
    if (y > (1 << 31))
        global = x;
    else
        global = y;
}

uint32_t test(uint32_t x, uint32_t y)
{
    test2(x, y);
    return global;
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]), atoi(argv[2]));
    printf("%u\n", res);
    return 0;
}
