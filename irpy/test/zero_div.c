#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

uint32_t test(uint32_t x, uint32_t y)
{
    return x / y;
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]), atoi(argv[2]));
    printf("%u\n", res);
    return 0;
}
