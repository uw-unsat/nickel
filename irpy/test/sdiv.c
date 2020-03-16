#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int32_t test(int32_t x, int32_t y)
{
    if (y != 0)
        return x / y;
    return 0;
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]), atoi(argv[2]));
    printf("%u\n", res);
    return 0;
}
