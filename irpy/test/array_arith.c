#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

uint32_t arr[] = {1, 2, 3, 4};

uint32_t test(uint32_t x)
{
    uint32_t idx = x % 4;
    uint32_t *bla = (uint32_t *)&arr;
    return *(bla + idx);
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]));
    printf("%u\n", res);
    return 0;
}
