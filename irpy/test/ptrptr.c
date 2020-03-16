#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

void bla(uint32_t x, uint32_t **a, uint32_t *b, uint32_t *c)
{
    if (x > 1 << 31)
        *a = b;
    else
        *a = c;
}

uint32_t test(uint32_t x, uint32_t y, uint32_t z)
{
    uint32_t *a = NULL;
    uint32_t *b = &y;
    uint32_t *c = &z;
    bla(x, &a, b, c);
    return *a;
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
    printf("%u\n", res);
    return 0;
}
