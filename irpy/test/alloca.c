#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

void foo(uint32_t *x, uint32_t y)
{
    *x += y;
}

uint32_t test(uint32_t x)
{
    uint32_t y = 0;
    foo(&y, x);
    if (y > x) {
        y++;
    } else {
        y--;
    }
    return y;
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]));
    printf("%u\n", res);
    return 0;
}
