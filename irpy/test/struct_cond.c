#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

struct point {
    uint64_t x;
    uint64_t y;
};

struct point arr[5];

_Bool is_valid(uint64_t x)
{
    return (x < 5);
}

uint8_t test(uint64_t x, uint64_t y)
{
    if (!is_valid(x))
        return -1;
    struct point *p = &arr[x];
    if (p->x < 1 << 31)
        return p->y;
    p->y = 54;
    return p->y;
}

int main(int argc, char **argv)
{
    uint64_t res = test(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10));
    printf("%" PRIu64 "\n", res);
    return 0;
}
