#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

struct point {
    uint64_t x;
    uint64_t y;
};

uint64_t sqrtlen(struct point *pt)
{
    return pt->x * pt->x + pt->y * pt->y;
}

uint8_t test(uint64_t x, uint64_t y)
{
    struct point pt;
    pt.x = x;
    pt.y = y;
    return sqrtlen(&pt);
}

int main(int argc, char **argv)
{
    uint64_t res = test(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10));
    printf("%" PRIu64 "\n", res);
    return 0;
}
