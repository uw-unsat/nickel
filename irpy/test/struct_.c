#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

struct vec3 {
    uint64_t x;
    uint64_t y;
    uint64_t z;
};

struct vec3 p = {0};

uint64_t test(uint64_t x)
{

    p.x = x;
    p.y = p.x + p.x;
    p.z = p.y - x;
    return p.z;
}

int main(int argc, char **argv)
{
    uint64_t res = test(strtoull(argv[1], NULL, 10));
    printf("%" PRIu64 "\n", res);
    return 0;
}
