#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int64_t test(int8_t y)
{
    return y;
}

int main(int argc, char **argv)
{
    uint64_t res = test(strtoull(argv[1], NULL, 10));
    printf("%" PRIu64 "\n", res);
    return 0;
}
