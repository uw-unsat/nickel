#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t test2(uint64_t *x)
{
        *(char*)x = 0;
        return  *x;
}

uint64_t test(uint64_t x)
{
        return test2(&x);
}

int main(int argc, char **argv)
{
    uint64_t res = test(strtoull(argv[1], NULL, 10));
    printf("%" PRIu64 "\n", res);
    return 0;
}
