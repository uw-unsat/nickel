#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint8_t test2(uint64_t *x)
{
        return *(char*)x;
}

uint8_t test(uint64_t x)
{
        return test2(&x);
}

int main(int argc, char **argv)
{
    uint8_t res = test(strtoull(argv[1], NULL, 10));
    printf("%d\n", res);
    return 0;
}
