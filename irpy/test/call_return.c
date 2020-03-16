#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

uint64_t fib(uint64_t a, uint64_t b, uint64_t steps)
{
    uint64_t tmp;
    while (steps) {
        tmp = a;
        a = b;
        b = a + tmp;
        steps--;
    }
    return b;
}

uint64_t test(uint64_t a, uint64_t b)
{
    return fib(a, b, 10);
}

int main(int argc, char **argv)
{
    uint64_t res = test(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10));
    printf("%" PRIu64 "\n", res);
    return 0;
}
