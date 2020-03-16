#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t test2(uint64_t *x)
{
        *((char*)x + 8) = 0;
        return  *x;
}

uint64_t test(uint64_t x)
{
        uint64_t arr[10];
        for(int i = 0; i < 10; i++)
                arr[i] = x;
        return test2(arr);
}

int main(int argc, char **argv)
{
    uint64_t res = test(strtoull(argv[1], NULL, 10));
    printf("%" PRIu64 "\n", res);
    return 0;
}
