#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

uint8_t test(uint64_t y)
{
    return y;
}

int main(int argc, char **argv)
{
    int res = test(strtoull(argv[1], NULL, 10));
    printf("%u\n", res);
    return 0;
}
