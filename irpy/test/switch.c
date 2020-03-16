#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int test(uint32_t x)
{
    int32_t y;

    switch (x) {
    case 1:
    case 2:
        y = 10;
        break;
    case 10:
        y = 703;
        break;
    default:
        y = -1;
        break;
    }

    if (y > 5)
        return y + x;
    return y - x;
}

int main(int argc, char **argv)
{
    int res = test(strtoull(argv[1], NULL, 10));
    printf("%u\n", res);
    return 0;
}
