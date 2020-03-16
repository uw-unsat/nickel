#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

void inc(uint32_t *x)
{
    *x += 1;
}

uint32_t test(uint32_t x, uint32_t y)
{
    if (y > 1 << 31) {
        inc(&x);
        x++;
    } else {
        for (int i = 0; i < 5; ++i) {
            inc(&x);
        }
        inc(&y);
        x--;
    }
    x = x + 1;
    inc(&x);
    return x - y;
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]), atoi(argv[2]));
    printf("%u\n", res);
    return 0;
}
