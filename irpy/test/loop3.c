#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int test(uint64_t y)
{
    for (int i = 0; i < 10; i++) {
        if (i % 2) {
            y = y * 2 + 1;
        } else {
            y = y - 12;
        }
    }
    return y;
}

int main(int argc, char **argv)
{
    int res = test(strtoull(argv[1], NULL, 10));
    printf("%u\n", res);
    return 0;
}
