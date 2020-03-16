#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

uint32_t global[10];

void global_init()
{
    for (int i = 0; i < 10; ++i) {
        global[i] = i;
    }
}

uint32_t test(uint32_t x)
{
    global_init();
    return global[x % 10];
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]));
    printf("%u\n", res);
    return 0;
}
