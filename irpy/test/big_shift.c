#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int test(int x, int y)
{
    return x << y;
}

int main(int argc, char **argv)
{
    int res = test(atoi(argv[1]), atoi(argv[2]));
    printf("%u\n", res);
    return 0;
}
