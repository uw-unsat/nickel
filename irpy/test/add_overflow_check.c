#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int __attribute__((noinline)) add(int x, int y) { return x + y; }

/* Beware signed overflow :) */
int test(int x, int y)
{
	if (x < -5000 || x > 5000 || y < -5000 || y > 5000)
		return 0;
	else
        return add(x, y);
}

int main(int argc, char **argv)
{
    int res = test(atoi(argv[1]), atoi(argv[2]));
    printf("%u\n", res);
    return 0;
}
