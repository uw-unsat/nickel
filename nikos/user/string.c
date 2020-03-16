#include "user.h"

size_t strlen(const char *s)
{
        size_t n;

        for (n = 0; s[n]; n++)
                ;
        return n;
}
