#include <emmintrin.h>

__attribute__((__vector_size__(2 * sizeof(long long)))) long long melttest(__m128i val1, __m128i val2)
{
    return val1 == val2;
}
