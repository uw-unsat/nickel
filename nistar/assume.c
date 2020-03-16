#include "assume.h"

noinline void ASSUME(bool cond)
{
        BUG_ON(!cond);
}
