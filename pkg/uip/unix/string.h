#pragma once

#include <sys/string.h>

/*
 * The semantics of the return values are different,
 * though they are okay for this simple test.
 */
#define snprintf        scnprintf
#define strncpy         strscpy

#define strcpy(t, s)    strscpy(t, s, -1)
