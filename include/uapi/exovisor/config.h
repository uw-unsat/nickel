#pragma once

#define NR_EPC_PAGES 8192

/*
 * Don't change this:
 * Making it bigger will mean the OS can't access the ones past 2MB
 * Making it smaller will allow the OS to read random pages in the VMM...
 */
#define NR_SHARED_PAGES (SZ_2M / PAGE_SIZE)
