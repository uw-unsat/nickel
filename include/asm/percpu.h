#pragma once

#if defined(__IRPY__)

#define PER_CPU_VAR(var)        var

#define this_cpu_read(pcp) pcp

#define this_cpu_write(pcp, val) ({pcp = val;})

#else

#ifdef __ASSEMBLER__

/* keep %gs even if NR_CPU is 1 for shared mamping; see entry.S */
#define PER_CPU_VAR(var)        %gs:var

#else /* !__ASSEMBLER__ */

#define this_cpu_read(pcp)                                      \
({                                                              \
        typeof(pcp) _val;                                       \
        asm("mov %%gs:%1, %0" : "=r" (_val) : "m" (pcp));       \
        _val;                                                   \
})

#define this_cpu_write(pcp, val)                                \
({                                                              \
        asm("mov %1, %%gs:%0" : "+m" (pcp) : "r" (val));        \
})

#endif /* !__ASSEMBLER__ */

#endif /* !__IRPY__ */