#pragma once

#include <sys/bug.h>
#include <uapi/asm/debugreg.h>

/*
 * These special macros can be used to get or set a debugging register
 */
#define get_debugreg(var, register)                             \
        (var) = native_get_debugreg(register)
#define set_debugreg(value, register)                           \
        native_set_debugreg(register, value)

static inline unsigned long native_get_debugreg(int regno)
{       
        unsigned long val = 0;  /* Damn you, gcc! */
        
        switch (regno) {
        case 0: 
                asm("mov %%db0, %0" :"=r" (val));
                break;
        case 1: 
                asm("mov %%db1, %0" :"=r" (val));
                break;
        case 2: 
                asm("mov %%db2, %0" :"=r" (val));
                break;
        case 3: 
                asm("mov %%db3, %0" :"=r" (val));
                break;
        case 6: 
                asm("mov %%db6, %0" :"=r" (val));
                break;
        case 7: 
                asm("mov %%db7, %0" :"=r" (val));
                break;
        default:
                BUG();
        }
        return val;
}

static inline void native_set_debugreg(int regno, unsigned long value)
{       
        switch (regno) {
        case 0: 
                asm("mov %0, %%db0"     ::"r" (value));
                break;
        case 1: 
                asm("mov %0, %%db1"     ::"r" (value));
                break;
        case 2: 
                asm("mov %0, %%db2"     ::"r" (value));
                break;
        case 3: 
                asm("mov %0, %%db3"     ::"r" (value));
                break;
        case 6: 
                asm("mov %0, %%db6"     ::"r" (value));
                break;
        case 7: 
                asm("mov %0, %%db7"     ::"r" (value));
                break;
        default:
                BUG();
        }
}
