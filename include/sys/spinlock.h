#pragma once

#include <asm/processor.h>

struct spinlock {
        atomic_flag val;
};

#define SPINLOCK_INIT           { ATOMIC_FLAG_INIT }
#define DEFINE_SPINLOCK(x)      struct spinlock x = SPINLOCK_INIT

static inline void spinlock_init(struct spinlock *lock)
{
        atomic_flag_clear(&lock->val);
}

/*
 * Returns true if it acquires the lock, or false if not.
 */
static inline bool spin_trylock(struct spinlock *lock)
{
        return !atomic_flag_test_and_set_explicit(&lock->val, memory_order_acquire);
}

static inline void spin_lock(struct spinlock *lock)
{
        while (!spin_trylock(lock))
                cpu_relax();
}

static inline void spin_unlock(struct spinlock *lock)
{
        atomic_flag_clear_explicit(&lock->val, memory_order_release);
}
