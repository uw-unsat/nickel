#include <stdio.h>
#include <nistar/env.h>
#include <nistar/ulib.h>

long gate_test(uint64_t arg0, uint64_t arg1)
{
        printf("gate_test: %ld %ld\n", arg0, arg1);
        return 1339;
}

int main()
{
        usymlink_t gate;
        struct label secrecy;
        struct label integrity;
        struct label ownership;
        struct label guard;
        self_get_label(&secrecy, &integrity, &ownership);
        label_init(&guard);
        alloc_call_gate(&gate, self_get_internal_container(), &secrecy, &integrity,
                        &ownership, &guard, self_get_pud(), gate_test, 1337, "test");
        long r = gate_call(gate, self_get_internal_container(), 1338);
        printf("gate return: %ld\n", r);
        return 0;
}
