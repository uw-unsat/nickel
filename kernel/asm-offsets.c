#include <asm/cpu_entry_area.h>
#include <io/kbuild.h>

int main(void)
{
        /* layout info for cpu_entry_area */
        OFFSET(CPU_ENTRY_AREA_tss, cpu_entry_area, tss);
        OFFSET(CPU_ENTRY_AREA_entry_trampoline, cpu_entry_area, entry_trampoline);
        OFFSET(CPU_ENTRY_AREA_entry_stack, cpu_entry_area, entry_stack);
        DEFINE(SIZEOF_entry_stack, sizeof(struct entry_stack));

        OFFSET(TSS_ist, tss, ist);
        OFFSET(TSS_sp0, tss, sp0);
        OFFSET(TSS_sp1, tss, sp1);
        BLANK();

        return 0;
}
