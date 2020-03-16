#include <asm/cpu_entry_area.h>
#include <asm/i8259.h>
#include <asm/msr.h>
#include <asm/ptrace.h>
#include <asm/setup.h>

static uint8_t cpu_gdt[NR_CPUS][PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t entry_stacks[NR_CPUS][PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t exception_stacks[NR_CPUS][NR_EXCEPTION_STACKS * EXCEPTION_STACK_SIZE] __aligned(PAGE_SIZE);
/* per-cpu cpu_tss is used in entry.S */
DEFINE_PER_CPU(uint8_t[PAGE_SIZE], cpu_tss) __aligned(PAGE_SIZE);

static struct segment_desc gdt_data[] = {
        [GDT_ENTRY_KERNEL_CS]   = GDT_ENTRY_INIT(0xa09b, 0, 0xfffff),
        [GDT_ENTRY_KERNEL_DS]   = GDT_ENTRY_INIT(0xc093, 0, 0xfffff),
        [GDT_ENTRY_USER_DS]     = GDT_ENTRY_INIT(0xc0f3, 0, 0xfffff),
        [GDT_ENTRY_USER_CS]     = GDT_ENTRY_INIT(0xa0fb, 0, 0xfffff),
};

static inline void set_tss_desc(struct segment_desc *gdt, unsigned int entry, void *addr)
{
        struct tss_desc tss;

        set_tssldt_descriptor(&tss, (uintptr_t)addr, DESC_TSS, KERNEL_TSS_LIMIT);
        write_gdt_entry(gdt, entry, &tss, DESC_TSS);
}

static void load_direct_gdt(int cpu)
{
        struct desc_ptr gdt = {
                .address = (uintptr_t)get_cpu_gdt_rw(cpu),
                .size = GDT_SIZE - 1,
        };

        load_gdt(&gdt);
}

static void load_fixmap_gdt(int cpu)
{
        struct desc_ptr gdt = {
                .address = (uintptr_t)get_cpu_gdt_ro(cpu),
                .size = GDT_SIZE - 1,
        };

        load_gdt(&gdt);
}

static void switch_to_new_gdt(void)
{
        int cpu = smp_processor_id();
        void *gdt = get_cpu_gdt_rw(cpu);
        struct tss *tss = (struct tss *)per_cpu_ptr(&cpu_tss, cpu);
        size_t i;

        memcpy(gdt, gdt_data, sizeof(gdt_data));

        cea_set_pte(&get_cpu_entry_area(cpu)->gdt, __pa(gdt), PTE_KERNEL_RO);

        load_direct_gdt(cpu);

        cea_set_pte(&get_cpu_entry_area(cpu)->tss, __pa(tss), PTE_KERNEL_RO);

        /* disable IO permission bitmap */
        tss->io_bitmap_base = INVALID_IO_BITMAP_OFFSET;

        /* use per-cpu stack */
        cea_set_pte(&get_cpu_entry_area(cpu)->entry_stack, __pa(&entry_stacks[cpu]), PTE_KERNEL);
        tss->sp0 = (uintptr_t)&get_cpu_entry_area(cpu)->entry_stack + sizeof(struct entry_stack);
        tss->sp1 = (uintptr_t)&cpu_stacks[cpu] + CPU_STACK_SIZE;

        /* set IST pointers */
        for (i = 0; i < NR_EXCEPTION_STACKS; ++i) {
                void *estack = &get_cpu_entry_area(cpu)->exception_stacks[i];

                cea_map_pages(estack, __pa(&exception_stacks[i]), EXCEPTION_STACK_SIZE / PAGE_SIZE, PTE_KERNEL);
                tss->ist[i] = (uintptr_t)estack + EXCEPTION_STACK_SIZE;
        }

        set_tss_desc(gdt, GDT_ENTRY_TSS, &get_cpu_entry_area(cpu)->tss);

        load_tr_desc();

        /* reload gdt as ro after ltr */
        load_fixmap_gdt(cpu);
}

struct segment_desc *get_cpu_gdt_ro(int cpu)
{
        return (struct segment_desc *)&get_cpu_entry_area(cpu)->gdt;
}

struct segment_desc *get_cpu_gdt_rw(int cpu)
{
        return (struct segment_desc *)&cpu_gdt[cpu];
}

struct pt_regs *get_cpu_pt_regs(int cpu)
{
        struct tss *tss = (struct tss *)per_cpu_ptr(&cpu_tss, cpu);

        return (void *)tss->sp0 - sizeof(struct pt_regs);
}

void load_tr_desc(void)
{
        struct desc_ptr gdt;
        int cpu = smp_processor_id();
        bool restore = false;

        store_gdt(&gdt);

        if (gdt.address == (uintptr_t)get_cpu_gdt_ro(cpu)) {
                load_direct_gdt(cpu);
                restore = true;
        }

        asm volatile("ltr %w0" : : "q" (GDT_ENTRY_TSS * 8));

        if (restore)
                load_fixmap_gdt(cpu);
}

#if 0
static void smep_init(void)
{
        if (!this_cpu_has(X86_FEATURE_SMEP))
                return;

        cr4_set_bits(X86_CR4_SMEP);
}

static void smap_init(void)
{
        unsigned long rflags = save_flags();

        /* This should have been cleared long ago */
        BUG_ON(rflags & X86_RFLAGS_AC);

        if (!this_cpu_has(X86_FEATURE_SMAP))
                return;

        cr4_set_bits(X86_CR4_SMAP);
}
#endif

void trap_init(void)
{
        switch_to_new_gdt();

        idt_setup_traps();
        idt_setup_ist_traps();

        /*
         * Initialize legacy 8259; otherwise Bochs will generate
         * spurious interrupts.
         */
        i8259_init();

        idt_setup_apic_and_irq_gates();

        /* disable sysenter */
        wrmsrl(MSR_IA32_SYSENTER_CS, GDT_ENTRY_INVALID_SEG);
        wrmsrl(MSR_IA32_SYSENTER_ESP, 0);
        wrmsrl(MSR_IA32_SYSENTER_EIP, 0);

        wrmsrl(MSR_FS_BASE, 0);
        wrmsrl(MSR_KERNEL_GS_BASE, 0);
}

void syscall_init(void)
{
        extern char __entry_trampoline[], do_syscall_64[], do_syscall_32[];
        uint64_t efer;
        int cpu = smp_processor_id();
        void *entry_trampoline;

        entry_trampoline = get_cpu_entry_area(cpu)->entry_trampoline + (do_syscall_64 - __entry_trampoline);
        cea_set_pte(entry_trampoline, __pa(__entry_trampoline), PTE_KERNEL_RX);

        /* enable syscall */
        efer = rdmsrl(MSR_EFER);
        if (!(efer & EFER_SCE))
                wrmsrl(MSR_EFER, efer | EFER_SCE);

        wrmsr(MSR_STAR, 0, ((USER_CS - 16) << 16) | KERNEL_CS);
        wrmsrl(MSR_LSTAR, (uintptr_t)entry_trampoline);
        wrmsrl(MSR_CSTAR, cpu_entry_area_text_address(do_syscall_32));

        /* flags to clear on syscall */
        wrmsrl(MSR_SYSCALL_MASK,
               X86_RFLAGS_TF|X86_RFLAGS_DF|X86_RFLAGS_IF|
               X86_RFLAGS_IOPL|X86_RFLAGS_AC|X86_RFLAGS_NT);
}
