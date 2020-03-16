#include <asm/cpufeature.h>
#include <sys/ctype.h>
#include <sys/string.h>

struct cpu_dev {
        /* some have two possibilities for cpuid string */
        const char      *c_ident[2];
        int             c_x86_vendor;
};

static const struct cpu_dev intel_cpu_dev = {
        .c_ident        = { "GenuineIntel" },
        .c_x86_vendor   = X86_VENDOR_INTEL,
};

static const struct cpu_dev amd_cpu_dev = {
        .c_ident        = { "AuthenticAMD" },
        .c_x86_vendor   = X86_VENDOR_AMD,
};

static const struct cpu_dev *cpu_devs[] = {
        &intel_cpu_dev,
        &amd_cpu_dev,
};

DEFINE_PER_CPU(struct cpuinfo_x86, cpu_info);

static void cpu_detect(struct cpuinfo_x86 *c);
static void get_cpu_vendor(struct cpuinfo_x86 *c);
static void get_cpu_cap(struct cpuinfo_x86 *c);
static void get_model_name(struct cpuinfo_x86 *c);

void cpu_init(void)
{
        struct cpuinfo_x86 *c = this_cpu_ptr(&cpu_info);

        cpu_detect(c);
        get_cpu_vendor(c);
        get_cpu_cap(c);
        get_model_name(c);
}

static unsigned int x86_family(unsigned int sig)
{
        unsigned int x86;

        x86 = (sig >> 8) & 0xf;

        if (x86 == 0xf)
                x86 += (sig >> 20) & 0xff;

        return x86;
}

static unsigned int x86_model(unsigned int sig)
{
        unsigned int fam, model;

        fam = x86_family(sig);

        model = (sig >> 4) & 0xf;

        if (fam >= 0x6)
                model += ((sig >> 16) & 0xf) << 4;

        return model;
}

static unsigned int x86_stepping(unsigned int sig)
{
        return sig & 0xf;
}

static void cpu_detect(struct cpuinfo_x86 *c)
{
        /* Get vendor name */
        cpuid(0x00000000, (unsigned int *)&c->cpuid_level,
              (unsigned int *)&c->x86_vendor_id[0],
              (unsigned int *)&c->x86_vendor_id[8],
              (unsigned int *)&c->x86_vendor_id[4]);

        c->x86 = 4;
        /* Intel-defined flags: level 0x00000001 */
        if (c->cpuid_level >= 0x00000001) {
                uint32_t junk, tfms, cap0, misc;

                cpuid(0x00000001, &tfms, &misc, &junk, &cap0);
                c->x86          = x86_family(tfms);
                c->x86_model    = x86_model(tfms);
                c->x86_mask     = x86_stepping(tfms);
        }
}

static void get_cpu_vendor(struct cpuinfo_x86 *c)
{
        char *v = c->x86_vendor_id;
        int i;

        for (i = 0; i < ARRAY_SIZE(cpu_devs); i++) {
                const struct cpu_dev *cpu_dev = cpu_devs[i];

                if (!cpu_dev)
                        break;

                if (!strcmp(v, cpu_dev->c_ident[0]) ||
                    (cpu_dev->c_ident[1] && !strcmp(v, cpu_dev->c_ident[1]))) {
                        c->x86_vendor = cpu_dev->c_x86_vendor;
                        return;
                }
        }

        pr_warn("cpu: vendor_id '%.12s' unknown\n", v);
        c->x86_vendor = X86_VENDOR_UNKNOWN;
}

static void get_cpu_cap(struct cpuinfo_x86 *c)
{
        uint32_t eax, ebx, ecx, edx;

        /* Intel-defined flags: level 0x00000001 */
        if (c->cpuid_level >= 0x00000001) {
                cpuid(0x00000001, &eax, &ebx, &ecx, &edx);
                c->x86_capability[CPUID_1_ECX] = ecx;
                c->x86_capability[CPUID_1_EDX] = edx;
        }

        /* Thermal and Power Management Leaf: level 0x00000006 (eax) */
        if (c->cpuid_level >= 0x00000006)
                c->x86_capability[CPUID_6_EAX] = cpuid_eax(0x00000006);

        /* Additional Intel-defined flags: level 0x00000007 */
        if (c->cpuid_level >= 0x00000007) {
                cpuid_count(0x00000007, 0, &eax, &ebx, &ecx, &edx);
                c->x86_capability[CPUID_7_0_EBX] = ebx;
                c->x86_capability[CPUID_7_ECX] = ecx;
        }

        /* Extended state features: level 0x0000000d */
        if (c->cpuid_level >= 0x0000000d) {
                cpuid_count(0x0000000d, 1, &eax, &ebx, &ecx, &edx);
                c->x86_capability[CPUID_D_1_EAX] = eax;
        }

        /* Additional Intel-defined flags: level 0x0000000F */
        if (c->cpuid_level >= 0x0000000F) {
                /* QoS sub-leaf, EAX=0Fh, ECX=0 */
                cpuid_count(0x0000000F, 0, &eax, &ebx, &ecx, &edx);
                c->x86_capability[CPUID_F_0_EDX] = edx;

                if (cpu_has(c, X86_FEATURE_CQM_LLC)) {
                        /* QoS sub-leaf, EAX=0Fh, ECX=1 */
                        cpuid_count(0x0000000F, 1, &eax, &ebx, &ecx, &edx);
                        c->x86_capability[CPUID_F_1_EDX] = edx;
                }
        }

        /* AMD-defined flags: level 0x80000001 */
        eax = cpuid_eax(0x80000000);
        c->extended_cpuid_level = eax;

        if ((eax & 0xffff0000) == 0x80000000) {
                if (eax >= 0x80000001) {
                        cpuid(0x80000001, &eax, &ebx, &ecx, &edx);
                        c->x86_capability[CPUID_8000_0001_ECX] = ecx;
                        c->x86_capability[CPUID_8000_0001_EDX] = edx;
                }
        }

        if (c->extended_cpuid_level >= 0x80000007)
                c->x86_capability[CPUID_8000_0007_EBX] = cpuid_ebx(0x80000007);

        if (c->extended_cpuid_level >= 0x80000008)
                c->x86_capability[CPUID_8000_0008_EBX] = cpuid_ebx(0x80000008);

        if (c->extended_cpuid_level >= 0x8000000a)
                c->x86_capability[CPUID_8000_000A_EDX] = cpuid_edx(0x8000000a);
}

static void get_model_name(struct cpuinfo_x86 *c)
{
        unsigned int *v;
        char *p, *q, *s;

        if (c->extended_cpuid_level < 0x80000004)
                return;

        v = (unsigned int *)c->x86_model_id;
        cpuid(0x80000002, &v[0], &v[1], &v[2], &v[3]);
        cpuid(0x80000003, &v[4], &v[5], &v[6], &v[7]);
        cpuid(0x80000004, &v[8], &v[9], &v[10], &v[11]);
        c->x86_model_id[48] = 0;

        /* Trim whitespace */
        p = q = s = &c->x86_model_id[0];

        while (*p == ' ')
                p++;

        while (*p) {
                /* Note the last non-whitespace index */
                if (!isspace(*p))
                        s = q;

                *q++ = *p++;
        }

        *(s + 1) = '\0';
}
