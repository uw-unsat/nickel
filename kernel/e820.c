#include <asm/e820.h>
#include <io/mmu.h>
#include <sys/multiboot.h>
#include <sys/sort.h>
#include <sys/string.h>

struct e820_table e820_table;

/*
 * This function checks if the entire <start,end> range is mapped with 'type'.
 *
 * Note: this function only works correctly once the E820 table is sorted and
 * not-overlapping (at least for the range specified), which is the case normally.
 */
bool e820_mapped_all(uint64_t start, uint64_t end, enum e820_type type)
{
        int i;

        for (i = 0; i < e820_table.nr_entries; i++) {
                struct e820_entry *entry = &e820_table.entries[i];

                if (type && entry->type != type)
                        continue;

                /* Is the region (part) in overlap with the current region? */
                if (entry->addr >= end || entry->addr + entry->size <= start)
                        continue;

                /*
                 * If the region is at the beginning of <start,end> we move
                 * 'start' to the end of the region since it's ok until there
                 */
                if (entry->addr <= start)
                        start = entry->addr + entry->size;

                /*
                 * If 'start' is now at or beyond 'end', we're done, full
                 * coverage of the desired range exists:
                 */
                if (start >= end)
                        return 1;
        }
        return 0;
}

/*
 * Add a memory region to the kernel E820 map.
 */
static void __e820_range_add(struct e820_table *table, uint64_t start, uint64_t size, enum e820_type type)
{
        int x = table->nr_entries;

        if (x >= ARRAY_SIZE(table->entries)) {
                pr_err("e820: too many entries; ignoring [mem %#010" PRIx64 "-%#010" PRIx64 "]\n", start, start + size - 1);
                return;
        }

        table->entries[x].addr = start;
        table->entries[x].size = size;
        table->entries[x].type = type;
        table->nr_entries++;
}

void e820_range_add(uint64_t start, uint64_t size, enum e820_type type)
{
        __e820_range_add(&e820_table, start, size, type);
}

static void e820_print_type(enum e820_type type)
{
        switch (type) {
        case E820_TYPE_RAM:             pr_cont("usable");              break;
        case E820_TYPE_RESERVED:        pr_cont("reserved");            break;
        case E820_TYPE_ACPI:            pr_cont("ACPI data");           break;
        case E820_TYPE_NVS:             pr_cont("ACPI NVS");            break;
        case E820_TYPE_UNUSABLE:        pr_cont("unusable");            break;
        case E820_TYPE_PMEM:            pr_cont("persistent");          break;
        default:                        pr_cont("type %u", type);       break;
        }
}

void e820_print_table(char *who)
{
        int i;

        for (i = 0; i < e820_table.nr_entries; i++) {
                pr_info("%s: [mem %#018" PRIx64 "-%#018" PRIx64 "] ", who,
                        e820_table.entries[i].addr,
                        e820_table.entries[i].addr + e820_table.entries[i].size - 1);

                e820_print_type(e820_table.entries[i].type);
                pr_cont("\n");
        }
}

/*
 * Sanitize an E820 map.
 *
 * Some E820 layouts include overlapping entries. The following
 * replaces the original E820 map with a new one, removing overlaps,
 * and resolving conflicting memory types in favor of highest
 * numbered type.
 *
 * The input parameter 'entries' points to an array of 'struct
 * e820_entry' which on entry has elements in the range [0, *nr_entries)
 * valid, and which has space for up to max_nr_entries entries.
 * On return, the resulting sanitized E820 map entries will be in
 * overwritten in the same location, starting at 'entries'.
 *
 * The integer pointed to by nr_entries must be valid on entry (the
 * current number of valid entries located at 'entries'). If the
 * sanitizing succeeds the *nr_entries will be updated with the new
 * number of valid entries (something no more than max_nr_entries).
 *
 * The return value from e820_update_table() is zero if it
 * successfully 'sanitized' the map entries passed in, and is -1
 * if it did nothing, which can happen if either of (1) it was
 * only passed one map entry, or (2) any of the input map entries
 * were invalid (start + size < start, meaning that the size was
 * so big the described memory range wrapped around through zero.)
 *
 *      Visually we're performing the following
 *      (1,2,3,4 = memory types)...
 *
 *      Sample memory map (w/overlaps):
 *         ____22__________________
 *         ______________________4_
 *         ____1111________________
 *         _44_____________________
 *         11111111________________
 *         ____________________33__
 *         ___________44___________
 *         __________33333_________
 *         ______________22________
 *         ___________________2222_
 *         _________111111111______
 *         _____________________11_
 *         _________________4______
 *
 *      Sanitized equivalent (no overlap):
 *         1_______________________
 *         _44_____________________
 *         ___1____________________
 *         ____22__________________
 *         ______11________________
 *         _________1______________
 *         __________3_____________
 *         ___________44___________
 *         _____________33_________
 *         _______________2________
 *         ________________1_______
 *         _________________4______
 *         ___________________2____
 *         ____________________33__
 *         ______________________4_
 */
struct change_member {
        /* Pointer to the original entry: */
        struct e820_entry       *entry;
        /* Address for this change point: */
        unsigned long long      addr;
};

static struct change_member     change_point_list[2*E820_MAX_ENTRIES];
static struct change_member     *change_point[2*E820_MAX_ENTRIES];
static struct e820_entry        *overlap_list[E820_MAX_ENTRIES];
static struct e820_entry        new_entries[E820_MAX_ENTRIES];

static int cpcompare(const void *a, const void *b)
{
        struct change_member * const *app = a, * const *bpp = b;
        const struct change_member *ap = *app, *bp = *bpp;

        /*
         * Inputs are pointers to two elements of change_point[].  If their
         * addresses are not equal, their difference dominates.  If the addresses
         * are equal, then consider one that represents the end of its region
         * to be greater than one that does not.
         */
        if (ap->addr != bp->addr)
                return ap->addr > bp->addr ? 1 : -1;

        return (ap->addr != ap->entry->addr) - (bp->addr != bp->entry->addr);
}

static int __e820_update_table(struct e820_table *table)
{
        struct e820_entry *entries = table->entries;
        uint32_t max_nr_entries = ARRAY_SIZE(table->entries);
        enum e820_type current_type, last_type;
        unsigned long long last_addr;
        uint32_t new_nr_entries, overlap_entries;
        uint32_t i, chg_idx, chg_nr;

        /* If there's only one memory region, don't bother: */
        if (table->nr_entries < 2)
                return -1;

        BUG_ON(table->nr_entries > max_nr_entries);

        /* Bail out if we find any unreasonable addresses in the map: */
        for (i = 0; i < table->nr_entries; i++) {
                if (entries[i].addr + entries[i].size < entries[i].addr)
                        return -1;
        }

        /* Create pointers for initial change-point information (for sorting): */
        for (i = 0; i < 2 * table->nr_entries; i++)
                change_point[i] = &change_point_list[i];

        /*
         * Record all known change-points (starting and ending addresses),
         * omitting empty memory regions:
         */
        chg_idx = 0;
        for (i = 0; i < table->nr_entries; i++) {
                if (entries[i].size != 0) {
                        change_point[chg_idx]->addr     = entries[i].addr;
                        change_point[chg_idx++]->entry  = &entries[i];
                        change_point[chg_idx]->addr     = entries[i].addr + entries[i].size;
                        change_point[chg_idx++]->entry  = &entries[i];
                }
        }
        chg_nr = chg_idx;

        /* Sort change-point list by memory addresses (low -> high): */
        sort(change_point, chg_nr, sizeof(*change_point), cpcompare, NULL);

        /* Create a new memory map, removing overlaps: */
        overlap_entries = 0;     /* Number of entries in the overlap table */
        new_nr_entries = 0;      /* Index for creating new map entries */
        last_type = 0;           /* Start with undefined memory type */
        last_addr = 0;           /* Start with 0 as last starting address */

        /* Loop through change-points, determining effect on the new map: */
        for (chg_idx = 0; chg_idx < chg_nr; chg_idx++) {
                /* Keep track of all overlapping entries */
                if (change_point[chg_idx]->addr == change_point[chg_idx]->entry->addr) {
                        /* Add map entry to overlap list (> 1 entry implies an overlap) */
                        overlap_list[overlap_entries++] = change_point[chg_idx]->entry;
                } else {
                        /* Remove entry from list (order independent, so swap with last): */
                        for (i = 0; i < overlap_entries; i++) {
                                if (overlap_list[i] == change_point[chg_idx]->entry)
                                        overlap_list[i] = overlap_list[overlap_entries-1];
                        }
                        overlap_entries--;
                }
                /*
                 * If there are overlapping entries, decide which
                 * "type" to use (larger value takes precedence --
                 * 1=usable, 2,3,4,4+=unusable)
                 */
                current_type = 0;
                for (i = 0; i < overlap_entries; i++) {
                        if (overlap_list[i]->type > current_type)
                                current_type = overlap_list[i]->type;
                }

                /* Continue building up new map based on this information: */
                if (current_type != last_type) {
                        if (last_type != 0) {
                                new_entries[new_nr_entries].size = change_point[chg_idx]->addr - last_addr;
                                /* Move forward only if the new size was non-zero: */
                                if (new_entries[new_nr_entries].size != 0)
                                        /* No more space left for new entries? */
                                        if (++new_nr_entries >= max_nr_entries)
                                                break;
                        }
                        if (current_type != 0)  {
                                new_entries[new_nr_entries].addr = change_point[chg_idx]->addr;
                                new_entries[new_nr_entries].type = current_type;
                                last_addr = change_point[chg_idx]->addr;
                        }
                        last_type = current_type;
                }
        }

        /* Copy the new entries into the original location: */
        memcpy(entries, new_entries, new_nr_entries*sizeof(*entries));
        table->nr_entries = new_nr_entries;

        return 0;
}

void e820_update_table(void)
{
        if (__e820_update_table(&e820_table))
                panic("e820: fail to sanitize the physical RAM map\n");
}

void e820_update_table_print(void)
{
        e820_update_table();

        pr_info("e820: modified physical RAM map:\n");
        e820_print_table("modified");
}

static uint64_t __e820_range_update(struct e820_table *table, uint64_t start, uint64_t size, enum e820_type old_type, enum e820_type new_type)
{
        uint64_t end;
        unsigned int i;
        uint64_t real_updated_size = 0;

        BUG_ON(old_type == new_type);

        if (size > (ULLONG_MAX - start))
                size = ULLONG_MAX - start;

        end = start + size;
        pr_info("e820: update [mem %#010" PRIx64 "-%#010" PRIx64 "] ", start, end - 1);
        e820_print_type(old_type);
        pr_cont(" ==> ");
        e820_print_type(new_type);
        pr_cont("\n");

        for (i = 0; i < table->nr_entries; i++) {
                struct e820_entry *entry = &table->entries[i];
                uint64_t final_start, final_end;
                uint64_t entry_end;

                if (entry->type != old_type)
                        continue;

                entry_end = entry->addr + entry->size;

                /* Completely covered by new range? */
                if (entry->addr >= start && entry_end <= end) {
                        entry->type = new_type;
                        real_updated_size += entry->size;
                        continue;
                }

                /* New range is completely covered? */
                if (entry->addr < start && entry_end > end) {
                        __e820_range_add(table, start, size, new_type);
                        __e820_range_add(table, end, entry_end - end, entry->type);
                        entry->size = start - entry->addr;
                        real_updated_size += size;
                        continue;
                }

                /* Partially covered: */
                final_start = max(start, entry->addr);
                final_end = min(end, entry_end);
                if (final_start >= final_end)
                        continue;

                __e820_range_add(table, final_start, final_end - final_start, new_type);

                real_updated_size += final_end - final_start;

                /*
                 * Left range could be head or tail, so need to update
                 * its size first:
                 */
                entry->size -= final_end - final_start;
                if (entry->addr < final_start)
                        continue;

                entry->addr = final_end;
        }
        return real_updated_size;
}

uint64_t e820_range_update(uint64_t start, uint64_t size, enum e820_type old_type, enum e820_type new_type)
{
        return __e820_range_update(&e820_table, start, size, old_type, new_type);
}

/* Find the highest page frame number we have available */
static unsigned long e820_end_pfn(unsigned long limit_pfn, enum e820_type type)
{
        int i;
        unsigned long last_pfn = 0;
        unsigned long max_arch_pfn = MAXMEM_PFN;

        for (i = 0; i < e820_table.nr_entries; i++) {
                struct e820_entry *entry = &e820_table.entries[i];
                unsigned long start_pfn;
                unsigned long end_pfn;

                if (entry->type != type)
                        continue;

                start_pfn = entry->addr >> PAGE_SHIFT;
                end_pfn = (entry->addr + entry->size) >> PAGE_SHIFT;

                if (start_pfn >= limit_pfn)
                        continue;
                if (end_pfn > limit_pfn) {
                        last_pfn = limit_pfn;
                        break;
                }
                if (end_pfn > last_pfn)
                        last_pfn = end_pfn;
        }

        if (last_pfn > max_arch_pfn)
                last_pfn = max_arch_pfn;

        pr_info("e820: last_pfn = %#lx max_arch_pfn = %#lx\n",
                last_pfn, max_arch_pfn);
        return last_pfn;
}

unsigned long e820_end_of_ram_pfn(void)
{
        return e820_end_pfn(MAXMEM_PFN, E820_TYPE_RAM);
}

void e820_range_add_multiboot(struct multiboot_mmap_entry *e, size_t len)
{
        size_t i, skip;

        for (i = 0; i < len; ) {
                e820_range_add(e->addr, e->len, e->type);
                skip = e->size + sizeof(e->size);
                i += skip;
                e = (void *)e + skip;
        }
        e820_update_table();
        e820_print_table("BIOS-e820");
}
