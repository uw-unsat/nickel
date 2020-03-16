#include <sys/errno.h>
#include <sys/string.h>
#include "directory.h"
#include "container.h"
#include "pgtable.h"

struct directory *get_directory(kpage_id_t id)
{
        BUG_ON(!(kpage_is_type(id, PAGE_TYPE_PUD) || kpage_is_type(id, PAGE_TYPE_PMD)));
        return page_data(id.id);
}

int untyped_to_directory(page_id_t id, uint64_t type)
{
        struct page *page;
        struct directory *directory;

        BUILD_BUG_ON(sizeof(struct directory) != PAGE_DATA_SIZE);
        BUG_ON((type != PAGE_TYPE_PUD) &&
               (type != PAGE_TYPE_PMD));

        if (!page_is_type(id, PAGE_TYPE_UNTYPED))
                return -EEXIST;

        page = page_get(id);
        page->type = type;
        directory = page_data(id);
        memset(directory->entries, 0, sizeof(directory->entries));
        return 0;
}

int directory_alloc(page_id_t id, uint64_t type)
{
        int r;
        r = page_alloc(id, PAGE_TYPE_UNTYPED);
        if (r)
                return r;
        return untyped_to_directory(id, type);
}

static void directory_pack_entry(page_id_t id, size_t slot, ksymlink_t entry)
{
        struct directoryf *directory;

        directory = page_data(id);

        directory->entries[slot*4+0] = page_id_val(entry.page.id);
        directory->entries[slot*4+1] = entry.page.generation;
        directory->entries[slot*4+2] = page_id_val(entry.parent.id);
        directory->entries[slot*4+3] = entry.parent.generation;
}

static ksymlink_t directory_unpack_entry(page_id_t id, size_t slot)
{
        ksymlink_t entry;
        struct directoryf *directory;

        directory = page_data(id);

        entry.page.id = __page_id(directory->entries[slot*4+0]);
        entry.page.generation = directory->entries[slot*4+1];
        entry.parent.id = __page_id(directory->entries[slot*4+2]);
        entry.parent.generation = directory->entries[slot*4+3];
        return entry;
}

int directory_put(page_id_t id, size_t slot, ksymlink_t subid)
{
        BUG_ON(!page_is_type(id, PAGE_TYPE_PUD));
        BUG_ON(!ksymlink_is_type(subid, PAGE_TYPE_PMD));

        if (!(slot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;

        /* must be an empty slot */
        if (ksymlink_is_viable(directory_unpack_entry(id, slot)))
                return -EINVAL;

        directory_pack_entry(id, slot, subid);

        return 0;
}

ksymlink_t directory_get(page_id_t id, size_t slot)
{
        BUG_ON(!page_is_valid(id));
        BUG_ON(!page_is_type(id, PAGE_TYPE_PGD) &&
               !page_is_type(id, PAGE_TYPE_PUD) &&
               !page_is_type(id, PAGE_TYPE_PMD));
        BUG_ON(!(slot < DIRECTORY_NR_ENTRIES));

        return directory_unpack_entry(id, slot);
}

int directory_link(page_id_t id, size_t slot, ksymlink_t blkid, pteval_t perm)
{
        /* assume 2MB pages */
        BUG_ON(!page_is_type(id, PAGE_TYPE_PMD));
        BUG_ON(!ksymlink_is_type(blkid, PAGE_TYPE_BLOCK));

        if (!(slot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;

        /* must be an empty slot */
        if (ksymlink_is_viable(directory_unpack_entry(id, slot)))
            return -EEXIST;

        directory_pack_entry(id, slot, blkid);
        return 0;
}

int directory_unlink(page_id_t id, size_t slot)
{
        BUG_ON(!(page_is_type(id, PAGE_TYPE_PUD) || page_is_type(id, PAGE_TYPE_PMD)));

        if (!(slot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;

        directory_pack_entry(id, slot, __ksymlink(KPAGE_ID_INVALID, KPAGE_ID_INVALID));

        return 0;
}

int directory_free(page_id_t cid, page_id_t id)
{
        BUG_ON(!page_is_type(id, PAGE_TYPE_PUD) &&
               !page_is_type(id, PAGE_TYPE_PMD));

        container_page_free(cid, page_get(id)->secrecy);
        container_page_free(cid, page_get(id)->integrity);
        container_page_free(cid, id);

        return 0;
}
