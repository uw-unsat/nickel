#include "block.h"
#include "container.h"
#include "mm.h"
#include "thread.h"

noinline bool implies(bool a, bool b)
{
    return !a || b;
}

noinline bool not(bool a)
{
    return !a;
}

noinline bool and2(bool a, bool b)
{
    return a && b;
}

/* bool __attribute__((noinline)) and3(bool a, bool b, bool c) */
/* { */
/*     return a && b && c; */
/* } */
/*  */
/* bool __attribute__((noinline)) and4(bool a, bool b, bool c, bool d) */
/* { */
/*     return a && b && c && d; */
/* } */
/*  */
/* bool __attribute__((noinline)) and5(bool a, bool b, bool c, bool d, bool e) */
/* { */
/*     return a && b && c && d && e; */
/* } */
/*  */
/* bool __attribute__((noinline)) and6(bool a, bool b, bool c, bool d, bool e, bool f) */
/* { */
/*     return a && b && c && d && e && f; */
/* } */
/*  */
/* bool __attribute__((noinline)) and7(bool a, bool b, bool c, bool d, bool e, bool f, bool g) */
/* { */
/*     return a && b && c && d && e && f && g; */
/* } */
/*  */
/* bool __attribute__((noinline)) and8(bool a, bool b, bool c, bool d, bool e, bool f, bool g, bool h) */
/* { */
/*     return a && b && c && d && e && f && g && h; */
/* } */
/*  */
/* bool __attribute__((noinline)) and9(bool a, bool b, bool c, bool d, bool e, bool f, bool g, bool h, bool i) */
/* { */
/*     return a && b && c && d && e && f && g && h && i; */
/* } */
/*  */
/* bool __attribute__((noinline)) or2(bool a, bool b) */
/* { */
/*     return a || b; */
/* } */
/*  */
/* bool __attribute__((noinline)) or3(bool a, bool b, bool c) */
/* { */
/*     return a || b || c; */
/* } */
/*  */
/* bool __attribute__((noinline)) or4(bool a, bool b, bool c, bool d) */
/* { */
/*     return a || b || c || d; */
/* } */

// Sum of quota for all containers should equal the number of free pages
static bool check_quota()
{
        size_t quota = 0;
        size_t free = 0;
        size_t uquota = 0;
        size_t ufree = 0;
        size_t i;

        for (i = 0; i < NR_PAGES; i++) {
                if (page_is_type(__page_id(i), PAGE_TYPE_NONE))
                        free++;
                if (page_is_type(__page_id(i), PAGE_TYPE_CONTAINER)) {
                        quota += page_get(__page_id(i))->c_quota;
                        uquota += page_get(__page_id(i))->c_uquota;
                }
        }
        for (i = 0; i < NR_PAGE2M; i++) {
                if (page2m_is_free(__page2m_id(i)))
                        ufree++;
        }

        return quota == free && uquota == ufree;
}

static bool check_freelist()
{
        page_id_t cur = root_container_id;
        uint64_t quota = page_get(cur)->c_quota;

        while (quota > 0) {
                BUG_ON(!page_is_valid(page_get(cur)->freelist_next));
                cur = page_get(cur)->freelist_next;
                if (!page_is_type(cur, PAGE_TYPE_NONE))
                        pr_info("Found page with type %ld %ld\n", page_get(cur)->type, quota);
                BUG_ON(!page_is_type(cur, PAGE_TYPE_NONE));
                quota--;
        }
        return true;
}

static bool check_ufreelist()
{
        page2m_id_t cur = page_get(root_container_id)->ufreelist_next;
        uint64_t quota = page_get(root_container_id)->c_uquota-1;

        while (quota > 0) {
                BUG_ON(!page2m_is_valid(page2m_get(cur)->next));
                cur = page2m_get(cur)->next;
                if (!page2m_is_free(cur)) {
                        pr_info("Found page with type %ld %ld\n", page2m_id_val(cur), quota);
                }
                BUG_ON(!page2m_is_free(cur));
                quota--;
        }
        return true;
}

bool root_container_id_valid()
{
        return page_is_valid(root_container_id);
}

bool current_thread_valid()
{
        return page_is_valid(get_current_thread());
}

bool current_thread_thread()
{
        page_id_t tid = get_current_thread();
        return page_get(tid)->type == PAGE_TYPE_THREAD;
}

bool secrecy_integrity_valid(page_id_t p)
{
        return implies(and2(page_is_valid(p),
                           not(page_is_type(p, PAGE_TYPE_NONE))),
                       and2(page_is_type(page_get(p)->integrity, PAGE_TYPE_LABEL),
                            page_is_type(page_get(p)->secrecy, PAGE_TYPE_LABEL)));
}

bool check_invariants()
{
        bool r = true;

        r &= check_quota();
        r &= check_freelist();
        r &= check_ufreelist();
        r &= root_container_id_valid();
        r &= current_thread_valid();

        return r;
}
