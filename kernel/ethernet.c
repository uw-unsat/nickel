#include <sys/ethernet.h>
#include <sys/list.h>

static LIST_HEAD(nets);

void ethernet_register(struct ethernet *net)
{
        list_add_tail(&net->list, &nets);
}

struct ethernet *ethernet_first(void)
{
        return list_first_entry_or_null(&nets, struct ethernet, list);
}
