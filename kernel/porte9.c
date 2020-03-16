#include <asm/io.h>
#include <sys/console.h>
#include <sys/string.h>

#define END_COLOR "\x1b[0m"

static const char *prefix;

static void porte9_write(struct console *con, const char *s, size_t n)
{
        if (prefix)
                outsb(0xe9, prefix, strlen(prefix));
        outsb(0xe9, s, n);
        outsb(0xe9, END_COLOR, sizeof(END_COLOR) - 1);
}

static struct console con = {
        .write = porte9_write,
};

void porte9_init(const char *s)
{
        prefix = s;
        register_console(&con);
}
