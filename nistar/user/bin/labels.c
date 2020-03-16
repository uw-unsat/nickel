#include <nistar/ulib.h>
#include <stdio.h>

int main() {
        struct label secrecy, integrity, ownership;
        self_get_label(&secrecy, &integrity, &ownership);
        char buf[256];
        label_format(&secrecy, buf, sizeof(buf));
        printf("Secrecy:\t%s\n", buf);
        label_format(&integrity, buf, sizeof(buf));
        printf("Integrity:\t%s\n", buf);
        label_format(&ownership, buf, sizeof(buf));
        printf("Ownership:\t%s\n", buf);
        return 0;
}
