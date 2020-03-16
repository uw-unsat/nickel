#include <dirent.h>
#include <fcntl.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>


char *fmtname(char *path)
{
        static char buf[32];
        char *p;

        /* find first character after last slash */
        for (p = path + strlen(path); p >= path && *p != '/'; p--)
                ;
        p++;

        /* return blank-padded name */
        if (strlen(p) >= sizeof(buf) - 1)
                return p;
        memmove(buf, p, strlen(p));
        memset(buf + strlen(p), ' ', sizeof(buf) - 1 - strlen(p));
        return buf;
}

int ls(char *path)
{
        char pathname[512];
        struct dirent *de;
        DIR *dir;
        struct stat st;

        if (lstat(path, &st) < 0) {
                fprintf(stderr, "ls: cannot stat %s\n", path);
                return -1;
        }

        switch (st.st_mode) {
                case S_IFREG:
                        printf("%s %d %lu %lu\n", fmtname(path), st.st_mode, st.st_ino, st.st_size);
                        break;

                case S_IFDIR:
                        if ((dir = opendir(path)) < 0) {
                                fprintf(stderr, "ls: cannot open %s\n", path);
                                return -1;
                        }

                        while ((de = readdir(dir)) != NULL) {
                                strlcpy(pathname, path, sizeof(pathname));
                                strlcat(pathname, "/", sizeof(pathname));
                                strlcat(pathname, de->d_name, sizeof(pathname));
                                if (lstat(pathname, &st) < 0) {
                                        fprintf(stderr, "ls: cannot stat %s\n", de->d_name);
                                        return -1;
                                }

                                printf("%s %d %lu %lu\n", fmtname(de->d_name), st.st_mode, st.st_ino, st.st_size);
                        }


                        closedir(dir);
        }
        return 0;
}

int main(int argc, char *argv[])
{
        int i;

        if (argc < 2) {
                return ls(".");
        }
        for (i = 1; i < argc; i++)
                return ls(argv[i]);

        return 0;
}
