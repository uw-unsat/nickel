#include <nistar/spawn.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>

extern char **environ;

int main(int argc, char **argv) {
        printf("Start\n");
        argv[0] = "/bin/hello";
        spawn(argv[0], argv, environ);
        wait(NULL);
        printf("After spawn\n");
        return 0;
}
