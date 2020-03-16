#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

uint64_t global = 7;

int main(int argc, char **argv) {
        uint64_t stackvar = 8;
        pid_t pid = fork();
        if (pid == 0) {
                printf("Child %ld %ld\n", global, stackvar);
                global = 19;
                stackvar = 20;
        } else {
                wait(NULL);
                printf("Parent %ld %ld\n", global, stackvar, pid);
        }
        return 0;
}

