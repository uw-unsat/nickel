#pragma once

int hs_fexecve(int fd, char *const argv[], char *const envp[]);
int hs_execve(int fd, char *const argv[], char *const envp[]);
