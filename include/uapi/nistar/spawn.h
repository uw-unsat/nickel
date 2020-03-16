#pragma once

long fspawn(int fd, char *const argv[], char *const envp[]);
int spawn(const char *path, char *const argv[], char *const envp[]);
