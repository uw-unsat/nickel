#pragma once

#include <sys/types.h>

int memcmp(const void *dest, const void *src, size_t count);
size_t memfind64(const uint64_t *s, uint64_t v, size_t n);
size_t memfind128(const unsigned __int128 *s, unsigned __int128 v, size_t n);
void *memset(void *s, int c, size_t count);
void *memset64(uint64_t *s, uint64_t v, size_t n);
void *memcpy(void *dest, const void *src, size_t count);
void *memmove(void *dest, const void *src, size_t count);
void memzero_explicit(void *s, size_t count);

char *strchr(const char *s, int c);
int strcmp(const char *dest, const char *src);
size_t strlen(const char *s);
int strncmp(const char *dest, const char *src, size_t count);
size_t strnlen(const char *s, size_t count);
char *strrchr(const char *s, int c);
ssize_t strscpy(char *dest, const char *src, size_t count);
char *strstr(const char *haystack, const char *needle);
