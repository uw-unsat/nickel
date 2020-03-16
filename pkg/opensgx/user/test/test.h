#pragma once

#include <opensgx/sgx-lib.h>
#include <sys/errno.h>

#define O_RDONLY        00
#define O_WRONLY        01
#define O_ASYNC         020000

#define S_IFIFO         0010000

#define PF_INET         2
#define AF_INET         PF_INET
#define SOCK_STREAM     1
#define INADDR_ANY      ((in_addr_t) 0x00000000)

typedef uint64_t        dev_t;
typedef uint32_t        mode_t;
typedef long            ssize_t;

typedef uint16_t        in_port_t;
typedef uint32_t        in_addr_t;
typedef unsigned short  sa_family_t;
typedef unsigned        socklen_t;

struct in_addr {
        in_addr_t s_addr;
};

struct sockaddr {
        sa_family_t sa_family;
        char sa_data[14];
};

struct sockaddr_in {
        sa_family_t sin_family;
        in_port_t sin_port;
        struct in_addr sin_addr;
        uint8_t sin_zero[8];
};

__attribute__((const)) int *__errno_location(void);
#define errno (*__errno_location())

int accept(int, struct sockaddr *__restrict, socklen_t *__restrict);
int bind(int, const struct sockaddr *, socklen_t);
int close(int);
int connect(int, const struct sockaddr *, socklen_t);
void free(void *);
struct tm *gmtime(const time_t *);
uint16_t htons(uint16_t);
int inet_pton(int, const char *__restrict, void *__restrict);
int listen(int, int);
void *malloc(size_t);
void *memalign(size_t, size_t);
void *memcpy(void *__restrict, const void *__restrict, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
void *memchr(const void *, int, size_t);
int mkdir(const char *, mode_t);
int mknod(const char *, mode_t, dev_t);
int open(const char *, int, ...);
int puts(const char *);
int printf(const char *__restrict, ...);
ssize_t read(int, void *, size_t);
void *realloc(void *, size_t);
ssize_t recv(int, void *, size_t, int);
ssize_t send(int, const void *, size_t, int);
int socket(int, int, int);
int strcmp(const char *, const char *);
char *strcpy(char *__restrict, const char *__restrict);
int strncmp(const char *, const char *, size_t);
char *strncpy(char *__restrict, const char *__restrict, size_t);
size_t strftime(char *__restrict, size_t, const char *__restrict, const struct tm *__restrict);
size_t strlen(const char *);
ssize_t write(int, const void *, size_t);

/* openssl */

typedef struct bignum_st BIGNUM;
typedef struct rsa_st RSA;

BIGNUM *BN_new(void);
RSA *RSA_new(void);
