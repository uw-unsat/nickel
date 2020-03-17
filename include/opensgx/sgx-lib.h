#pragma once

#include <opensgx/sgx-shared.h>

#define sgx_exit(ptr) {                         \
    asm volatile("movl %0, %%eax\n\t"           \
                 "movq %1, %%rbx\n\t"           \
                 ".byte 0x0F\n\t"               \
                 ".byte 0x01\n\t"               \
                 ".byte 0xd7\n\t"               \
                 :                              \
                 :"a"((uint32_t)ENCLU_EEXIT),   \
                  "b"((uint64_t)ptr));          \
}

#define sgx_report(tgtinfo, rptdata, output) {  \
    asm volatile("movl %0, %%eax\n\t"           \
                 "movq %1, %%rbx\n\t"           \
                 "movq %2, %%rcx\n\t"           \
                 "movq %3, %%rdx\n\t"           \
                 ".byte 0x0F\n\t"               \
                 ".byte 0x01\n\t"               \
                 ".byte 0xd7\n\t"               \
                 :                              \
                 :"a"((uint32_t)ENCLU_EREPORT), \
                  "b"((uint64_t)tgtinfo),       \
                  "c"((uint64_t)rptdata),       \
                  "d"((uint64_t)output));       \
}

#define sgx_getkey(keyreq, output) {            \
    asm volatile("movl %0, %%eax\n\t"           \
                 "movq %1, %%rbx\n\t"           \
                 "movq %2, %%rcx\n\t"           \
                 ".byte 0x0F\n\t"               \
                 ".byte 0x01\n\t"               \
                 ".byte 0xd7\n\t"               \
                 :                              \
                 :"a"((uint32_t)ENCLU_EGETKEY), \
                  "b"((uint64_t)keyreq),        \
                  "c"((uint64_t)output));       \
}

extern int sgx_enclave_read(void *buf, int len);
extern int sgx_enclave_write(void *buf, int len);

/* SIGSTRUCT parsing function */
extern sigstruct_t *sgx_load_sigstruct(char *conf);

/* Attestation supporting funcitons */
extern int sgx_make_server(int port);
extern int sgx_connect_server(const char *target_ip, int target_port);
extern int sgx_get_report(int fd, report_t *report);
extern int sgx_read_sock(int fd, void *buf, int len);
extern int sgx_write_sock(int fd, void *buf, int len);
extern int sgx_match_mac(unsigned char *report_key, report_t *report);
extern int sgx_make_quote(const char* pers, report_t *report, unsigned char *rsa_N, unsigned char *rsa_E);

/* Intra attestation supporting functions */
extern int sgx_intra_attest_challenger(int target_port, char *conf);
extern int sgx_intra_attest_target(int port);

/* Remote attestation supporing functions */
extern int sgx_remote_attest_challenger(const char *target_ip, int target_port, const char *challenge);
extern int sgx_remote_attest_target(int challenger_port, int quote_port, char *conf);
extern int sgx_remote_attest_quote(int target_port);
