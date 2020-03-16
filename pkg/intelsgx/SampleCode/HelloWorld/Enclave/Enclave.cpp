#include "Enclave_t.h"

int ecall_helloworld() {
    ocall_print("Hello world!\n");
    return 451;
}
