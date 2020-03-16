#include <stdio.h>
#include <iostream>
#include "Enclave_u.h"
#include "sgx_urts.h"

#define ENCLAVE_NAME "enclave.signed.so"

sgx_enclave_id_t global_eid = 0;
sgx_launch_token_t token = {0};

void ocall_print(const char* str) {
    printf("%s\n", str);
}

int main(int argc, char const *argv[]) {
    int launch_token_updated;

    sgx_create_enclave(ENCLAVE_NAME, SGX_DEBUG_FLAG, &token, &launch_token_updated, &global_eid, NULL);

    // run enclave
    int ret;

    ecall_helloworld(global_eid, &ret);
    printf("return value: %d\n", ret);
    
    return 0;
}
