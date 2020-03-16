// Komodo test enclave
// https://github.com/Microsoft/Komodo/blob/master/driver/driver.c

        .text
        .arch   armv6t2
test_enclave:
        mrc     p15, 0, r9, c9, c13, 0              // grab cycles for later
        cmp     r0, #0
        beq     9f
        cmp     r0, #1
        beq     2f
        cmp     r0, #2
        beq     3f
        cmp     r0, #3
        beq     4f
        cmp     r0, #4
        beq     5f

        // straight exit
     9: mov     r1, r9                              // cycle count
     1: mov     r0, #0                              // KOM_SVC_EXIT
        svc     #0
        b       1b

        // enter/resume tests: exec until interrupted
     2: mov     r2, r9
        mrc     p15, 0, r9, c9, c13, 0              // while (1) {
        sub     r3, r9, r2                          // delta = rdcycles() - oldcycles;
        cmp     r3, #200                            // if (delta > 200) break;
        bgt     9b
        b       2b

        // attest test
     3: mov     r0, #1                              // KOM_SVC_ATTEST
        mrc     p15, 0, r9, c9, c13, 0              // r9 = start
        svc     #0
        mrc     p15, 0, r10, c9, c13, 0             // r10 = end
        sub     r1, r10, r9                         // retval = end - start
        b       1b                                  // exit

        // verify test
     4: mov     r0, #2                              // KOM_SVC_VERIFY_STEP0
        mrc     p15, 0, r9, c9, c13, 0              // r9 = start
        svc     #0
        mov     r0, #3                              // KOM_SVC_VERIFY_STEP1
        svc     #0
        mov     r0, #4                              // KOM_SVC_VERIFY_STEP2
        svc     #0
        mrc     p15, 0, r10, c9, c13, 0             // r10 = end
        sub     r1, r10, r9                         // retval = end - start
        b       1b                                  // exit

        // map_data test
     5: mov     r0, #10                             // KOM_SVC_MAP_DATA
        // r1 = pageno, r2 = mapping
        mov     r11, r1                             // save pageno (from SVC args) for later
        movw    r2, #0xd003                         // RW page at 0xd000
        mrc     p15, 0, r9, c9, c13, 0              // r9 = start
        svc     #0
        mrc     p15, 0, r10, c9, c13, 0             // r10 = end
        cmp     r0, #0                              // bail on failure
        bne     6f
        mov     r0, #11                             // KOM_SVC_UNMAP_DATA
        mov     r1, r11                             // pageno
        movw    r2, #0xd003                         // map VA
        svc     #0
        cmp     r0, #0                              // bail on failure
        bne     7f
        sub     r1, r10, r9                         // retval = end - start
        b       1b                                  // exit
     6: mov     r1, r0                              // fail case 1
        b       1b
     7: add     r1, r0, #30                         // fail case 2
        b       1b
