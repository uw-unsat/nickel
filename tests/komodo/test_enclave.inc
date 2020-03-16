        0xee199f1d, /*        0:        1d 9f 19 ee     mrc     p15, #0, r9, c9, c13, #0 */
        0xe3500000, /*        4:        00 00 50 e3     cmp     r0, #0 */
        0x0a000007, /*        8:        07 00 00 0a     beq     #28 <test_enclave+0x2C> */
        0xe3500001, /*        c:        01 00 50 e3     cmp     r0, #1 */
        0x0a000009, /*       10:        09 00 00 0a     beq     #36 <test_enclave+0x3C> */
        0xe3500002, /*       14:        02 00 50 e3     cmp     r0, #2 */
        0x0a00000d, /*       18:        0d 00 00 0a     beq     #52 <test_enclave+0x54> */
        0xe3500003, /*       1c:        03 00 50 e3     cmp     r0, #3 */
        0x0a000011, /*       20:        11 00 00 0a     beq     #68 <test_enclave+0x6C> */
        0xe3500004, /*       24:        04 00 50 e3     cmp     r0, #4 */
        0x0a000019, /*       28:        19 00 00 0a     beq     #100 <test_enclave+0x94> */
        0xe1a01009, /*       2c:        09 10 a0 e1     mov     r1, r9 */
        0xe3a00000, /*       30:        00 00 a0 e3     mov     r0, #0 */
        0xef000000, /*       34:        00 00 00 ef     svc     #0 */
        0xeafffffc, /*       38:        fc ff ff ea     b       #-16 <test_enclave+0x30> */
        0xe1a02009, /*       3c:        09 20 a0 e1     mov     r2, r9 */
        0xee199f1d, /*       40:        1d 9f 19 ee     mrc     p15, #0, r9, c9, c13, #0 */
        0xe0493002, /*       44:        02 30 49 e0     sub     r3, r9, r2 */
        0xe35300c8, /*       48:        c8 00 53 e3     cmp     r3, #200 */
        0xcafffff6, /*       4c:        f6 ff ff ca     bgt     #-40 <test_enclave+0x2C> */
        0xeafffff9, /*       50:        f9 ff ff ea     b       #-28 <test_enclave+0x3C> */
        0xe3a00001, /*       54:        01 00 a0 e3     mov     r0, #1 */
        0xee199f1d, /*       58:        1d 9f 19 ee     mrc     p15, #0, r9, c9, c13, #0 */
        0xef000000, /*       5c:        00 00 00 ef     svc     #0 */
        0xee19af1d, /*       60:        1d af 19 ee     mrc     p15, #0, r10, c9, c13, #0 */
        0xe04a1009, /*       64:        09 10 4a e0     sub     r1, r10, r9 */
        0xeafffff0, /*       68:        f0 ff ff ea     b       #-64 <test_enclave+0x30> */
        0xe3a00002, /*       6c:        02 00 a0 e3     mov     r0, #2 */
        0xee199f1d, /*       70:        1d 9f 19 ee     mrc     p15, #0, r9, c9, c13, #0 */
        0xef000000, /*       74:        00 00 00 ef     svc     #0 */
        0xe3a00003, /*       78:        03 00 a0 e3     mov     r0, #3 */
        0xef000000, /*       7c:        00 00 00 ef     svc     #0 */
        0xe3a00004, /*       80:        04 00 a0 e3     mov     r0, #4 */
        0xef000000, /*       84:        00 00 00 ef     svc     #0 */
        0xee19af1d, /*       88:        1d af 19 ee     mrc     p15, #0, r10, c9, c13, #0 */
        0xe04a1009, /*       8c:        09 10 4a e0     sub     r1, r10, r9 */
        0xeaffffe6, /*       90:        e6 ff ff ea     b       #-104 <test_enclave+0x30> */
        0xe3a0000a, /*       94:        0a 00 a0 e3     mov     r0, #10 */
        0xe1a0b001, /*       98:        01 b0 a0 e1     mov     r11, r1 */
        0xe30d2003, /*       9c:        03 20 0d e3     movw    r2, #53251 */
        0xee199f1d, /*       a0:        1d 9f 19 ee     mrc     p15, #0, r9, c9, c13, #0 */
        0xef000000, /*       a4:        00 00 00 ef     svc     #0 */
        0xee19af1d, /*       a8:        1d af 19 ee     mrc     p15, #0, r10, c9, c13, #0 */
        0xe3500000, /*       ac:        00 00 50 e3     cmp     r0, #0 */
        0x1a000007, /*       b0:        07 00 00 1a     bne     #28 <test_enclave+0xD4> */
        0xe3a0000b, /*       b4:        0b 00 a0 e3     mov     r0, #11 */
        0xe1a0100b, /*       b8:        0b 10 a0 e1     mov     r1, r11 */
        0xe30d2003, /*       bc:        03 20 0d e3     movw    r2, #53251 */
        0xef000000, /*       c0:        00 00 00 ef     svc     #0 */
        0xe3500000, /*       c4:        00 00 50 e3     cmp     r0, #0 */
        0x1a000003, /*       c8:        03 00 00 1a     bne     #12 <test_enclave+0xDC> */
        0xe04a1009, /*       cc:        09 10 4a e0     sub     r1, r10, r9 */
        0xeaffffd6, /*       d0:        d6 ff ff ea     b       #-168 <test_enclave+0x30> */
        0xe1a01000, /*       d4:        00 10 a0 e1     mov     r1, r0 */
        0xeaffffd4, /*       d8:        d4 ff ff ea     b       #-176 <test_enclave+0x30> */
        0xe280101e, /*       dc:        1e 10 80 e2     add     r1, r0, #30 */
        0xeaffffd2, /*       e0:        d2 ff ff ea     b       #-184 <test_enclave+0x30> */
