/*
 * Copyright (C) 2011-2018 Intel Corporation. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in
 *     the documentation and/or other materials provided with the
 *     distribution.
 *   * Neither the name of Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef _SE_ARCH_H_
#define _SE_ARCH_H_

#include "inst.h"
#include "se_types.h"
#include "sgx_attributes.h"
#include "sgx_key.h"
#include "sgx_report.h"
#include "sgx_tcrypto.h"

#define SE_PAGE_SIZE 0x1000
#define TCS_SIZE SE_PAGE_SIZE

#pragma pack(push, 1)

#define STATIC_ASSERT_UNUSED_ATTRIBUTE __attribute__((unused))
#define _ASSERT_CONCAT(a, b) a##b
#define ASSERT_CONCAT(a, b) _ASSERT_CONCAT(a, b)
#define se_static_assert(e) typedef char ASSERT_CONCAT(assert_line, __LINE__)[(e)?1:-1] STATIC_ASSERT_UNUSED_ATTRIBUTE

se_static_assert(sizeof(sgx_key_request_t) == 512);
se_static_assert(sizeof(sgx_target_info_t) == 512);

/****************************************************************************
 * Definitions for SSA
 ****************************************************************************/
typedef struct _exit_info_t
{
    uint32_t    vector:8;                /* Exception number of exceptions reported inside enclave */
    uint32_t    exit_type:3;             /* 3: Hardware exceptions, 6: Software exceptions */
    uint32_t    reserved:20;
    uint32_t    valid:1;                 /* 0: unsupported exceptions, 1: Supported exceptions */
} exit_info_t;

#define SE_VECTOR_DE    0
#define SE_VECTOR_DB    1
#define SE_VECTOR_BP    3
#define SE_VECTOR_BR    5
#define SE_VECTOR_UD    6
#define SE_VECTOR_MF    16
#define SE_VECTOR_AC    17
#define SE_VECTOR_XM    19

typedef struct _ssa_gpr_t
{
    REGISTER(   ax);                    /* (0) */
    REGISTER(   cx);                    /* (8) */
    REGISTER(   dx);                    /* (16) */
    REGISTER(   bx);                    /* (24) */
    REGISTER(   sp);                    /* (32) */
    REGISTER(   bp);                    /* (40) */
    REGISTER(   si);                    /* (48) */
    REGISTER(   di);                    /* (56) */
    uint64_t    r8;                     /* (64) */
    uint64_t    r9;                     /* (72) */
    uint64_t    r10;                    /* (80) */
    uint64_t    r11;                    /* (88) */
    uint64_t    r12;                    /* (96) */
    uint64_t    r13;                    /* (104) */
    uint64_t    r14;                    /* (112) */
    uint64_t    r15;                    /* (120) */
    REGISTER(flags);                 /* (128) */
    REGISTER(   ip);                 /* (136) */
    REGISTER( sp_u);                 /* (144) untrusted stack pointer. saved by EENTER */
    REGISTER( bp_u);                 /* (152) untrusted frame pointer. saved by EENTER */
    exit_info_t exit_info;              /* (160) contain information for exits */
    uint32_t    reserved;               /* (164) padding to multiple of 8 bytes */
    uint64_t    fs;                     /* (168) FS register */
    uint64_t    gs;                     /* (176) GS register */
} ssa_gpr_t;

typedef uint64_t si_flags_t;

#define SI_FLAG_NONE                0x0
#define SI_FLAG_R                   0x1             /* Read Access */
#define SI_FLAG_W                   0x2             /* Write Access */
#define SI_FLAG_X                   0x4             /* Execute Access */
#define SI_FLAG_PT_LOW_BIT          0x8                             /* PT low bit */
#define SI_FLAG_PT_MASK             (0xFF<<SI_FLAG_PT_LOW_BIT)      /* Page Type Mask [15:8] */
#define SI_FLAG_SECS                (0x00<<SI_FLAG_PT_LOW_BIT)      /* SECS */
#define SI_FLAG_TCS                 (0x01<<SI_FLAG_PT_LOW_BIT)      /* TCS */
#define SI_FLAG_REG                 (0x02<<SI_FLAG_PT_LOW_BIT)      /* Regular Page */
#define SI_FLAG_TRIM                (0x04<<SI_FLAG_PT_LOW_BIT)      /* Trim Page */
#define SI_FLAG_PENDING             0x8
#define SI_FLAG_MODIFIED            0x10
#define SI_FLAG_PR                  0x20

#define SI_FLAGS_EXTERNAL           (SI_FLAG_PT_MASK | SI_FLAG_R | SI_FLAG_W | SI_FLAG_X)   /* Flags visible/usable by instructions */
#define SI_FLAGS_R                  (SI_FLAG_R|SI_FLAG_REG)
#define SI_FLAGS_RW                 (SI_FLAG_R|SI_FLAG_W|SI_FLAG_REG)
#define SI_FLAGS_RX                 (SI_FLAG_R|SI_FLAG_X|SI_FLAG_REG)
#define SI_FLAGS_TCS                (SI_FLAG_TCS)
#define SI_FLAGS_SECS               (SI_FLAG_SECS)
#define SI_MASK_TCS                 (SI_FLAG_PT_MASK)
#define SI_MASK_MEM_ATTRIBUTE       (0x7)


typedef struct _sec_info_t
{
   si_flags_t        flags;
   uint64_t          reserved[7];
} sec_info_t;

typedef struct _page_info_t
{
    PADDED_POINTER(void,        lin_addr);      /* Enclave linear address */
    PADDED_POINTER(void,        src_page);      /* Linear address of the page where contents are located */
    PADDED_POINTER(sec_info_t,  sec_info);      /* Linear address of the SEC_INFO structure for the page */
    PADDED_POINTER(void,        secs);          /* Linear address of EPC slot that contains SECS for this enclave */
} page_info_t;

/****************************************************************************
* Definitions for enclave signature
****************************************************************************/
#define SE_KEY_SIZE         384         /* in bytes */
#define SE_EXPONENT_SIZE    4           /* RSA public key exponent size in bytes */


typedef struct _css_header_t {        /* 128 bytes */
    uint8_t  header[12];                /* (0) must be (06000000E100000000000100H) */
    uint32_t type;                      /* (12) bit 31: 0 = prod, 1 = debug; Bit 30-0: Must be zero */
    uint32_t module_vendor;             /* (16) Intel=0x8086, ISV=0x0000 */
    uint32_t date;                      /* (20) build date as yyyymmdd */
    uint8_t  header2[16];               /* (24) must be (01010000600000006000000001000000H) */
    uint32_t hw_version;                /* (40) For Launch Enclaves: HWVERSION != 0. Others, HWVERSION = 0 */
    uint8_t  reserved[84];              /* (44) Must be 0 */
} css_header_t;
se_static_assert(sizeof(css_header_t) == 128);

typedef struct _css_key_t {           /* 772 bytes */
    uint8_t modulus[SE_KEY_SIZE];       /* (128) Module Public Key (keylength=3072 bits) */
    uint8_t exponent[SE_EXPONENT_SIZE]; /* (512) RSA Exponent = 3 */
    uint8_t signature[SE_KEY_SIZE];     /* (516) Signature over Header and Body */
} css_key_t;
se_static_assert(sizeof(css_key_t) == 772);

typedef struct _css_body_t {            /* 128 bytes */
    sgx_misc_select_t   misc_select;    /* (900) The MISCSELECT that must be set */
    sgx_misc_select_t   misc_mask;      /* (904) Mask of MISCSELECT to enforce */
    uint8_t             reserved[20];   /* (908) Reserved. Must be 0. */
    sgx_attributes_t    attributes;     /* (928) Enclave Attributes that must be set */
    sgx_attributes_t    attribute_mask; /* (944) Mask of Attributes to Enforce */
    sgx_measurement_t   enclave_hash;   /* (960) MRENCLAVE - (32 bytes) */
    uint8_t             reserved2[32];  /* (992) Must be 0 */
    uint16_t            isv_prod_id;    /* (1024) ISV assigned Product ID */
    uint16_t            isv_svn;        /* (1026) ISV assigned SVN */
} css_body_t;
se_static_assert(sizeof(css_body_t) == 128);

typedef struct _css_buffer_t {         /* 780 bytes */
    uint8_t  reserved[12];              /* (1028) Must be 0 */
    uint8_t  q1[SE_KEY_SIZE];           /* (1040) Q1 value for RSA Signature Verification */
    uint8_t  q2[SE_KEY_SIZE];           /* (1424) Q2 value for RSA Signature Verification */
} css_buffer_t;
se_static_assert(sizeof(css_buffer_t) == 780);

typedef struct _enclave_css_t {        /* 1808 bytes */
    css_header_t    header;             /* (0) */
    css_key_t       key;                /* (128) */
    css_body_t      body;               /* (900) */
    css_buffer_t    buffer;             /* (1028) */
} enclave_css_t;

se_static_assert(sizeof(enclave_css_t) == 1808);

/****************************************************************************
* Definitions for launch token
****************************************************************************/
typedef struct _launch_body_t
{
   uint32_t              valid;            /* (  0) 0 = Invalid, 1 = Valid */
   uint32_t              reserved1[11];    /* (  4) must be zero */
   sgx_attributes_t      attributes;       /* ( 48) ATTRIBUTES of Enclave */
   sgx_measurement_t     mr_enclave;       /* ( 64) MRENCLAVE of Enclave */
   uint8_t               reserved2[32];    /* ( 96) */
   sgx_measurement_t     mr_signer;        /* (128) MRSIGNER of Enclave */
   uint8_t               reserved3[32];    /* (160) */
} launch_body_t;
se_static_assert(sizeof(launch_body_t) == 192);

typedef struct _launch_t {
  launch_body_t         body;
  sgx_cpu_svn_t          cpu_svn_le;       /* (192) Launch Enclave's CPUSVN */
  uint16_t               isv_prod_id_le;   /* (208) Launch Enclave's ISVPRODID */
  uint16_t               isv_svn_le;       /* (210) Launch Enclave's ISVSVN */
  uint8_t                reserved2[24];    /* (212) Must be 0 */
  sgx_misc_select_t      masked_misc_select_le; /* (236) */
  sgx_attributes_t       attributes_le;    /* (240) ATTRIBUTES of Launch Enclave */
  sgx_key_id_t           key_id;           /* (256) Value for key wear-out protection */
  sgx_mac_t              mac;              /* (288) CMAC using Launch Token Key */
} token_t;
se_static_assert(sizeof(token_t) == 304);

typedef struct _wl_cert_t                           /* All fields except the mr_signer_list fields, are big-endian integer format */
{
    uint16_t                version;                /* ( 0) White List Cert format version. Currently, only valid version is 1 */
    uint16_t                cert_type;              /* ( 2) White List Cert Type. For Enclave Signing Key White List Cert, must be 1 */
    uint16_t                provider_id;            /* ( 4) Enclave Signing Key White List Provider ID to identify the key used to sign this Enclave signing Key White List Certificate. Currently, only one White List Provider is approved: WLProviderID-ISecG = 0 */
    uint16_t                le_prod_id;             /* ( 6) Launch Enclave ProdID the White List Cert applies to. Linux LE-ProdID = 0x20 */
    uint32_t                wl_version;             /* ( 8) Version of the Enclave Signing Key White List. For a specific LE-ProdID, should increase on every WL Cert signing request */
    uint32_t                entry_number;           /* (12) Number of MRSIGNER entries in the Cert. If the White List Certificate allows enclave signed by any key to launch, the White List Cert must only contain one all-0 MRSIGNER entry. */
    sgx_measurement_t       mr_signer_list[];       /* (16) White Listed Enclave Signing Key entry 0 - SHA256 Hash of the little-endian format RSA-3072 Enclave Signing Key modulus. If the White List Cert allows enclave signed by any key to launch, this field must be all 0s */
}wl_cert_t;
typedef struct _wl_provider_cert_t                  /* All fields are big endian */
{
    uint16_t                version;                /* ( 0) White List Cert format version. Currently, only valid version is 1 */
    uint16_t                cert_type;              /* ( 2) White List Cert Type, For Enclave Signing Key White List Signer Cert, must be 0 */
    uint16_t                provider_id;            /* ( 4) Enclave Signing Key White List Signer ID assigned by the White List Root CA. Currently, only one White List Provider is approved: WLProviderID-ISecG = 0 */
    uint16_t                root_id;                /* ( 6) Identify the White List Root CA key used to sign the Cert. Currently, only one WLRootID is valid: WLRootID-iKGF-Key-0 = 0 */
    sgx_ec256_public_t      pub_key;                /* ( 8) ECDSA public key of the Enclave Signing Key White List Provider identified by WLProviderID */
    sgx_ec256_signature_t   signature;              /* (72) ECDSA Signature by WL Root CA identified by WLRootID */
}wl_provider_cert_t;
se_static_assert(sizeof(wl_provider_cert_t) == 136);
typedef struct _wl_cert_chain_t
{
    wl_provider_cert_t      wl_provider_cert;
    wl_cert_t               wl_cert;
}wl_cert_chain_t;
#pragma pack(pop)

#endif/*_SE_ARCH_H_*/