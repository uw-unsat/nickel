#pragma once

#include <sys/types.h>

/* setup_data types */
#define SETUP_NONE                      0
#define SETUP_E820_EXT                  1
#define SETUP_DTB                       2
#define SETUP_PCI                       3
#define SETUP_EFI                       4
#define SETUP_APPLE_PROPERTIES          5

/* ram_size flags */
#define RAMDISK_IMAGE_START_MASK        0x07FF
#define RAMDISK_PROMPT_FLAG             0x8000
#define RAMDISK_LOAD_FLAG               0x4000

/* loadflags */
#define LOADED_HIGH                     (1<<0)
#define KASLR_FLAG                      (1<<1)
#define QUIET_FLAG                      (1<<5)
#define KEEP_SEGMENTS                   (1<<6)
#define CAN_USE_HEAP                    (1<<7)

/* xloadflags */
#define XLF_KERNEL_64                   (1<<0)
#define XLF_CAN_BE_LOADED_ABOVE_4G      (1<<1)
#define XLF_EFI_HANDOVER_32             (1<<2)
#define XLF_EFI_HANDOVER_64             (1<<3)
#define XLF_EFI_KEXEC                   (1<<4)

#ifndef __ASSEMBLER__

#include <sys/types.h>

/* extensible setup data list node */
struct setup_data {
        uint64_t next;
        uint32_t type;
        uint32_t len;
        uint8_t data[0];
};

struct setup_header {
        uint8_t  setup_sects;
        uint16_t root_flags;
        uint32_t syssize;
        uint16_t ram_size;
        uint16_t vid_mode;
        uint16_t root_dev;
        uint16_t boot_flag;
        uint16_t jump;
        uint32_t header;
        uint16_t version;
        uint32_t realmode_swtch;
        uint16_t start_sys_seg;
        uint16_t kernel_version;
        uint8_t  type_of_loader;
        uint8_t  loadflags;
        uint16_t setup_move_size;
        uint32_t code32_start;
        uint32_t ramdisk_image;
        uint32_t ramdisk_size;
        uint32_t bootsect_kludge;
        uint16_t heap_end_ptr;
        uint8_t  ext_loader_ver;
        uint8_t  ext_loader_type;
        uint32_t cmd_line_ptr;
        uint32_t initrd_addr_max;
        uint32_t kernel_alignment;
        uint8_t  relocatable_kernel;
        uint8_t  min_alignment;
        uint16_t xloadflags;
        uint32_t cmdline_size;
        uint32_t hardware_subarch;
        uint64_t hardware_subarch_data;
        uint32_t payload_offset;
        uint32_t payload_length;
        uint64_t setup_data;
        uint64_t pref_address;
        uint32_t init_size;
        uint32_t handover_offset;
} __packed;

struct sys_desc_table {
        uint16_t length;
        uint8_t  table[14];
};

/* Gleaned from OFW's set-parameters in cpu/x86/pc/linux.fth */
struct olpc_ofw_header {
        uint32_t ofw_magic;     /* OFW signature */
        uint32_t ofw_version;
        uint32_t cif_handler;   /* callback into OFW */
        uint32_t irq_desc_table;
} __packed;

struct efi_info {
        uint32_t efi_loader_signature;
        uint32_t efi_systab;
        uint32_t efi_memdesc_size;
        uint32_t efi_memdesc_version;
        uint32_t efi_memmap;
        uint32_t efi_memmap_size;
        uint32_t efi_systab_hi;
        uint32_t efi_memmap_hi;
};

/*
 * This is the maximum number of entries in struct boot_params::e820_table
 * (the zeropage), which is part of the x86 boot protocol ABI:
 */
#define E820_MAX_ENTRIES_ZEROPAGE       128

#define EDDMAXNR                        6
#define EDD_MBR_SIG_MAX                 16

/*
 * The E820 memory region entry of the boot protocol ABI:
 */
struct boot_e820_entry {
        uint64_t addr;
        uint64_t size;
        uint32_t type;
} __packed;

struct screen_info { uint8_t data[64]; } __packed;
struct apm_bios_info { uint8_t data[20]; } __packed;
struct ist_info { uint8_t data[16]; } __packed;
struct edid_info { uint8_t data[128]; } __packed;
struct edd_info { uint8_t data[82]; } __packed;

/* The so-called "zeropage" */
struct boot_params {
        struct screen_info screen_info;                 /* 0x000 */
        struct apm_bios_info apm_bios_info;             /* 0x040 */
        uint8_t  _pad2[4];                              /* 0x054 */
        uint64_t  tboot_addr;                           /* 0x058 */
        struct ist_info ist_info;                       /* 0x060 */
        uint8_t  _pad3[16];                             /* 0x070 */
        uint8_t  hd0_info[16];  /* obsolete! */         /* 0x080 */
        uint8_t  hd1_info[16];  /* obsolete! */         /* 0x090 */
        struct sys_desc_table sys_desc_table; /* obsolete! */   /* 0x0a0 */
        struct olpc_ofw_header olpc_ofw_header;         /* 0x0b0 */
        uint32_t ext_ramdisk_image;                     /* 0x0c0 */
        uint32_t ext_ramdisk_size;                      /* 0x0c4 */
        uint32_t ext_cmd_line_ptr;                      /* 0x0c8 */
        uint8_t  _pad4[116];                            /* 0x0cc */
        struct edid_info edid_info;                     /* 0x140 */
        struct efi_info efi_info;                       /* 0x1c0 */
        uint32_t alt_mem_k;                             /* 0x1e0 */
        uint32_t scratch;       /* Scratch field! */    /* 0x1e4 */
        uint8_t  e820_entries;                          /* 0x1e8 */
        uint8_t  eddbuf_entries;                        /* 0x1e9 */
        uint8_t  edd_mbr_sig_buf_entries;               /* 0x1ea */
        uint8_t  kbd_status;                            /* 0x1eb */
        uint8_t  secure_boot;                           /* 0x1ec */
        uint8_t  _pad5[2];                              /* 0x1ed */
        /*
         * The sentinel is set to a nonzero value (0xff) in header.S.
         *
         * A bootloader is supposed to only take setup_header and put
         * it into a clean boot_params buffer. If it turns out that
         * it is clumsy or too generous with the buffer, it most
         * probably will pick up the sentinel variable too. The fact
         * that this variable then is still 0xff will let kernel
         * know that some variables in boot_params are invalid and
         * kernel should zero out certain portions of boot_params.
         */
        uint8_t  sentinel;                              /* 0x1ef */
        uint8_t  _pad6[1];                              /* 0x1f0 */
        struct setup_header hdr; /* setup header */     /* 0x1f1 */
        uint8_t  _pad7[0x290-0x1f1-sizeof(struct setup_header)];
        uint32_t edd_mbr_sig_buffer[EDD_MBR_SIG_MAX];   /* 0x290 */
        struct boot_e820_entry e820_table[E820_MAX_ENTRIES_ZEROPAGE]; /* 0x2d0 */
        uint8_t  _pad8[48];                             /* 0xcd0 */
        struct edd_info eddbuf[EDDMAXNR];               /* 0xd00 */
        uint8_t  _pad9[276];                            /* 0xeec */
} __packed;

#endif  /* !__ASSEMBLER__ */
