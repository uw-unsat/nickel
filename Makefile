include config.mk

include scripts/Makefile.lib

BASE_CFLAGS     += -ffreestanding
BASE_CFLAGS     += -fno-omit-frame-pointer
BASE_CFLAGS     += -fno-stack-protector
BASE_CFLAGS     += -fno-strict-aliasing
BASE_CFLAGS     += -ffunction-sections -fdata-sections
BASE_CFLAGS     += -g
BASE_CFLAGS     += -Wall -MD -MP
ifeq ($(USE_CLANG),1)
BASE_CFLAGS     += -Wno-initializer-overrides
endif

CFLAGS          += $(BASE_CFLAGS)
CFLAGS          += -fno-PIE
CFLAGS          += -fwrapv
CFLAGS          += -mno-red-zone
CFLAGS          += -mno-sse -mno-mmx -mno-sse2 -mno-3dnow -mno-avx
CFLAGS          += -I include
CFLAGS          += -DNR_CPUS=$(NR_CPUS)

USER_CFLAGS     += $(BASE_CFLAGS)
USER_CFLAGS     += -fPIC
USER_CFLAGS     += -fwrapv
USER_CFLAGS     += -nostdinc -I include/uapi

USER_CRT_OBJS   := \
        $(O)/nistar/user/lib/crt1.o \
        $(O)/nistar/user/lib/crti.o \
        $(O)/nistar/user/lib/crtn.o \

USER_LDLIBS     := \
        $(USER_CRT_OBJS) \
        $(O)/nistar/user/lib/libc.a \

LDFLAGS         += -nostdlib --gc-sections

include coq/coq.mk
include boot/boot.mk
include pkg/pkg.mk
include trampoline/trampoline.mk
include kernel/kernel.mk
include nikos/nikos.mk
include nikos2/nikos2.mk
include nistar/nistar.mk
include irpy/irpy.mk
include examples/examples.mk
include tests/tests.mk
include host/host.mk
include sk/sk.mk

all: $(ALL)

.DEFAULT_GOAL = all

# force the static pattern rule
ASM_OFFSETS := $(call rwildcard,./,*asm-offsets.h)

$(ASM_OFFSETS): %/asm-offsets.h: $(O)/%/asm-offsets.S
	$(QUIET_GEN)$(call gen-offsets) < $< > $@~
	$(Q)mv $@~ $@

$(O)/%/asm-offsets.S: %/asm-offsets.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -S $(CFLAGS) $<

%.bin: %.elf
	$(QUIET_GEN)$(OBJCOPY) -O binary $< $@
	$(Q)$(OBJDUMP) -S $< > $(basename $@).asm

$(O)/%.lds: %.lds.S
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_GEN)$(CPP) -o $@ -P $(CFLAGS) $<

$(O)/%.o: %.s
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(CFLAGS) $<

$(O)/%.o: %.S
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(CFLAGS) $<

$(O)/%.o: %.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(CFLAGS) -DCONFIG_SAFE_TYPE -D__MODULE__='"$(basename $(notdir $<))"' $<

$(O)/%.ll: %.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(LLVM_CC) -o $@ -S -emit-llvm -O2 $(CFLAGS) -D__IRPY__ -D__MODULE__='"$(basename $(notdir $<))"' $<

clean:
ifeq ($(GIT_CLEAN),1)
	git clean -e '!/local.mk' -e '!/.vscode/' -e '!/.gdbinit' -e '!/solver.toml' -Xdf
else
	-rm -rf $(O)
	-find . -type d -name '__pycache__' -or -name '*.pyc' -print -exec rm -rf '{}' '+'
endif

VMM_ISO         := $(basename $(VMM)).iso
KERNEL_ISO      := $(basename $(KERNEL)).iso

bochs: $(VMM_ISO)
	$(Q)$(MAKE) bochs-vmm

bochs-vmm: $(VMM_ISO)
	$(call run-bochs)

bochs-kernel: $(KERNEL_ISO)
	$(call run-bochs)

$(VMM_ISO): $(VMM) $(KERNEL) $(INITRD)
	$(Q)-rm -rf $(@D)/iso
	$(Q)$(MKDIR_P) $(@D)/iso/
	$(Q)$(LN_S) $(realpath $(VMM)) $(@D)/iso/
	$(Q)echo 'default mboot.c32 /$(notdir $(VMM)) --- /$(notdir $(KERNEL))$(if $(APPEND), $(APPEND))$(if $(INITRD), --- /$(notdir $(INITRD)))' > $(@D)/iso/isolinux.cfg
	$(QUIET_GEN)$(call gen-iso)

$(KERNEL_ISO): $(KERNEL)
	$(Q)-rm -rf $(@D)/iso
	$(Q)$(MKDIR_P) $(@D)/iso/
	$(Q)echo 'default mboot.c32 /$(notdir $(KERNEL))$(if $(APPEND), $(APPEND))$(if $(INITRD), --- /$(notdir $(INITRD)))' > $(@D)/iso/isolinux.cfg
	$(QUIET_GEN)$(call gen-iso)

QEMUOPTS += -machine q35,accel=$(QEMU_ACCEL)
QEMUOPTS += -cpu $(QEMU_CPU)
QEMUOPTS += -smp cpus=$(NR_CPUS)
QEMUOPTS += -m 2G
QEMUOPTS += -device isa-debug-exit
QEMUOPTS += -debugcon file:/dev/stdout
QEMUOPTS += -serial mon:stdio
QEMUOPTS += -display none
QEMUOPTS += -device $(QEMU_IOMMU)
QEMUOPTS += -netdev user,id=net0,hostfwd=tcp::10080-:80
QEMUOPTS += -device $(QEMU_NIC),netdev=net0
QEMUOPTS += -object filter-dump,id=filter0,netdev=net0,file=$(O)/qemu.pcap
# the bottled QEMU from Homebrew doesn't support -fsdev and
# we won't need this on macOS anyway
ifeq ($(QEMU_USE_VIRTIO),1)
QEMUOPTS += -fsdev local,id=fsdev0,path=$(PWD),security_model=passthrough,readonly
QEMUOPTS += -device virtio-9p-pci,fsdev=fsdev0,mount_tag=fs0
endif
#QEMUOPTS += -s -S

qemu:
	$(Q)$(MAKE) qemu-vmm

qemu-vmm: $(VMM) $(KERNEL) $(INITRD)
ifneq ($(UNAME_S),Linux)
	$(error works on Linux only)
else
	$(QEMU) $(QEMUOPTS) -kernel $(VMM) -initrd "$(KERNEL)$(if $(APPEND), $(APPEND)),$(if $(INITRD),$(INITRD),/dev/null)" || true
endif

kernel: $(KERNEL) $(INITRD)

qemu-kernel: $(KERNEL) $(INITRD)
	$(QEMU) $(QEMUOPTS) -kernel $(KERNEL)$(if $(APPEND), -append $(APPEND))$(if $(INITRD), -initrd $(INITRD)) || true

-include $(call rwildcard,./,*.d)

PRECIOUS += $(O)/%.o $(O)/%/asm-offsets.S

PHONY += all clean check bochs bochs-kernel qemu qemu-kernel host kernel $(VMM_ISO) $(KERNEL_ISO)

.PHONY: $(PHONY)

.PRECIOUS: $(PRECIOUS)
