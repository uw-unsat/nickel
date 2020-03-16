RISCVEMU        := pkg/riscvemu

RISCVEMU_SRCS   := \
        $(RISCVEMU)/virtio.c \
        $(RISCVEMU)/pci.c \
        $(RISCVEMU)/fs.c \
        $(RISCVEMU)/cutils.c \
        $(RISCVEMU)/iomem.c \
        $(RISCVEMU)/simplefb.c \
        $(RISCVEMU)/json.c \
        $(RISCVEMU)/machine.c \
        $(RISCVEMU)/fs_disk.c \
        $(RISCVEMU)/riscvemu.c \
        $(RISCVEMU)/riscv_machine.c \
        $(RISCVEMU)/softfp.c \

RISCVEMU_OBJS    := $(call object,$(RISCVEMU_SRCS))

$(O)/$(RISCVEMU)/%.o: CFLAGS := $(USER_CFLAGS) -DCONFIG_VERSION=\"$(shell cat $(RISCVEMU)/VERSION)\" -w

$(O)/$(RISCVEMU)/riscv_cpu64.o: $(RISCVEMU)/riscv_cpu.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(USER_CFLAGS) -DMAX_XLEN=64 -w $<

$(O)/$(RISCVEMU)/riscvemu64: $(O)/$(RISCVEMU)/riscv_cpu64.o $(RISCVEMU_OBJS) $(USER_LDLIBS) $(O)/$(COMPILER_RT)/libcompiler_rt.a
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
