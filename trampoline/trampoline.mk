
TRAMPOLINE_ELF  := $(O)/trampoline/trampoline.elf
TRAMPOLINE_BIN  := $(basename $(TRAMPOLINE_ELF)).bin
TRAMPOLINE_LDS  := $(O)/trampoline/trampoline.lds
TRAMPOLINE_SRCS := trampoline/head.S
TRAMPOLINE_OBJS := $(call object,$(TRAMPOLINE_SRCS))

$(TRAMPOLINE_ELF): $(TRAMPOLINE_LDS) $(TRAMPOLINE_OBJS)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $(TRAMPOLINE_LDS) $(TRAMPOLINE_OBJS)
