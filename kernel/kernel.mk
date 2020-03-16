KERNEL_LDS      := $(O)/kernel/kernel.lds

KERNEL_SRCS     := \
	$(call rwildcard,kernel/,*.c) \
	$(call rwildcard,kernel/,*.S) \
        $(wildcard pkg/e1000/*.c) \

KERNEL_OBJS     := $(call object,$(KERNEL_SRCS))

HEAD_OBJS       := $(O)/boot/head.o

$(O)/kernel/trampoline.o: $(TRAMPOLINE_BIN)
$(O)/kernel/trampoline.o: CFLAGS += -I $(O)/trampoline

kernel/capflags.c: include/asm/cpufeatures.h
	$(Q)kernel/mkcapflags.sh $< | expand > $@~
	$(QUIET_GEN)mv $@~ $@

$(O)/kernel/e1000.o: CFLAGS += -I pkg/e1000
