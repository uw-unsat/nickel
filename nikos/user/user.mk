NIKOS_INITRD        := $(O)/nikos/user/initrd.cpio

NIKOS_USER_BINS     := \
        $(O)/nikos/user/idle \
        $(O)/nikos/user/alice \
        $(O)/nikos/user/bob \
        $(O)/nikos/user/hacker \

NIKOS_USER_LIBS     := \
        $(O)/nikos/user/crt0.o \
        $(O)/nikos/user/printf.o \
        $(O)/nikos/user/string.o \
        $(O)/nikos/user/syscall.o \

$(NIKOS_INITRD): $(NIKOS_USER_BINS)
	$(Q)cd $(@D) && find $(^:$(@D)/%=%) | cpio -o -H newc --quiet > $(@F)~
	$(QUIET_GEN)mv $@~ $@

$(O)/nikos/user/%: $(O)/nikos/user/%.o $(NIKOS_USER_LIBS)
	$(QUIET_LD)$(LD) -o $@ -static $(LDFLAGS) $^

$(O)/nikos/user/%.o: CFLAGS := $(USER_CFLAGS) -mno-mmx -mno-sse -fno-PIC

$(O)/nikos/user/asm-offsets.S: CFLAGS := $(USER_CFLAGS)
