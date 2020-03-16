NIKOS2_INITRD        := $(O)/nikos2/user/initrd.cpio

NIKOS2_USER_BINS     := \
        $(O)/nikos2/user/idle \
        $(O)/nikos2/user/alice \
        $(O)/nikos2/user/bob \
        $(O)/nikos2/user/hacker \

NIKOS2_USER_LIBS     := \
        $(O)/nikos2/user/crt0.o \
        $(O)/nikos2/user/printf.o \
        $(O)/nikos2/user/string.o \
        $(O)/nikos2/user/syscall.o \

$(NIKOS2_INITRD): $(NIKOS2_USER_BINS)
	$(Q)cd $(@D) && find $(^:$(@D)/%=%) | cpio -o -H newc --quiet > $(@F)~
	$(QUIET_GEN)mv $@~ $@

$(O)/nikos2/user/%: $(O)/nikos2/user/%.o $(NIKOS2_USER_LIBS)
	$(QUIET_LD)$(LD) -o $@ -static $(LDFLAGS) $^

$(O)/nikos2/user/%.o: CFLAGS := $(USER_CFLAGS) -mno-mmx -mno-sse -fno-PIC

$(O)/nikos2/user/asm-offsets.S: CFLAGS := $(USER_CFLAGS)
