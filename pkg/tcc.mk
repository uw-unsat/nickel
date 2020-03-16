TCC             := pkg/tcc

TCC_SRCS        := \
        $(TCC)/libtcc.c \
        $(TCC)/tccpp.c \
        $(TCC)/tccgen.c \
        $(TCC)/tccelf.c \
        $(TCC)/tccasm.c \
        $(TCC)/tccrun.c \
        $(TCC)/x86_64-gen.c \
        $(TCC)/x86_64-link.c \
        $(TCC)/i386-asm.c \

TCC_OBJS        := $(call object,$(TCC_SRCS))

$(O)/$(TCC)/libtcc.a: $(TCC_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(TCC)/%.o: CFLAGS := $(USER_CFLAGS) -w \
                           -DCONFIG_TCC_CRTPREFIX="\"/lib\"" \
                           -DCONFIG_TCC_LIBPATHS="\"/lib\"" \
                           -DCONFIG_TCC_SYSINCLUDEPATHS="\"/include\"" \
                           -DCONFIG_TRIPLET="\"x86_64-linux-gnu\"" \
                           -DTCC_TARGET_X86_64 \
                           -DTCC_MUSL

$(O)/$(TCC)/tcc: $(O)/$(TCC)/tcc.o $(O)/$(TCC)/libtcc.a $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^

$(O)/$(TCC)/libtcc1.a: $(O)/$(TCC)/lib/libtcc1.o $(O)/$(TCC)/lib/alloca86_64.o $(O)/$(TCC)/lib/alloca86_64-bt.o
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_AR)$(AR) rcs $@ $^
