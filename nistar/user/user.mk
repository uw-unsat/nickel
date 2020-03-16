NISTAR_INITRD           := $(O)/nistar/user/initrd.cpio

NISTAR_PKGS             := $(notdir $(shell find pkg -mindepth 1 -maxdepth 1 -type d))

NISTAR_TOYBOX_BINS      := $(addprefix $(O)/nistar/user/bin/,$(TOYBOX_BINS))

NISTAR_USER             := \
        $(O)/nistar/user/bin/authd \
        $(O)/nistar/user/bin/cat \
        $(O)/nistar/user/bin/ctree \
        $(O)/nistar/user/bin/dlhello \
        $(O)/nistar/user/bin/fork-test \
        $(O)/nistar/user/bin/fork-loop \
        $(O)/nistar/user/bin/log-timer2 \
        $(O)/nistar/user/bin/ns \
        $(O)/nistar/user/bin/ns-test \
        $(O)/nistar/user/bin/gate-bench \
        $(O)/nistar/user/bin/syscall-bench \
        $(O)/nistar/user/bin/gate-test \
        $(O)/nistar/user/bin/hello \
        $(O)/nistar/user/bin/labels \
        $(O)/nistar/user/bin/ls \
        $(O)/nistar/user/bin/sched-test \
        $(O)/nistar/user/bin/sh \
        $(O)/nistar/user/bin/spawn-test \
        $(O)/nistar/user/bin/spell \
        $(O)/nistar/user/bin/tcc \
        $(O)/nistar/user/bin/timer \
        $(O)/nistar/user/bin/log-timer \
        $(O)/nistar/user/bin/toybox \
        $(O)/nistar/user/bin/ubpf-test \
        $(O)/nistar/user/bin/uno_local \
        $(O)/nistar/user/init \
        $(O)/nistar/user/lib/crt1.o \
        $(O)/nistar/user/lib/crti.o \
        $(O)/nistar/user/lib/crtn.o \
        $(O)/nistar/user/lib/ld-musl-x86_64.so.1 \
        $(O)/nistar/user/lib/libc.so \
        $(O)/nistar/user/lib/tcc/libtcc1.a \
        $(O)/nistar/user/share/big.txt \
        $(O)/nistar/user/share/README \
        $(O)/nistar/user/src/hello.c \

NISTAR_USER_EXTRAS   += \
        $(O)/nistar/user/bin/boolector \
        $(O)/nistar/user/share/rosette.smt2 \

NISTAR_USER_EXTRAS   += \
        $(O)/nistar/user/bin/picosat \
        $(O)/nistar/user/share/test.cnf \

NISTAR_USER_EXTRAS   += \
        $(O)/nistar/user/bin/riscvemu64 \
        $(O)/nistar/user/share/bbl64.bin \
        $(O)/nistar/user/share/root-riscv64.cfg \
        $(O)/nistar/user/share/root-riscv64.bin \

NISTAR_USER_EXTRAS   += \
        $(O)/nistar/user/bin/selfie \
        $(O)/nistar/user/src/selfie.c \

NISTAR_USER_EXTRAS   += \
        $(O)/nistar/user/bin/http-parser-test \
        $(O)/nistar/user/bin/linenoise-test \
        $(O)/nistar/user/bin/sqlite3 \

#NISTAR_USER          += $(NISTAR_TOYBOX_BINS)
#NISTAR_USER          += $(NISTAR_USER_EXTRAS)

$(NISTAR_INITRD): $(NISTAR_USER)
	$(Q)cd $(@D) && find $(^:$(@D)/%=%) | cpio -o -H newc --quiet > $(@F)~
	$(QUIET_GEN)mv $@~ $@

NISTAR_USER_SRCS     := $(wildcard nistar/user/*.c nistar/user/bin/*.c)
NISTAR_USER_OBJS     := $(call object,$(NISTAR_USER_SRCS))

NISTAR_USER_LIB_SRCS := $(wildcard nistar/user/lib/*.S nistar/user/lib/*.c)
NISTAR_USER_LIB_OBJS := $(call object,$(NISTAR_USER_LIB_SRCS))

# bin
$(O)/nistar/user/%: $(O)/nistar/user/%.o $(USER_LDLIBS)
	$(QUIET_LD)$(LD) -o $@ -static $(LDFLAGS) $^

include pkg/lwip.mk

$(O)/$(LWIP)/%.o: CFLAGS := $(USER_CFLAGS) -Ipkg/lwip/include -Inistar/user/include

$(O)/nistar/user/bin/ns.o: CFLAGS := $(USER_CFLAGS) -Ipkg/lwip/include -Inistar/user/include

$(O)/nistar/user/bin/ns: $(O)/nistar/user/bin/ns.o $(O)/lwip/liblwip.a $(USER_LDLIBS)
	$(QUIET_LD)$(LD) -o $@ -static $(LDFLAGS) $^

$(O)/nistar/user/bin/dlhello: $(O)/nistar/user/bin/hello.o $(USER_CRT_OBJS) $(O)/nistar/user/lib/libc.so
	$(QUIET_LD)$(LD) -o $@ -dynamic-linker /lib/ld-musl-x86_64.so.1 $(LDFLAGS) $< $(USER_CRT_OBJS) -L $(O)/nistar/user/lib -lc

define nistar_pkg_bin
$$(O)/nistar/user/bin/%: $$(O)/pkg/$(1)/%
	$$(Q)$$(MKDIR_P) $$(@D)
	$$(Q)cp $$< $$@
endef

$(foreach pkg,$(NISTAR_PKGS),$(eval $(call nistar_pkg_bin,$(pkg))))

# should be symbolic links eventually; for now just copy toybox
$(NISTAR_TOYBOX_BINS): $(O)/nistar/user/bin/toybox
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@

# lib
$(O)/nistar/user/lib/libc.a: $(LIBBACKTRACE_OBJS) $(MUSL_OBJS) $(NISTAR_USER_LIB_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/nistar/user/lib/libc.so: $(LIBBACKTRACE_OBJS) $(MUSL_OBJS) $(MUSL_LDSO_OBJS) $(NISTAR_USER_LIB_OBJS)
	$(QUIET_LD)$(LD) -shared -nostdlib --sort-section=alignment --sort-common --hash-style=both --no-undefined --exclude-libs=ALL -Bsymbolic-functions --entry=_dlstart -o $@ $^

# should be symbolic links eventually
$(O)/nistar/user/lib/ld-musl-x86_64.so.1: $(O)/nistar/user/lib/libc.so
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@

$(O)/nistar/user/lib/tcc/%: $(O)/$(TCC)/%
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@

$(O)/nistar/user/lib/%.o: $(O)/$(MUSL)/crt/%.o
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@

$(O)/nistar/user/lib/%.o: $(O)/$(MUSL)/crt/$(ARCH)/%.o
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@

# share
$(O)/nistar/user/share/%: nistar/user/share/%
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@

# src
$(O)/nistar/user/src/%: nistar/user/bin/%
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@

$(O)/nistar/user/%.o: CFLAGS := $(USER_CFLAGS)

$(O)/nistar/user/%/asm-offsets.S: CFLAGS := $(USER_CFLAGS)

$(O)/nistar/user/bin/selfie.o: CFLAGS := $(USER_CFLAGS) -w \
                                            -D'main(a,b)=main(int argc, char** argv)' \
                                            -Duint64_t='unsigned long long'

$(O)/nistar/user/lib/__init_tls.o: CFLAGS := $(USER_CFLAGS) -Wno-unused-value
