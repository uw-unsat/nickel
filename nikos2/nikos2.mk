NIKOS2_ELF   := $(O)/nikos2.elf
NIKOS2_BIN   := $(basename $(NIKOS2_ELF)).bin

NIKOS2_SRCS  := $(wildcard nikos2/*.c)
NIKOS2_OBJS  := $(call object,$(NIKOS2_SRCS))

NIKOS2_IMPL_PY  := $(O)/nikos2/impl.py
NIKOS2_INIT_PY  := $(O)/nikos2/__init__.py

NIKOS2_LLS      := \
	$(O)/nikos2/syscall.ll \
	$(O)/nikos2/proc.ll

include nikos2/user/user.mk

$(O)/nikos2/impl.ll: $(NIKOS2_LLS)
	$(QUIET_GEN)$(LLVM_LINK) -o $@ -S $^
	$(QUIET_CC)$(LLVM_CC) -S -emit-llvm -O2 $@ -o $@
	$(Q)./scripts/no_undef.sh $@

$(NIKOS2_INIT_PY):
	@$(MKDIR_P) $(dir $@)
	@touch $@

$(NIKOS2_ELF): $(KERNEL_LDS) $(HEAD_OBJS) $(KERNEL_OBJS) $(NIKOS2_OBJS)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $^

qemu-nikos2: $(NIKOS2_BIN) $(NIKOS2_INITRD)
	$(Q)$(MAKE) KERNEL=$< INITRD=$(word 2,$^) qemu-kernel

bochs-nikos2: $(NIKOS2_BIN) $(NIKOS2_INITRD)
	$(Q)$(MAKE) KERNEL=$< INITRD=$(word 2,$^) bochs-kernel

verify-nikos2: $(NIKOS2_IMPL_PY) $(NIKOS2_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) nikos2/verif/main.py $(ARGS)

verify-nikos2-par: $(NIKOS2_IMPL_PY) $(NIKOS2_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nikos2/verif/main.py

ALL += $(NIKOS2_ELF)

PHONY += qemu-nikos2 bochs-nikos2 verify-nikos2
