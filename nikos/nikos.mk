NIKOS_ELF   := $(O)/nikos.elf
NIKOS_BIN   := $(basename $(NIKOS_ELF)).bin

NIKOS_SRCS  := $(wildcard nikos/*.c)
NIKOS_OBJS  := $(call object,$(NIKOS_SRCS))

NIKOS_IMPL_PY  := $(O)/nikos/impl.py
NIKOS_INIT_PY  := $(O)/nikos/__init__.py

NIKOS_LLS      := \
	$(O)/nikos/syscall.ll \
	$(O)/nikos/proc.ll

include nikos/user/user.mk

$(O)/nikos/impl.ll: $(NIKOS_LLS)
	$(QUIET_GEN)$(LLVM_LINK) -o $@ -S $^
	$(QUIET_CC)$(LLVM_CC) -S -emit-llvm -O2 $@ -o $@
	$(Q)./scripts/no_undef.sh $@

$(NIKOS_INIT_PY):
	@$(MKDIR_P) $(dir $@)
	@touch $@

$(NIKOS_ELF): $(KERNEL_LDS) $(HEAD_OBJS) $(KERNEL_OBJS) $(NIKOS_OBJS)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $^

qemu-nikos: $(NIKOS_BIN) $(NIKOS_INITRD)
	$(Q)$(MAKE) KERNEL=$< INITRD=$(word 2,$^) qemu-kernel

bochs-nikos: $(NIKOS_BIN) $(NIKOS_INITRD)
	$(Q)$(MAKE) KERNEL=$< INITRD=$(word 2,$^) bochs-kernel

verify-nikos: $(NIKOS_IMPL_PY) $(NIKOS_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) nikos/verif/main.py $(ARGS)

verify-nikos-par: $(NIKOS_IMPL_PY) $(NIKOS_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nikos/verif/main.py


ALL += $(NIKOS_ELF)

PHONY += qemu-nikos bochs-nikos verify-nikos
