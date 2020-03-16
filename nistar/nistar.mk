NISTAR_ELF      := $(O)/nistar.elf
NISTAR_BIN      := $(basename $(NISTAR_ELF)).bin
NISTAR_SRCS     += $(wildcard nistar/*.S) $(wildcard nistar/*.c)
NISTAR_OBJS     := $(call object,$(NISTAR_SRCS))
NISTAR_IMPL_PY  := $(O)/nistar/impl.py
NISTAR_INIT_PY  := $(O)/nistar/__init__.py

NISTAR_LLS     := \
        $(O)/nistar/block.ll \
        $(O)/nistar/container.ll \
        $(O)/nistar/directory.ll \
        $(O)/nistar/gate.ll \
        $(O)/nistar/invariants.ll \
        $(O)/nistar/label.ll \
        $(O)/nistar/mm.ll \
        $(O)/nistar/pgtable.ll \
        $(O)/nistar/sched.ll \
        $(O)/nistar/syscall.ll \
        $(O)/nistar/thread.ll \

include nistar/user/user.mk

$(NISTAR_ELF): $(KERNEL_LDS) $(HEAD_OBJS) $(KERNEL_OBJS) $(NISTAR_OBJS)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $^

$(O)/nistar/impl.ll: $(NISTAR_LLS)
	$(QUIET_GEN)$(LLVM_LINK) -o $@ -S $^
	$(QUIET_CC)$(LLVM_CC) -S -emit-llvm -O2 $@ -o $@
	$(Q)./scripts/no_undef.sh $@

$(NISTAR_INIT_PY):
	@$(MKDIR_P) $(dir $@)
	@touch $@

serve-ipxe-nistar: $(NISTAR_BIN) $(NISTAR_INITRD)
	@echo '#!ipxe' > $(O)/boot.ipxe
	@echo "kernel http://$(IPXE_HOST):$(IPXE_PORT)/nistar.bin" >> $(O)/boot.ipxe
	@echo "initrd http://$(IPXE_HOST):$(IPXE_PORT)/nistar/user/initrd.cpio" >> $(O)/boot.ipxe
	@echo 'imgexec' >> $(O)/boot.ipxe
	cd $(O) && $(PY2) -m SimpleHTTPServer 8081

qemu-nistar: $(NISTAR_BIN) $(NISTAR_INITRD)
	$(Q)$(MAKE) KERNEL=$< INITRD=$(word 2,$^) qemu-kernel

bochs-nistar: $(NISTAR_BIN) $(NISTAR_INITRD)
	$(Q)$(MAKE) KERNEL=$< INITRD=$(word 2,$^) bochs-kernel

verify-nistar: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) nistar/verif/kernel/main.py $(ARGS)

verify-nistar-par-refinement: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::Nistar

verify-nistar-par-assumptions: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::NistarAssumptions

verify-nistar-par-inv: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::NistarInvariantTests

verify-nistar-par-spec-lemmas: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::NistarSpecLemma

verify-nistar-par-ni: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py \
		-k 'StepConsistency or LocalRespect or OutputConsistency or DomainConsistency'

verify-nistar-par-local-respect: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::LocalRespect

verify-nistar-par-step-consistency: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::StepConsistency

verify-nistar-par-output-consistency: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::OutputConsistency

verify-nistar-par-domain-consistency: $(NISTAR_IMPL_PY) $(NISTAR_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) scripts/pytest -v --duration=10 --full-trace -r fEsxX --color=auto -n=auto --boxed nistar/verif/kernel/main.py::DomainConsistency


check-nistar: $(NISTAR_BIN) $(NISTAR_INITRD)
	$(Q)tests/test_nistar.py -v

ALL += $(NISTAR_BIN)

PHONY += serve-ipxe-nistar qemu-nistar bochs-nistar verify-nistar
