TESTS   :=                                    \
        $(O)/tests/hello32.elf                \
        $(O)/tests/hello64.bin                \
        $(O)/tests/crypto.bin                 \
        $(O)/tests/lv6.bin                    \
        $(O)/tests/uip.bin                    \
        $(O)/tests/komodo.bin                 \

TESTS_OBJS = $(call object,$(call rwildcard,tests/,*.c *.S))

$(O)/tests/hello32.o: CFLAGS += -m32

$(O)/tests/hello32.elf: $(O)/tests/hello32.o
	$(QUIET_LD)$(LD) -o $@ -m elf_i386 -N -Ttext 0x100000 $<

$(O)/tests/hello64.elf: $(O)/tests/hello64.o
	$(QUIET_LD)$(LD) -o $@ -Ttext 0x100000 $<

$(O)/tests/crypto.elf: $(KERNEL_LDS) $(HEAD_OBJS) $(KERNEL_OBJS) $(O)/tests/crypto.o
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $^

$(O)/tests/lv6.elf: $(KERNEL_LDS) $(HEAD_OBJS) $(KERNEL_OBJS) $(call object,$(call rwildcard,tests/lv6/,*.c *.S))
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $^

$(O)/tests/uip.elf: $(KERNEL_LDS) $(HEAD_OBJS) $(KERNEL_OBJS) $(O)/tests/uip.o $(O)/$(UIP)/uip.a
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $^

$(O)/tests/uip.o: CFLAGS += $(UIP_INCLUDE)

$(O)/tests/komodo.elf: $(KERNEL_LDS) $(HEAD_OBJS) $(KERNEL_OBJS) $(call object,$(wildcard tests/komodo/*.c) tests/komodo/image.S)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T $^

#$(O)/tests/komodo/image.o: $(O)/tests/komodo/enclave.elf
$(O)/tests/komodo/image.o: CFLAGS += -I $(O)/tests/komodo

$(O)/tests/komodo/translate.o: tests/komodo/test_enclave.inc

tests/komodo/%.inc: tests/komodo/%.S
	$(Q)$(LLVM_HOST_CC) --target=arm-none-eabi -c $< -o - | \
            $(LLVM_OBJDUMP) -triple=armv6t2 -d - | \
            sed -n 's/.*\([0-9a-z][0-9a-z]\) \([0-9a-z][0-9a-z]\) \([0-9a-z][0-9a-z]\) \([0-9a-z][0-9a-z]\).*/        0x\4\3\2\1, \/\* & \*\//p' | \
            expand > $@~
	$(QUIET_GEN)mv $@~ $@

$(O)/tests/komodo/enclave.elf: $(call object,tests/komodo/enclave.S tests/komodo/translate.c)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^

check-vmm: all $(TESTS)
ifneq ($(UNAME_S),Linux)
	$(error works on Linux only)
else
	$(Q)tests/test_vmm.py -v $(ARGS)
endif

PRECIOUS += tests/komodo/%.inc $(O)/tests/komodo/%.elf
