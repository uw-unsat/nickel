UBPF            := pkg/ubpf

UBPF_SRCS       := $(wildcard $(UBPF)/vm/*.c)

UBPF_OBJS    := $(call object,$(UBPF_SRCS))

$(O)/$(UBPF)/libubpf.a: $(UBPF_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(UBPF)/%.o: CFLAGS := $(USER_CFLAGS) -I $(UBPF)/vm/inc

$(O)/$(UBPF)/ubpf-test: $(O)/$(UBPF)/vm/test.o $(O)/$(UBPF)/libubpf.a $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
