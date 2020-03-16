COMPILER_RT             := pkg/compiler-rt

COMPILER_RT_SRCS        := \
        $(wildcard $(COMPILER_RT)/*.c) \

COMPILER_RT_OBJS    := $(call object,$(COMPILER_RT_SRCS))

$(O)/$(COMPILER_RT)/libcompiler_rt.a: $(COMPILER_RT_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(COMPILER_RT)/%.o: CFLAGS := $(USER_CFLAGS)
