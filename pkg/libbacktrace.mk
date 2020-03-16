LIBBACKTRACE            := pkg/libbacktrace

LIBBACKTRACE_SRCS       := \
        $(LIBBACKTRACE)/alloc.c \
        $(LIBBACKTRACE)/backtrace.c \
        $(LIBBACKTRACE)/dwarf.c \
        $(LIBBACKTRACE)/elf.c \
        $(LIBBACKTRACE)/fileline.c \
        $(LIBBACKTRACE)/posix.c \
        $(LIBBACKTRACE)/read.c \
        $(LIBBACKTRACE)/sort.c \
        $(LIBBACKTRACE)/state.c \

LIBBACKTRACE_OBJS       := $(call object,$(LIBBACKTRACE_SRCS))

$(O)/$(LIBBACKTRACE)/libbacktrace.a: $(LIBBACKTRACE_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(LIBBACKTRACE)/%.o: CFLAGS := $(USER_CFLAGS)
