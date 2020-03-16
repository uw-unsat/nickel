SPARSE          := pkg/sparse

SPARSE_SRCS     := \
        $(SPARSE)/allocate.c \
        $(SPARSE)/builtin.c \
        $(SPARSE)/char.c \
        $(SPARSE)/compat-linux.c \
        $(SPARSE)/cse.c \
        $(SPARSE)/dissect.c \
        $(SPARSE)/evaluate.c \
        $(SPARSE)/expand.c \
        $(SPARSE)/expression.c \
        $(SPARSE)/flow.c \
        $(SPARSE)/inline.c \
        $(SPARSE)/lib.c \
        $(SPARSE)/linearize.c \
        $(SPARSE)/liveness.c \
        $(SPARSE)/memops.c \
        $(SPARSE)/parse.c \
        $(SPARSE)/pre-process.c \
        $(SPARSE)/ptrlist.c \
        $(SPARSE)/scope.c \
        $(SPARSE)/show-parse.c \
        $(SPARSE)/simplify.c \
        $(SPARSE)/sort.c \
        $(SPARSE)/stats.c \
        $(SPARSE)/storage.c \
        $(SPARSE)/symbol.c \
        $(SPARSE)/target.c \
        $(SPARSE)/tokenize.c \
        $(SPARSE)/unssa.c \

SPARSE_OBJS     := $(call object,$(SPARSE_SRCS))

$(O)/$(SPARSE)/libsparse.a: $(SPARSE_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(SPARSE)/%.o: CFLAGS := $(USER_CFLAGS) -DGCC_BASE=\"/usr/lib/gcc/x86_64-linux-gnu/7/\" -DMULTIARCH_TRIPLET=\"x86_64-linux-gnu\" -w

$(O)/$(SPARSE)/sparse: $(O)/$(SPARSE)/sparse.o $(O)/$(SPARSE)/libsparse.a $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
