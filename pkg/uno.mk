UNO             := pkg/uno

UNO_LOCAL_SRCS  := \
        $(UNO)/src/uno_local.c \
        $(UNO)/src/heap.c \
        $(UNO)/src/nmetab.c \
        $(UNO)/src/symtab.c \
	$(UNO)/src/token.c \
        $(UNO)/src/tree.c \
        $(UNO)/src/treestk.c \
        $(UNO)/src/lexer.c \
        $(UNO)/src/c_gram.c \
        $(UNO)/src/dflow.c \
	$(UNO)/src/prnttree.c \
        $(UNO)/src/uno_lts.c \
        $(UNO)/src/explore.c \
	$(UNO)/src/uno_bounds.c \
        $(UNO)/src/uno_intervals.c \
        $(UNO)/src/uno_generic.c \

UNO_LOCAL_OBJS  := $(call object,$(UNO_LOCAL_SRCS))

$(O)/$(UNO)/%.o: CFLAGS := $(USER_CFLAGS) -DPC -DCPP="\"/bin/tcc -E\"" -DBINDIR=\"/bin\"

$(O)/$(UNO)/uno_local: $(UNO_LOCAL_OBJS) $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
