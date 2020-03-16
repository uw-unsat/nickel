SQLITE3         := pkg/sqlite3

SQLITE3_SRCS    := \
        $(wildcard $(SQLITE3)/*.c) \

SQLITE3_OBJS    := $(call object,$(SQLITE3_SRCS))

$(O)/$(SQLITE3)/%.o: CFLAGS := $(USER_CFLAGS) -w \
                               -DSQLITE_THREADSAFE=0 \
                               -DSQLITE_OMIT_LOAD_EXTENSION \
                               -DSQLITE_OMIT_POPEN \
                               -D_BSD_SOURCE \
                               -D__minux \
                               -DHAVE_LINENOISE \

$(O)/$(SQLITE3)/sqlite3: $(SQLITE3_OBJS) $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
