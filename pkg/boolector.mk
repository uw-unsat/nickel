BOOLECTOR       := pkg/boolector

BOOLECTOR_SRCS  := \
        $(wildcard $(BOOLECTOR)/btor*.c) \
        $(BOOLECTOR)/boolector.c \

BOOLECTOR_OBJS    := $(call object,$(BOOLECTOR_SRCS))

$(O)/$(BOOLECTOR)/libboolector.a: $(BOOLECTOR_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(BOOLECTOR)/%.o: CFLAGS := $(USER_CFLAGS) -DNDEBUG -DBTOR_USE_PICOSAT -w

$(O)/$(BOOLECTOR)/boolector: $(O)/$(BOOLECTOR)/boolectormain.o $(O)/$(BOOLECTOR)/libboolector.a $(O)/$(PICOSAT)/libpicosat.a $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
