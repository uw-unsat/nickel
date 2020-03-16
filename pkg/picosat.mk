PICOSAT         := pkg/picosat

PICOSAT_SRCS    := \
        $(PICOSAT)/picosat.c \
        $(PICOSAT)/version.c \

PICOSAT_OBJS    := $(call object,$(PICOSAT_SRCS))

$(O)/$(PICOSAT)/libpicosat.a: $(PICOSAT_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(PICOSAT)/%.o: CFLAGS := $(USER_CFLAGS) -DNGETRUSAGE -DNALLSIGNALS -w

$(O)/$(PICOSAT)/picosat: $(O)/$(PICOSAT)/main.o $(O)/$(PICOSAT)/app.o $(O)/$(PICOSAT)/libpicosat.a $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
