HOST_BINS := \
        $(O)/host/picosat \
        $(O)/host/sh \
        $(O)/host/spell \

host: $(HOST_BINS)

$(O)/host/picosat: $(PICOSAT_SRCS) $(PICOSAT)/app.c $(PICOSAT)/main.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_GEN)$(HOST_CC) -o $@ -w $^

# $(O)/host/sh: nistar/user/bin/sh.c nistar/user/lib/linenoise.c
# 	$(Q)$(MKDIR_P) $(@D)
# 	$(QUIET_GEN)$(HOST_CC) -o $@ -I include/uapi $^

$(O)/host/spell: nistar/user/bin/spell.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_GEN)$(HOST_CC) -o $@ $^
