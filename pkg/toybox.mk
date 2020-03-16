TOYBOX          := pkg/toybox

TOYBOX_BINS     := \
        ascii \
        base64 \
        basename \
        cat \
        cmp \
        dirname \
        echo \
        factor \
        false \
        md5sum \
        nl \
        od \
        paste \
        printf \
        rev \
        sha1sum \
        sort \
        split \
        strings \
        tac \
        touch \
        true \
        wc \
        xxd \
        yes \

TOYBOX_SRCS     := \
        $(TOYBOX)/lib/args.c \
        $(TOYBOX)/lib/help.c \
        $(TOYBOX)/lib/lib.c \
        $(TOYBOX)/lib/linestack.c \
        $(TOYBOX)/lib/llist.c \
        $(TOYBOX)/lib/xwrap.c \
        $(TOYBOX)/main.c \
        $(foreach bin,$(TOYBOX_BINS),$(wildcard $(TOYBOX)/toys/*/$(bin).c)) \

TOYBOX_OBJS     := $(call object,$(TOYBOX_SRCS))

$(O)/$(TOYBOX)/%.o: CFLAGS := $(USER_CFLAGS) -I $(TOYBOX) -w -funsigned-char

$(O)/$(TOYBOX)/toybox: $(TOYBOX_OBJS) $(USER_LDLIBS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) $^
