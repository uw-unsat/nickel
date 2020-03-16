UIP             := pkg/uip
UIP_INCLUDE     := -I $(UIP)/uip -I $(UIP)/apps/dhcpc -I $(UIP)/apps/webserver -I $(UIP)/unix
UIP_CFLAGS      := $(UIP_INCLUDE) -fpack-struct

UIP_SRCS        := \
        $(UIP)/apps/webserver/http-strings.c \
        $(UIP)/apps/webserver/httpd.c \
        $(UIP)/apps/webserver/httpd-cgi.c \
        $(UIP)/apps/webserver/httpd-fs.c \
        $(UIP)/uip/psock.c \
        $(UIP)/uip/timer.c \
        $(UIP)/uip/uip.c \
        $(UIP)/uip/uip_arp.c \

UIP_OBJS        := $(call object,$(UIP_SRCS))

$(O)/$(UIP)/uip.a: $(UIP_OBJS)
	$(QUIET_AR)$(AR) rcs $@ $^

$(O)/$(UIP)/%.o: CFLAGS += $(UIP_CFLAGS) -w
