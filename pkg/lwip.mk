
LWIP := pkg/lwip

LWIP_SRCS :=                               \
        $(LWIP)/core/init.c          \
        $(LWIP)/core/def.c           \
        $(LWIP)/core/dns.c           \
        $(LWIP)/core/inet_chksum.c   \
        $(LWIP)/core/ip.c            \
        $(LWIP)/core/mem.c           \
        $(LWIP)/core/memp.c          \
        $(LWIP)/core/netif.c         \
        $(LWIP)/core/pbuf.c          \
        $(LWIP)/core/raw.c           \
        $(LWIP)/core/stats.c         \
        $(LWIP)/core/sys.c           \
        $(LWIP)/core/tcp.c           \
        $(LWIP)/core/tcp_in.c        \
        $(LWIP)/core/tcp_out.c       \
        $(LWIP)/core/timeouts.c      \
        $(LWIP)/core/udp.c           \
        $(LWIP)/core/ipv4/autoip.c   \
        $(LWIP)/core/ipv4/dhcp.c     \
        $(LWIP)/core/ipv4/etharp.c   \
        $(LWIP)/core/ipv4/icmp.c     \
        $(LWIP)/core/ipv4/igmp.c     \
        $(LWIP)/core/ipv4/ip4_frag.c \
        $(LWIP)/core/ipv4/ip4.c      \
        $(LWIP)/core/ipv4/ip4_addr.c \
        $(LWIP)/api/err.c            \
        $(LWIP)/netif/ethernet.c     \

LWIP_OBJS := $(addprefix $(O)/,$(LWIP_SRCS:.c=.o))

$(O)/lwip/liblwip.a: $(LWIP_OBJS)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_AR)$(AR) rcs $@ $^