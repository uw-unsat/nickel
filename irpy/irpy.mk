LLVM_CXXFLAGS   = $(shell "$(LLVM_CONFIG)" --cxxflags)
LLVM_LDFLAGS    = $(shell "$(LLVM_CONFIG)" --ldflags)
LLVM_LIBS       = $(shell "$(LLVM_CONFIG)" --libs --system-libs)

IRPY            := $(O)/irpy/compiler/irpy

IRPY_SRCS       := $(wildcard irpy/compiler/*.cc)
IRPY_OBJS       := $(addprefix $(O)/,$(patsubst %.cc,%.o,$(IRPY_SRCS)))

$(O)/irpy/%.o: irpy/%.cc
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CXX)$(CXX) -o $@ -c $(LLVM_CXXFLAGS) -O2 $<

$(IRPY): $(IRPY_OBJS)
	$(QUIET_LD)$(CXX) -o $@ $^ $(LLVM_LDFLAGS) -O2 $(LLVM_LIBS)

IRPY_TEST_SRCS  := $(wildcard irpy/test/*.c)
IRPY_TEST_LLS   := $(foreach opt,0 1 2,$(addprefix $(O)/,$(patsubst %.c,%_$(opt).ll,$(IRPY_TEST_SRCS))))
IRPY_TEST_PYS   := $(patsubst %.ll,%.py,$(IRPY_TEST_LLS))
IRPY_TEST_BINS  := $(addprefix $(O)/,$(patsubst %.c,%,$(IRPY_TEST_SRCS)))

IRPY_TEST_CFLAGS := -emit-llvm -S -g -mno-sse -mno-sse2

$(O)/irpy/test/%_0.ll: irpy/test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(LLVM_HOST_CC) -o $@ -c $(IRPY_TEST_CFLAGS) -O0 $<

$(O)/irpy/test/%_1.ll: irpy/test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(LLVM_HOST_CC) -o $@ -c $(IRPY_TEST_CFLAGS) -O1 $<

$(O)/irpy/test/%_2.ll: irpy/test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(LLVM_HOST_CC) -o $@ -c $(IRPY_TEST_CFLAGS) -O2 $<

$(O)/irpy/test/%: irpy/test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_LD)$(LLVM_HOST_CC) -o $@ $<

%.py: %.ll $(IRPY)
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_IRPY)$(IRPY) $< > $@~
	$(Q)mv $@~ $@

check-irpy: irpy/test/test.py $(IRPY_TEST_BINS) $(IRPY_TEST_PYS)
	$(Q)PYTHONPATH=irpy:$(O)/irpy/test:$(PYTHONPATH) python2 $< $(ARGS)

.SECONDARY: $(IRPY_TEST_LLS)

PHONY += check-irpy
