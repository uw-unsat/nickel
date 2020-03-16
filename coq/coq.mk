
COQ_SOURCES := \
    coq/dom_state_ni.v \
    coq/dynamic_ni.v \

COQ_OBJECTS := $(patsubst %.v, %.vo, $(COQ_SOURCES))

%.vo: %.v
	$(QUIET_COQC)coqc "$^"

coq-check: $(COQ_OBJECTS)

PHONY += coq-check
