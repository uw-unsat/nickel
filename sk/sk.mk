MCERTIKOS_INIT_PY  := $(O)/sk/__init__.py

$(SK_INIT_PY):
	@$(MKDIR_P) $(dir $@)
	@touch $@

verify-sk: $(SK_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) sk/verif/main.py $(ARGS)

PHONY += verify-sk
