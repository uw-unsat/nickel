SIMPLE_INIT_PY  := $(O)/simple-template/__init__.py

$(SIMPLE_INIT_PY):
	@$(MKDIR_P) $(dir $@)
	@touch $@

verify-simple: $(SIMPLE_INIT_PY)
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) simple-template/main.py $(ARGS)

PHONY += verify-mcertikos
