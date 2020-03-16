verify-examples-%: examples/%/main.py $(O)/examples/%/__init__.py
	$(QUIET_PY2) PYTHONPATH=irpy:nickel:pkg:$(O):$(PYTHONPATH) $(PY2) $< $(ARGS)

$(O)/examples/%/__init__.py:
	@$(MKDIR_P) $(dir $@)
	@touch $@

PHONY += verify-examples-%
