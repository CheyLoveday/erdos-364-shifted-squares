PYTHON ?= python3

.PHONY: check clean

check:
	$(PYTHON) scripts/check_bootstrap.py
	git diff --check

clean:
	rm -rf build staging .stage-arxiv
