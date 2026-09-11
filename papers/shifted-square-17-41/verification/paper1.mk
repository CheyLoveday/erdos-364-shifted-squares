PAPER1_PYTHON ?= python3
PAPER1_OUT ?= .paper1-build
PAPER1_VERIFY := papers/shifted-square-17-41/verification

.PHONY: paper1-check paper1-verify paper1-build paper1-stage paper1-check-export
paper1-check paper1-verify paper1-build paper1-stage paper1-check-export:
	$(PAPER1_PYTHON) -B $(PAPER1_VERIFY)/release.py $(@:paper1-%=%) --output $(PAPER1_OUT)
