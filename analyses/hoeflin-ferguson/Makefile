# Model-specific validation with shared document targets.
PYTHON ?= python3
ANALYTICAL_STEM := composite_iq_analysis
SIMULATION_STEM := hoeflin_simulations
.DEFAULT_GOAL := all

.PHONY: all check data
all: check pdf

check:
	$(PYTHON) scripts/verify_calculations.py

data:
	$(PYTHON) scripts/verify_calculations.py --write

include ../../library/latex/book_targets.mk
