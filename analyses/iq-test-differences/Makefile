# Specialized campaign and isolated smoke output; shared document targets.
PYTHON ?= python3
ANALYTICAL_STEM := iq_test_differences
SIMULATION_STEM := iq_difference_simulations
PDF_STEMS := $(ANALYTICAL_STEM) $(SIMULATION_STEM)
.DEFAULT_GOAL := all

.PHONY: all data smoke
all: data pdf

data:
	PYTHONPATH=../.. $(PYTHON) simulate.py

smoke:
	PYTHONPATH=../.. $(PYTHON) simulate.py --rows-per-replicate 100000 --replicates 2 --block 50000 --workers 2 --output-dir output/smoke

include ../../library/latex/book_targets.mk
