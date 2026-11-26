PYTHON ?= python3
LATEXMK ?= latexmk
PDF_DIR := output/pdf
.PHONY: all data pdf smoke
all: data pdf
data:
	$(PYTHON) simulate.py
smoke:
	$(PYTHON) simulate.py --rows-per-replicate 100000 --replicates 2 --block 50000 --workers 2
pdf:
	mkdir -p $(PDF_DIR)
	$(LATEXMK) -xelatex -outdir=$(PDF_DIR) -interaction=nonstopmode -halt-on-error iq_test_differences.tex
	$(LATEXMK) -xelatex -outdir=$(PDF_DIR) -interaction=nonstopmode -halt-on-error iq_difference_simulations.tex
