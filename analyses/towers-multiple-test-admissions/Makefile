PYTHON ?= python3
LATEXMK ?= latexmk
TEX_SOURCE := towers_admissions_analysis.tex
PDF_DIR := output/pdf

.PHONY: all pdf check data clean

all: check pdf

pdf:
	mkdir -p $(PDF_DIR)
	$(LATEXMK) -xelatex -outdir=$(PDF_DIR) -interaction=nonstopmode -halt-on-error $(TEX_SOURCE)

check:
	$(PYTHON) scripts/verify_calculations.py

data:
	$(PYTHON) scripts/verify_calculations.py --write

clean:
	$(LATEXMK) -c -outdir=$(PDF_DIR) $(TEX_SOURCE)
