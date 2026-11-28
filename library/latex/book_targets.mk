# Shared XeLaTeX targets for all four analysis directories.
# Consumers specify book stems and preserve model-specific data targets.
LATEXMK ?= latexmk
PDF_DIR ?= output/pdf
PDF_STEMS ?= $(ANALYTICAL_STEM)
BOOK_STEMS := $(ANALYTICAL_STEM) $(SIMULATION_STEM)
BIBINPUTS := $(abspath ../../reporting):$(CURDIR):

.PHONY: pdf simulation-pdf clean
pdf:
	mkdir -p "$(PDF_DIR)"
	BIBINPUTS="$(BIBINPUTS)" $(LATEXMK) -xelatex -outdir="$(PDF_DIR)" -interaction=nonstopmode -halt-on-error $(addsuffix .tex,$(PDF_STEMS))

simulation-pdf:
	mkdir -p "$(PDF_DIR)"
	BIBINPUTS="$(BIBINPUTS)" $(LATEXMK) -xelatex -outdir="$(PDF_DIR)" -interaction=nonstopmode -halt-on-error $(SIMULATION_STEM).tex

clean:
	$(LATEXMK) -c -outdir="$(PDF_DIR)" $(addsuffix .tex,$(BOOK_STEMS))
