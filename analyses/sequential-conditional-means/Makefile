LATEXMK ?= latexmk
TEX_SOURCE := sequential_conditional_means.tex
PDF_DIR := output/pdf

.PHONY: all pdf clean

all: pdf

pdf:
	mkdir -p $(PDF_DIR)
	$(LATEXMK) -xelatex -outdir=$(PDF_DIR) -interaction=nonstopmode -halt-on-error $(TEX_SOURCE)

clean:
	$(LATEXMK) -c -outdir=$(PDF_DIR) $(TEX_SOURCE)
