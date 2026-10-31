GPRBUILD ?= gprbuild
GNATPROVE ?= gnatprove
PROVERS ?= cvc5,z3,altergo,colibri
PYTHON ?= python3
TRIALS ?= 500000
SEED ?= 20261030
OUTPUT ?= results

.PHONY: all build run check prove clean
all: build
build:
	$(GPRBUILD) -P hoeflin.gpr -p
run: build
	mkdir -p $(OUTPUT)
	bin/hoeflin_calculations > $(OUTPUT)/calculations.csv
	bin/hoeflin_simulation $(TRIALS) $(SEED) > $(OUTPUT)/simulation.csv
check: run
	$(PYTHON) scripts/validate_results.py --calculations $(OUTPUT)/calculations.csv --simulation $(OUTPUT)/simulation.csv --json-output $(OUTPUT)/validation.json
prove:
	$(GNATPROVE) -P hoeflin_proof.gpr -U --mode=all --prover=$(PROVERS) --steps=0 --timeout=30 --report=statistics --checks-as-errors
clean:
	gprclean -P hoeflin.gpr
	gprclean -P hoeflin_proof.gpr
