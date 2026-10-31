GPRBUILD ?= gprbuild
GNATPROVE ?= gnatprove
PYTHON ?= python3
TRIALS ?= 1000000
SEED ?= 20261030
RESULTS ?= results

.PHONY: build run check prove clean
build:
	$(GPRBUILD) -P towers.gpr -p
run: build
	bin/towers_demo $(TRIALS) $(SEED) $(RESULTS)
check: run
	$(PYTHON) validate_results.py $(RESULTS) --replay
prove:
	$(GNATPROVE) -P towers_proof.gpr -U --prover=cvc5,z3,altergo --timeout=10 --report=statistics --checks-as-errors
clean:
	gprclean -P towers.gpr
