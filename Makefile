PYTHON ?= python3

.PHONY: check contracts test
check: contracts test

contracts:
	$(PYTHON) verification/check_contract_coverage.py

test:
	$(PYTHON) -m pytest -q tests
