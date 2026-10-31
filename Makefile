PYTHON ?= python3

.PHONY: check contracts lint test
check: contracts lint test

contracts:
	$(PYTHON) verification/check_contract_coverage.py

lint:
	$(PYTHON) verification/check_static_lint.py

test:
	$(PYTHON) -m pytest -q tests
