PYTHON ?= python3

.PHONY: check contracts lint test symbolic
check: contracts lint test symbolic

contracts:
	$(PYTHON) verification/check_contract_coverage.py
	$(PYTHON) verification/spark_contracts.py

lint:
	$(PYTHON) verification/check_static_lint.py

test:
	$(PYTHON) -m pytest -q tests

symbolic:
	$(PYTHON) verification/check_symbolic.py
