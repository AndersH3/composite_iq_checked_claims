PYTHON ?= python3

.PHONY: check contracts lint test symbolic
check: library contracts lint test symbolic

contracts:
	$(PYTHON) verification/check_contract_coverage.py
	$(PYTHON) verification/spark_contracts.py

lint:
	$(PYTHON) verification/check_static_lint.py

test:
	$(PYTHON) -m pytest -q tests

symbolic:
	$(PYTHON) verification/check_symbolic.py

.PHONY: simulations
simulations:
	$(PYTHON) -m reporting.simulate --pdf

.PHONY: library
library:
	bash scripts/check_library_layout.sh

.PHONY: proof-reports
proof-reports:
	$(PYTHON) -m reporting.rebuild_proofs

.PHONY: report-books
report-books: proof-reports

.PHONY: simulation-reports
simulation-reports:
	$(PYTHON) -m reporting.rebuild_proofs --simulations-only
