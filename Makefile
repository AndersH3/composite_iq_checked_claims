PYTHON ?= python3

.PHONY: check contracts lint test simulations library proof-reports report-books simulation-reports
check: library contracts lint test

contracts:
	$(PYTHON) verification/check_contract_coverage.py

lint:
	$(PYTHON) verification/check_static_lint.py

test:
	$(PYTHON) -m pytest -q tests

library:
	bash scripts/check_library_layout.sh

simulations:
	$(PYTHON) -m reporting.simulate --pdf

proof-reports:
	$(PYTHON) -m reporting.rebuild_proofs

report-books: proof-reports

simulation-reports:
	$(PYTHON) -m reporting.rebuild_proofs --simulations-only
