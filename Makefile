PYTHON ?= python3

.PHONY: shellcheck check contracts lint test simulations library report-template proof-reports report-books simulation-reports
check: library report-template contracts lint test

contracts:
	$(PYTHON) verification/check_contract_coverage.py

lint:
	$(PYTHON) verification/check_static_lint.py

test:
	$(PYTHON) -m pytest -q tests

shellcheck:
	command -v shellcheck
	git ls-files -z '*.sh' | xargs -0 -r shellcheck --severity=warning

report-template: shellcheck
	bash scripts/check_report_template.sh

library: shellcheck
	bash scripts/check_library_layout.sh

simulations:
	$(PYTHON) -m reporting.simulate --pdf

proof-reports:
	$(PYTHON) -m reporting.rebuild_proofs

report-books: proof-reports

simulation-reports:
	$(PYTHON) -m reporting.rebuild_proofs --simulations-only
