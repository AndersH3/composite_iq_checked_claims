#!/usr/bin/env bash
# Enforce the shared book-template structure for all six maintained reports.
# This is a structural check, not an independent review of report conclusions.
set -euo pipefail
cd "$(dirname "$0")/.."

require_count() {
  local file="$1" literal="$2" expected="$3" actual
  actual="$(grep -F -c -- "$literal" "$file" || true)"
  if [[ "$actual" -ne "$expected" ]]; then
    printf 'FAIL: %s has %s occurrences of %s; expected %s\n' \
      "$file" "$actual" "$literal" "$expected" >&2
    exit 1
  fi
}

for spec in \
  'hoeflin-ferguson composite_iq_analysis report_style' \
  'hoeflin-ferguson hoeflin_simulations simulation_style' \
  'towers-multiple-test-admissions towers_admissions_analysis report_style' \
  'towers-multiple-test-admissions towers_simulations simulation_style' \
  'sequential-conditional-means sequential_conditional_means report_style' \
  'sequential-conditional-means sequential_simulations simulation_style'
do
  read -r project stem style <<< "$spec"
  book="analyses/$project/$stem.tex"
  test -s "$book"
  require_count "$book" "\input{../../library/latex/$style}" 1
  require_count "$book" '\ProjectReportTitlePage' 1
  require_count "$book" '\ProjectReportAIAppendix' 1
  require_count "$book" '\renewcommand{\ProjectReportHighlights}' 1
  require_count "$book" '\frontmatter' 1
  require_count "$book" '\mainmatter' 1
  require_count "$book" '\appendix' 1
  require_count "$book" '\begin{abstract}' 1
  require_count "$book" '\end{abstract}' 1
  require_count "$book" '\tableofcontents' 1
  require_count "$book" '\end{document}' 1

  # Disallow old/new layout coexistence or an extra initial AI notice.
  for forbidden in \
    '\noindent\textbf{AI disclosure.}' \
    '\chapter{AI disclosure' \
    '\input{../../reporting/ai_disclosure}' \
    '\input{../../library/latex/ai_disclosure}' \
    '\maketitle' \
    '\begin{titlepage}' \
    '\ihead{' \
    '\ohead{' \
    '\thispagestyle{plain.scrheadings}'
  do
    require_count "$book" "$forbidden" 0
  done
  echo "Book template: $book OK"
done

require_count library/latex/report_style.tex '\newcommand*{\ProjectReportTitlePage}' 1
require_count library/latex/report_style.tex '\newcommand{\ProjectReportAIAppendix}' 1
require_count library/latex/report_style.tex '\begin{disclosurebox}' 1
require_count library/latex/report_style.tex '\chapter{AI disclosure and provenance}' 1
require_count library/latex/simulation_style.tex '\input{../../library/latex/report_style}' 1
require_count library/latex/ai_disclosure.tex 'No participant data were collected' 1
require_count reporting/book_style.tex '\input{../../library/latex/report_style}' 1
require_count reporting/simulation_style.tex '\input{../../library/latex/simulation_style}' 1
require_count reporting/ai_disclosure.tex '\input{../../library/latex/ai_disclosure}' 1

echo 'Report structure validated: one initial AI notice and one full final appendix in each book.'
