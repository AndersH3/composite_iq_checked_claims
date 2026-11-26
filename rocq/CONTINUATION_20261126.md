# Five-priority continuation — verification boundaries

Researcher/requester: Anders Hellström. AI-assisted source and analysis; only kernel and runtime checks establish verification.

Verified baseline: 8d2f76afb5fbbae250eb4d21c893d5e2cc4bda8d. All 45 canonical modules and the original 16 IQ algebra scripts passed locally with Rocq 9.3.0. Python 122 tests and 400 million synthetic rows passed before this change. Retain the published evidence unchanged until rerunning the revised source.

| Priority | Work in this revision | Open obligation |
|---|---|---|
| FormalML / MathComp | Upstream API inspection; CE transfer, normalized convolution and density-factorization candidates | Compile pinned libraries and all new scripts; upstream FormalML compatibility remains unresolved |
| Gaussian independence | Factor prior-likelihood density in centered residual coordinates using upstream conjugacy | Show measure pushforward under shear, factor rectangle probabilities and generalize to arbitrary joint Gaussian vectors, including singular boundaries |
| IQ propositions | Weighted Jensen deficit and strict inequality; written two-component proof | Folded normal integrals, joint order statistics, orthant law, selection and full Gaussian distributional arguments |
| Refactoring | Shared provenance, safe smoke path, floating-point correlation endpoint, small-scale folded mean | Re-run contracts, full Dask and PDFs |
| CI | Four failed workflows at verified baseline were submitted for failed-job rerun. Rocq job 140149809824 returned BlobNotFound and no step records | No verified root cause; inspect Actions UI or gh run view logs; never weaken gates to turn CI green |

CI run IDs: 45889938315 (books), 45889938182 (migration), 45889938621 (Python), 45889938258 (Rocq). The rerun requests were accepted, not confirmed successful. No change to required compiler versions or CI acceptance conditions. MathComp now requires all six candidate theorem declarations and Python CI verifies the smoke run does not modify tracked production data.


### Repeat computer10 validation at 0b22b3f

The researcher-provided November 26 terminal transcript identifies source revision `0b22b3f64c6429d04071b5c5f56028e86a3b8301` and records:

- ShellCheck and documentation audit passed: 4,020 declarations, 3,686 theorem/helper proofs and 3,699 registered proof scripts.
- Rocq 9.3.0 (OCaml 4.14.2) compiled all 45 canonical modules, including all 18 IQ discrepancy algebra theorems and both weighted-scale Jensen certificates. Stdlib is 9.2.0; the switch name `rocq-9.2` is not the actual compiler version.
- The Python audit passed for 139 functions and 2,217 contracts, with a minimum of 15; static lint passed with its expected DEL012 negative control; all 122 tests passed in 12.80 s.
- The isolated IQ smoke run completed and the production-data Git diff was empty. The full default Dask/Deal run exited zero in 25.76 s wall clock (379% CPU, 421,100 KiB peak RSS). Its ten scenarios each use 40 million rows; failure of any diagnostic would exit nonzero.
- Both XeLaTeX books built successfully (12 and 13 pages, respectively); the transcript shows the usual geometry and unicode-math warnings. No fresh visual inspection or artifact publication is demonstrated by this transcript. The new generated files and exact source hashes must be published from computer10.
- MathComp and FormalML were not installed in the inspected switch; Docker was not found in PATH. Their candidate scripts remain unverified. The existing validated switch is to be preserved; use the isolated environment in [PROBABILITY_LIBRARY_VALIDATION.md](PROBABILITY_LIBRARY_VALIDATION.md).

