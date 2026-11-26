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
