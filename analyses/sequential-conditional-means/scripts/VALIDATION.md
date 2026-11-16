**Author:** Anders Hellström.

The supplementary validator checks the SPARK executable's CSV output with
Python libraries that use different numerical methods. From the repository
root, run:

```sh
.venv/bin/python analyses/sequential-conditional-means/scripts/validate_spark.py PATH_TO_RESULTS --json-output PATH_TO_SUMMARY.json
```

The results directory must contain `calculation.csv`, `simulation.csv` and
`checks.csv`. Optional `--calculations`, `--simulation` and `--checks` arguments
select explicit files. The validator only reads these inputs; it writes a
summary when requested. Deal is explicitly enabled at the CLI entry point,
including when Python runs with `-O`.

The finite calculation schema is
`r,k,c,a_z,prediction_z,mean_z,population_variance,conditional_variance,prediction_limit_z,mean_limit_z,population_variance_limit,conditional_variance_limit`.
Here `k` counts subsequent predictions and every inclusive mean has `r+k`
terms. Negative correlations are accepted on their finite PSD domain and must
leave the four limit fields blank. `fractions.Fraction` checks scalar formulas
exactly; NumPy independently conditions the complete covariance matrix using
the Schur complement and a Moore–Penrose inverse at singular boundaries.
Reported floating values are compared at absolute/relative tolerance `2e-10`.

The simulation schema is
`mode,r,k,c,a_z,trials,seed,sample_mean_z,sample_variance_z`; extra columns may
be retained. Modes are `population`, `conditional`, `population_limit` and
`conditional_limit`. Only limit modes use the `k=0` sentinel. Variance must use
the unbiased `trials-1` denominator. Population means have expectation zero;
conditional means use the fixed starting history. SciPy supplies two-sided
normal checks of empirical means and chi-square checks of empirical variances,
each with tail probability `1e-10` per row. Under the assumed independent normal
sampling model, a union bound over the 24 required rows gives at most `4.8e-9`
probability of any diagnostic failure. Independence between rows is unnecessary
for that bound. The check does not establish that a pseudorandom generator
produces independent Gaussian observations.

The identity-check schema is `name,actual,expected,tolerance`. Eighteen mandatory
names cover recursive predictions, covariance eigenvectors, inverse identities
the variance decomposition, finite variance differences and the paper's
three-atom counterexample. Expected values are fixed in the
validator, so changing both CSV answer columns cannot approve a false claim.
Tolerances must be positive and at most `1e-8`; maximum absolute residuals must
also be nonnegative.

The integration gate requires all nine IQ-150 cases (`r=1,2,3`, `k=1,2,10`,
`c=0.6`), their eighteen finite population/conditional simulations, and six
limit simulations. Admissible extra cases may supplement them. A separate
self-check verifies the earlier standardized examples, the limit table,
all 74 printed integer rounding certificates and the counterexample's exact
finite probability law. These checks supplement the mathematical derivations;
they do not turn sampling diagnostics or numerical linear algebra into formal
proofs.

The validator's 17 named functions carry 135 distinct Deal declarations, with
a minimum of five per function. The exact finite/matrix/limit calculations and
rounding-certificate function have at least eleven each. Their contracts cover
domains, output types and bounds, inclusive counting, singular endpoints,
rounding uniqueness, exception boundaries and side effects as appropriate.
Structural counts alone do not establish adequacy or universal validity.

Targeted tests in `tests/test_sequential_spark_validation.py` exercise negative
PSD boundaries, singular matrices, invalid mathematical domains, corrupted
CSV values, missing experiment coverage, altered check targets, rounding ties,
actual NumPy normal samples and CLI serialization. Repository-wide coverage,
static lint and tests remain separate verification gates.

The campaign runner also uses contracted functions: three orchestration helpers carry ten declarations each and the CLI has five. The read-only `audit_spark.py` function carries ten declarations. Run it against the retained campaign to verify artifact/source hashes, current Ada identity, native proof scope and the CSVs with the current validator. The source archive preserves the original proof-time Python. Later Python-only differences are listed explicitly instead of being represented as new native proof evidence.
