# Reproducibility — Cary Conjectures 5.1 and 5.4

This directory contains two independent Python verification programs
accompanying the preprint *Two exact counterexamples to conjectures
of Cary*.

## Files

- `verificatore_indipendente_Cary.py`: exact-arithmetic verification
  of the two counterexamples and their certificates.
- `verificatore_indipendente.py`: a separately developed verification
  program, including additional Fourier and polarity checks.

Both programs use only the Python standard library and exact
arithmetic (`fractions.Fraction`). Python 3.10 or later is recommended.

## Running the programs

Download the two Python files into the same directory and open a
terminal in that directory.

First verifier:

```bash
python3 verificatore_indipendente_Cary.py --output-dir results
```

Second verifier:

```bash
python3 verificatore_indipendente.py results_astra.json
```

The first program produces a JSON report and an execution log.
The second produces a JSON report.

Both programs can also be executed with `python3 -O`; their
mathematical checks remain enabled.

## Expected results

The first verifier should report:

- 100164 successful checks in 146 categories.
- The optimal value 3 for the five-variable counterexample.
- The exact covariance-variance gap 115/131072 for the
  eleven-variable counterexample.

The second verifier should report:

- 414160 successful checks in 117 categories.
- Matching exact numerical certificates for both counterexamples.
- Additional Fourier and conditional-expectation cochain checks.

## Mathematical scope

The programs verify finite, explicitly specified certificates,
including the 27 entries of the primal cochain table, divergence
equations, Fourier coefficients, and the strict covariance
obstruction.

The universal certificate lemmas, the interpretation of Cary's
conjectures, and the extensions to arbitrary dimensions are
established by mathematical arguments in the accompanying preprint,
not by exhaustive computation.

These checks do not constitute formal proof-assistant verification
or independent human peer review.

## Source

Jonathan Cary, *On Kleitman's Conjecture*,
arXiv:2402.03150v5.

Preprint: *Two exact counterexamples to conjectures of Cary*,
Patrizio Cintioli, 1 November 2026.
