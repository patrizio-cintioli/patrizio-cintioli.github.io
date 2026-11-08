# Reproducibility — Lower-Section Polarity and Boolean Substitution

This directory contains the exact-arithmetic computational supplement to the preprint **_Lower-Section Polarity and Boolean Substitution_** by Patrizio Cintioli.


The main result of the preprint is proved mathematically. The files here provide additional finite checks of the lower-section substitution construction, not a computational proof of the general theorem.

## Files

- [`verify_examples.py`](verify_examples.py) — an independently developed Python verifier for the Fano-family examples discussed in Section 5 of the preprint.
- [`results.json`](results.json) — the recorded standard output of a successful execution of the verifier.
- `REPRODUCIBILITY.md` — these instructions.

## Requirements and execution

Python **3.10 or later** is required. The program uses only the Python standard library, including `fractions.Fraction`, and performs its mathematical checks with exact integer and rational arithmetic. No third-party packages, optimization solver, or internet connection are needed.

Download `verify_examples.py` and open a terminal in the directory containing it. Run:

```bash
python3 verify_examples.py > results.json
```

**Important:** The verifier uses Python `assert` statements. Run it with assertions enabled; **do not use `python3 -O` or `python3 -OO`**. The program also explicitly rejects optimized execution.

A successful run exits without an error and writes the JSON summary to `results.json`. A failed check raises an exception or assertion error. If you want to preserve the distributed results file, write the output to another location, for example:

```bash
python3 verify_examples.py > results_reproduced.json
```

You can then compare `results_reproduced.json` with the supplied `results.json`.

## Expected results

The output reports:

| Verification | Expected result |
| --- | ---: |
| Lower sections of the seven-variable Fano upset | 128 |
| Total vertices across those sections | 2,187 |
| Composition cases | 4 |
| Total vertices across those compositions | 7,296 |
| Two disjoint winning sets in the eleven-variable example | Verified (`true`) |

The four composition cases have the following expected summaries:

| Inner functions | Dimension | Vertices | Mixture terms | Mean |
| --- | ---: | ---: | ---: | ---: |
| Seven coordinate functions | 7 | 128 | 1 | `0` |
| Four-variable path, conjunction, five coordinates | 11 | 2,048 | 4 | `-9/64` |
| Four-variable path, two conjunctions, four coordinates | 12 | 4,096 | 8 | `-9/32` |
| Conjunction, four-variable path, constant `-1`, four coordinates | 10 | 1,024 | 4 | `-27/64` |

## What is checked

The verifier independently constructs exact rational polar witnesses for all 128 lower sections of the Fano upset, using an integer-capacity flow computation. It checks the corresponding **2,187 pointwise codifferential identities** and the bottom-minimum conditions.

For each of the four compositions, it also checks the inner-function witnesses and affine replacements, the multiaffine mixture identity, the telescoping decomposition and divergence, nonnegativity and bottom-zero values of the remainder, the final cochain's own-coordinate independence and minimum conditions, and correct centering. These checks cover all **7,296 composition vertices**. The program verifies the two disjoint winning sets used to demonstrate that one output is not intersecting.

## Scope and limitations

These are finite, exact computations supporting the examples in the preprint. They do **not** establish the dimension-free substitution theorem, Cary's Conjecture 5.3, or Keevash's Theorem 1.1 in general. Those conclusions depend on the mathematical arguments and, for the final application, on the cited theorem of Keevash.

The computation is not a proof-assistant formalization and does not constitute independent human peer review. No previously recorded certificate is needed as input: the section witnesses are constructed during execution.

## Mathematical references

- Jonathan Cary, *On Kleitman's Conjecture*, [arXiv:2402.03150v5](https://arxiv.org/abs/2402.03150v5), especially Conjectures 4.1 and 5.3.
- Peter Keevash, *On Kahn's flow conjecture*, [arXiv:2609.23595v1](https://arxiv.org/abs/2609.23595v1), Theorem 1.1.
