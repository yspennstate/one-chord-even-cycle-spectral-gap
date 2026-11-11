# Which chord of an even cycle preserves its spectral gap

Paper and checking code for the following one-edge case of Question 4 in Diaconis, *Some things we've learned (about
Markov chain Monte Carlo)*, Section 5. Add one edge of conductance w > 0 to the cycle C_n, n = 2m >= 4.

- For the random walk on the new graph, the spectral gap is largest exactly when the edge is antipodal, and then it
  equals 1 - cos(pi/m), the gap of the cycle, for every w. Every other chord {0,k} strictly lowers the gap, to at most
  a / (1 + 2w cos^2(pi k/n) / (n + w)) with a = 1 - cos(pi/m).
- For the walk Metropolized to keep the uniform law, with the walk on the new graph as proposal, every chord, the
  antipodal one included, strictly lowers the gap.

The question for a whole perfect matching remains open.

- `paper/` - the paper (`main.tex`, `main.pdf`).
- `code/` - Python 3 with numpy, scipy and sympy.
  - `exact_matrix.py` - even n = 4..16, every chord, w in {1/2, 1, 5}: characteristic polynomials of the pencil
    (D - A) - xD in rational arithmetic and Sturm counts locating the second root. Writes `evidence/exact_matrix.json`.
  - `exact_paths.py` - the same 84 cases by eliminating the two path interiors, with its own Fraction-only Sturm
    sequences; compares every coefficient with `exact_matrix.json`. Writes `evidence/exact_paths.json`.
  - `metropolis.py` - the same 84 cases for the Metropolis kernel, exact. Writes `evidence/metropolis.json`.
  - `controls.py` - exact checks that the statements are sensitive to their hypotheses (lazy versus non-lazy gap,
    a matching on C_8 that helps at weight 1 and hurts at weight 10, the degree-variance identity).
  - `explore.py` - floating point, even n = 4..40, five weights from 0.01 to 1000. Writes `evidence/exploration.json`.
  - `numeric_check.py` - an independent floating-point check of both theorems' bounds and of the odd-cycle remark.
- `lean/` - Lean 4 with Mathlib: the four-edge identity and the chord comparison used in the proof of Theorem 2.
  The spectral statements themselves are not formalised.

Run the checks from the repository root, for example

    python code/exact_matrix.py
    python code/exact_paths.py

Funding, competing interests and the use of AI systems are declared at the end of the paper.
