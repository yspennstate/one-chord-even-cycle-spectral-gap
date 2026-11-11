# Lean checks for the E0095 paper

Two files, Lean 4 with Mathlib.

## `E0095_PathLemma.lean`: the path lemma (Lemma 3, used in the proof of Theorem 1)

- `path_dirichlet`: for every m and every real sequence f with f(0) = f(m) = 0,
  (2 - 2 cos(π/m)) Σ_{i ≤ m} f(i)^2 ≤ Σ_{i < m} (f(i) - f(i+1))^2.
- `path_dirichlet_sin_eq`: equality holds for f(i) = sin(πi/m), m > 0.

Since 2a = 2 - 2 cos(π/m) and f vanishes at both ends, this is the lemma as stated in the paper. The proof is Picone's
identity with the positive ground state s(i) = sin(πi/m): `vertex_sum` regroups the terms by vertex, where the
recurrence s(i-1) + s(i+1) = 2 cos(π/m) s(i) gives each interior vertex the contribution λ f(i)^2, and `edge_bound`
bounds each edge by (f(i) - f(i+1))^2, the difference being (a s_b - b s_a)^2 / (s_a s_b) ≥ 0.

## `E0095_MHIdentity.lean`: two algebraic steps in the proof of Theorem 2

- `edge_sum`: for the test function f(i) = cos(θ(i - k/2)), the four cycle edges at the ends of the chord contribute
  2[(cos(θ-α) - cos α)^2 + (cos(θ+α) - cos α)^2] = 4[(1 - cos θ)^2 cos^2 α + sin^2 θ sin^2 α].
  Proof: expand cos(θ ∓ α) and `ring`.
- `chord_energy`: for w ≥ 0, 2(1 - cos θ) w s^2 ≤ 4 w s^2, since cos θ ≥ -1.

## Building

`lake env lean <file>` inside a Mathlib project (Lean 4.33.1). `E0095_PathLemma.out` is the compiler output for the
path lemma: no errors, no `sorry`, and both theorems depend only on propext, Classical.choice and Quot.sound. The two
theorems of `E0095_MHIdentity.lean` depend on the same three axioms.

Scope: the spectral-gap statements themselves, the variational characterisation and the choice of test function are
not formalised here.
