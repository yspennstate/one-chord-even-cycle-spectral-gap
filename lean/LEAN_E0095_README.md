# E0095: two steps of the Metropolis bound checked in Lean

`E0095_MHIdentity.lean` (Lean 4 + Mathlib) proves two of the algebraic steps used in the E0095 argument.

- `edge_sum`: for the test function f(i) = cos(θ(i - k/2)), the four cycle edges at the ends of the chord contribute
  2[(cos(θ-α) - cos α)^2 + (cos(θ+α) - cos α)^2] = 4[(1 - cos θ)^2 cos^2 α + sin^2 θ sin^2 α].
  Proof: expand cos(θ ∓ α) and `ring`.
- `chord_energy`: for w ≥ 0, 2(1 - cos θ) w s^2 ≤ 4 w s^2, since cos θ ≥ -1.

Compiled with `lake env lean E0095_MHIdentity.lean`: rc=0. Both theorems depend only on propext, Classical.choice and
Quot.sound (`E0095_MHIdentity.out`).

Scope: these are the trigonometric identity and the chord comparison. The spectral-gap statement itself, the
variational characterisation and the choice of test function are not formalized here.
