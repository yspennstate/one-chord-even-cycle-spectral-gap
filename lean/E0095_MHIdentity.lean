import Mathlib

/-!
# E0095: the edge sum in the Metropolis bound

Test function f(i) = cos(θ (i - k/2)) on the cycle, θ = 2π/n, α = π k/n, so f(0) = f(k) = cos α,
f(±1) = cos(θ ∓ α) and, by symmetry, the same at k ∓ 1. The four cycle edges at the chord ends
contribute twice [(f(1) - f(0))^2 + (f(-1) - f(0))^2], which equals 4 [a^2 cos^2 α + sin^2 θ sin^2 α]
with a = 1 - cos θ.
-/

namespace E0095

open Real

theorem edge_sum (θ α : ℝ) :
    2 * ((cos (θ - α) - cos α) ^ 2 + (cos (θ + α) - cos α) ^ 2)
      = 4 * ((1 - cos θ) ^ 2 * cos α ^ 2 + sin θ ^ 2 * sin α ^ 2) := by
  rw [cos_sub, cos_add]
  ring

/-- The antipodal chord's energy beats the odd-sector bound: 4 w s^2 ≥ 2 a w s^2 with a = 1 - cos θ ≤ 2. -/
theorem chord_energy (θ w s : ℝ) (hw : 0 ≤ w) :
    2 * (1 - cos θ) * w * s ^ 2 ≤ 4 * w * s ^ 2 := by
  have h1 : -1 ≤ cos θ := neg_one_le_cos θ
  have hws : 0 ≤ w * s ^ 2 := mul_nonneg hw (sq_nonneg s)
  nlinarith

end E0095

#print axioms E0095.edge_sum
#print axioms E0095.chord_energy
