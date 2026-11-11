import Mathlib

/-!
# The path lemma of "Which chord of an even cycle preserves its spectral gap"

For a sequence `f` with `f 0 = 0` and `f m = 0`,
`(2 - 2 cos (π / m)) * Σ_{i ≤ m} f i ^ 2 ≤ Σ_{i < m} (f i - f (i+1)) ^ 2`,
with equality for `f i = sin (π i / m)`. So `2 - 2 cos (π / m)` is the smallest eigenvalue of the path
matrix on the `m - 1` interior vertices with zero boundary values. The proof is Picone's identity with
the positive ground state `sin (π i / m)`.
-/

open Finset Real

namespace E0095Path

/-- One edge: `(a - b)^2` dominates `a^2 + b^2 - (a^2 / sa) * sb - (b^2 / sb) * sa`
when the weights are nonnegative and a zero weight carries a zero value. -/
lemma edge_bound (a b sa sb : ℝ) (hsa : 0 ≤ sa) (hsb : 0 ≤ sb)
    (ha : sa = 0 → a = 0) (hb : sb = 0 → b = 0) :
    a ^ 2 + b ^ 2 - a ^ 2 / sa * sb - b ^ 2 / sb * sa ≤ (a - b) ^ 2 := by
  by_cases h1 : sa = 0
  · have h2 := ha h1
    subst h2; subst h1
    simp
  by_cases h3 : sb = 0
  · have h4 := hb h3
    subst h4; subst h3
    simp
  have hpa : 0 < sa := lt_of_le_of_ne hsa (Ne.symm h1)
  have hpb : 0 < sb := lt_of_le_of_ne hsb (Ne.symm h3)
  have key : a ^ 2 / sa * sb + b ^ 2 / sb * sa - 2 * a * b = (a * sb - b * sa) ^ 2 / (sa * sb) := by
    field_simp
    ring
  have hnn : 0 ≤ (a * sb - b * sa) ^ 2 / (sa * sb) := div_nonneg (sq_nonneg _) (mul_pos hpa hpb).le
  nlinarith [key, hnn]

lemma sq_div_self_mul (x y : ℝ) : x ^ 2 / x * y = x * y := by
  by_cases hx : x = 0
  · subst hx; simp
  · field_simp

/-- The half-edge terms of Picone's identity. -/
noncomputable def Aterm (f s : ℕ → ℝ) (i : ℕ) : ℝ := f i ^ 2 - f i ^ 2 / s i * s (i + 1)
noncomputable def Bterm (f s : ℕ → ℝ) (i : ℕ) : ℝ := f i ^ 2 - f i ^ 2 / s i * s (i - 1)

/-- Regrouping the half-edge terms by vertex: each interior vertex contributes `lam * f i ^ 2`. -/
theorem vertex_sum (m : ℕ) (f s : ℕ → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < i → i < m → 0 < s i)
    (hrec : ∀ i, 0 < i → i < m → s (i - 1) + s (i + 1) = (2 - lam) * s i)
    (hf0 : f 0 = 0) (hfm : f m = 0) :
    lam * ∑ i ∈ range (m + 1), f i ^ 2 = ∑ i ∈ range m, (Aterm f s i + Bterm f s (i + 1)) := by
  have hAm : Aterm f s m = 0 := by simp [Aterm, hfm]
  have hB0 : Bterm f s 0 = 0 := by simp [Bterm, hf0]
  have hsplit : ∑ i ∈ range m, (Aterm f s i + Bterm f s (i + 1)) =
      ∑ i ∈ range (m + 1), (Aterm f s i + Bterm f s i) := by
    rw [sum_add_distrib, sum_add_distrib, sum_range_succ (Aterm f s), hAm,
      sum_range_succ' (Bterm f s), hB0]
    ring
  have hvert : ∀ i ∈ range (m + 1), lam * f i ^ 2 = Aterm f s i + Bterm f s i := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [Aterm, Bterm, hf0]
    rcases Nat.lt_or_ge i m with h' | h'
    · have hsi := hpos i h h'
      have hr := hrec i h h'
      simp only [Aterm, Bterm]
      have e1 : f i ^ 2 / s i * s (i + 1) + f i ^ 2 / s i * s (i - 1) =
          f i ^ 2 / s i * ((2 - lam) * s i) := by
        rw [← hr]; ring
      have e2 : f i ^ 2 / s i * ((2 - lam) * s i) = (2 - lam) * f i ^ 2 := by
        field_simp
      linarith
    · have hi' : i = m := le_antisymm him h'
      subst hi'; simp [Aterm, Bterm, hfm]
  rw [hsplit, mul_sum]
  exact sum_congr rfl hvert

/-- Picone's bound for a positive solution `s` of `s (i-1) + s (i+1) = (2 - lam) s i`
vanishing at `0` and `m`. -/
theorem path_bound (m : ℕ) (f s : ℕ → ℝ) (lam : ℝ)
    (hs0 : s 0 = 0) (hsm : s m = 0) (hpos : ∀ i, 0 < i → i < m → 0 < s i)
    (hrec : ∀ i, 0 < i → i < m → s (i - 1) + s (i + 1) = (2 - lam) * s i)
    (hf0 : f 0 = 0) (hfm : f m = 0) :
    lam * ∑ i ∈ range (m + 1), f i ^ 2 ≤ ∑ i ∈ range m, (f i - f (i + 1)) ^ 2 := by
  have hsnn : ∀ i, i ≤ m → 0 ≤ s i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, hs0]
    rcases Nat.lt_or_ge i m with h' | h'
    · exact (hpos i h h').le
    · rw [le_antisymm hi h', hsm]
  have hzero : ∀ i, i ≤ m → s i = 0 → f i = 0 := by
    intro i hi hsi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, hf0]
    rcases Nat.lt_or_ge i m with h' | h'
    · exact absurd hsi (hpos i h h').ne'
    · rw [le_antisymm hi h', hfm]
  rw [vertex_sum m f s lam hpos hrec hf0 hfm]
  apply sum_le_sum
  intro i hi
  have him : i < m := mem_range.mp hi
  have e := edge_bound (f i) (f (i + 1)) (s i) (s (i + 1)) (hsnn i him.le) (hsnn (i + 1) him)
    (hzero i him.le) (hzero (i + 1) him)
  simp only [Aterm, Bterm, Nat.add_sub_cancel]
  linarith

/-- With `f = s` the bound is an equality. -/
theorem path_bound_eq (m : ℕ) (s : ℕ → ℝ) (lam : ℝ)
    (hs0 : s 0 = 0) (hsm : s m = 0) (hpos : ∀ i, 0 < i → i < m → 0 < s i)
    (hrec : ∀ i, 0 < i → i < m → s (i - 1) + s (i + 1) = (2 - lam) * s i) :
    lam * ∑ i ∈ range (m + 1), s i ^ 2 = ∑ i ∈ range m, (s i - s (i + 1)) ^ 2 := by
  rw [vertex_sum m s s lam hpos hrec hs0 hsm]
  apply sum_congr rfl
  intro i _
  simp only [Aterm, Bterm, Nat.add_sub_cancel, sq_div_self_mul]
  ring

/-- The sine sequence satisfies the hypotheses with `lam = 2 - 2 cos (π / m)`. -/
lemma sin_hyps (m : ℕ) (hm : 0 < m) :
    let s : ℕ → ℝ := fun i => sin (π * i / m)
    s 0 = 0 ∧ s m = 0 ∧ (∀ i, 0 < i → i < m → 0 < s i) ∧
      (∀ i, 0 < i → i < m → s (i - 1) + s (i + 1) = (2 - (2 - 2 * cos (π / m))) * s i) := by
  intro s
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [s]
  · simp only [s]
    rw [mul_div_assoc, div_self hmR.ne', mul_one, sin_pi]
  · intro i hi him
    have hiR : (0 : ℝ) < i := by exact_mod_cast hi
    have himR : (i : ℝ) < m := by exact_mod_cast him
    simp only [s]
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hmR]; nlinarith [pi_pos]
  · intro i hi _
    simp only [s]
    have hc : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have e1 : π * ((i - 1 : ℕ) : ℝ) / m = π * i / m - π / m := by rw [hc]; ring
    have e2 : π * ((i + 1 : ℕ) : ℝ) / m = π * i / m + π / m := by push_cast; ring
    rw [e1, e2, sin_sub, sin_add]
    ring

/-- Lemma path of the paper, lower bound. -/
theorem path_dirichlet (m : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0) (hfm : f m = 0) :
    (2 - 2 * cos (π / m)) * ∑ i ∈ range (m + 1), f i ^ 2 ≤ ∑ i ∈ range m, (f i - f (i + 1)) ^ 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [hf0]
  obtain ⟨h0, h1, h2, h3⟩ := sin_hyps m hm
  exact path_bound m f _ _ h0 h1 h2 h3 hf0 hfm

/-- Lemma path of the paper, attainment: equality for `f i = sin (π i / m)`. -/
theorem path_dirichlet_sin_eq (m : ℕ) (hm : 0 < m) :
    (2 - 2 * cos (π / m)) * ∑ i ∈ range (m + 1), sin (π * i / m) ^ 2 =
      ∑ i ∈ range m, (sin (π * i / m) - sin (π * ((i + 1 : ℕ) : ℝ) / m)) ^ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := sin_hyps m hm
  exact path_bound_eq m (fun i => sin (π * i / m)) _ h0 h1 h2 h3

end E0095Path

#print axioms E0095Path.path_dirichlet
#print axioms E0095Path.path_dirichlet_sin_eq
