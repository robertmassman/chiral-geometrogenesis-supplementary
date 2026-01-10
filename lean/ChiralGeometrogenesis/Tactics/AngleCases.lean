/-
  ChiralGeometrogenesis/Tactics/AngleCases.lean

  Case analysis tactics for trigonometric equations.

  This module automates the common pattern of case-splitting on
  sin α = sin β or cos α = cos β equations, bounding the integer
  parameter using interval constraints.

  ## Mathematical Background

  From Mathlib (Analysis.SpecialFunctions.Trigonometric.Complex), we have:
  - `Real.sin_eq_sin_iff`: sin x = sin y ↔ ∃ k : ℤ, y = 2kπ + x ∨ y = (2k+1)π - x
  - `Real.cos_eq_cos_iff`: cos x = cos y ↔ ∃ k : ℤ, y = 2kπ + x ∨ y = 2kπ - x

  Note: The Mathlib form expresses y in terms of x. Our `sin_eq_cases` and
  `cos_eq_cases` theorems rearrange this to express α in terms of β.

  The key challenge is that k ranges over all integers. When we know
  x, y are in bounded intervals (e.g., [0, 2π)), we can narrow k to
  a finite set of values.

  ## Typical Proof Pattern

  For the trefoil injectivity proof:
  1. From sin(6πs) = sin(6πt) with s, t ∈ [0, 1)
  2. Either 6πs = 6πt + 2πk or 6πs = π - 6πt + 2πk
  3. Case 1: s - t = k/3, with s, t ∈ [0, 1) means k ∈ {-2, -1, 0, 1, 2}
  4. Case 2: s + t = (1 + 2k)/6, with s, t ∈ [0, 2) means k ∈ {0, 1, 2, 3, 4, 5}

  This module provides lemmas and tactics to automate this pattern.
-/

import ChiralGeometrogenesis.Tactics.TrigSimplify

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Tactics

open Real

/-! ## Core Case Split Lemmas

These lemmas restate Mathlib's angle equality characterizations in
forms that are easier to work with.
-/

/-- **Sine Equality Cases**

If sin α = sin β, then either:
- α = β + 2πk for some integer k (same angle modulo 2π), or
- α = π - β + 2πk for some integer k (supplementary angles)

This is `Real.sin_eq_sin_iff` rearranged. Mathlib gives:
  sin x = sin y ↔ ∃ k : ℤ, y = 2kπ + x ∨ y = (2k+1)π - x

We rearrange to express α (the first argument) in terms of β (the second).
-/
theorem sin_eq_cases {α β : ℝ} (h : sin α = sin β) :
    (∃ k : ℤ, α = β + 2 * π * k) ∨ (∃ k : ℤ, α = π - β + 2 * π * k) := by
  rw [sin_eq_sin_iff] at h
  -- h : ∃ k, β = 2kπ + α ∨ β = (2k+1)π - α
  obtain ⟨k, hk | hk⟩ := h
  · -- β = 2kπ + α, so α = β - 2kπ = β + 2π(-k)
    left
    use -k
    simp only [Int.cast_neg]
    linarith
  · -- β = (2k+1)π - α, so α = (2k+1)π - β = π - β + 2kπ
    right
    use k
    linarith

/-- **Cosine Equality Cases**

If cos α = cos β, then either:
- α = β + 2πk for some integer k (same angle modulo 2π), or
- α = -β + 2πk for some integer k (opposite angles)
-/
theorem cos_eq_cases {α β : ℝ} (h : cos α = cos β) :
    (∃ k : ℤ, α = β + 2 * π * k) ∨ (∃ k : ℤ, α = -β + 2 * π * k) := by
  rw [cos_eq_cos_iff] at h
  -- h : ∃ k, β = 2kπ + α ∨ β = 2kπ - α
  obtain ⟨k, hk | hk⟩ := h
  · -- β = 2kπ + α, so α = β - 2kπ = β + 2π(-k)
    left
    use -k
    simp only [Int.cast_neg]
    linarith
  · -- β = 2kπ - α, so α = 2kπ - β = -β + 2kπ
    right
    use k
    linarith

/-! ## Integer Bounding Lemmas

When we know the angles lie in bounded intervals, we can constrain k.
-/

/-- If s, t ∈ [0, 1) and 3(s - t) = k, then k ∈ {-2, -1, 0, 1, 2} -/
theorem bound_k_from_diff {s t : ℝ} {k : ℤ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (heq : s - t = k / 3) :
    k ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
  -- s - t ∈ (-1, 1), so k/3 ∈ (-1, 1), meaning k ∈ {-2, -1, 0, 1, 2}
  have h1 : s - t > -1 := by linarith [hs.1, ht.2]
  have h2 : s - t < 1 := by linarith [hs.2, ht.1]
  have h3 : (k : ℝ) / 3 > -1 := by rw [← heq]; exact h1
  have h4 : (k : ℝ) / 3 < 1 := by rw [← heq]; exact h2
  have h5 : (k : ℝ) > -3 := by linarith
  have h6 : (k : ℝ) < 3 := by linarith
  have hk_gt : k > -3 := by exact_mod_cast h5
  have hk_lt : k < 3 := by exact_mod_cast h6
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- If s, t ∈ [0, 1) and s + t = (1 + 2k)/6, then k ∈ {0, 1, 2, 3, 4, 5}

This is the tight bound. Since s, t ≥ 0, we have s + t ≥ 0.
From s + t = (1 + 2k)/6 ≥ 0, we get 1 + 2k ≥ 0, so k ≥ -1/2, hence k ≥ 0 for integers.
Since s, t < 1, we have s + t < 2, so (1 + 2k)/6 < 2, giving k < 5.5, hence k ≤ 5.
-/
theorem bound_k_from_sum {s t : ℝ} {k : ℤ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (heq : s + t = (1 + 2 * k) / 6) :
    k ∈ ({0, 1, 2, 3, 4, 5} : Set ℤ) := by
  -- s + t ∈ [0, 2), so (1 + 2k)/6 ∈ [0, 2), meaning 1 + 2k ∈ [0, 12)
  have h1 : s + t ≥ 0 := by linarith [hs.1, ht.1]
  have h2 : s + t < 2 := by linarith [hs.2, ht.2]
  have h3 : (1 + 2 * k : ℝ) / 6 ≥ 0 := by rw [← heq]; exact h1
  have h4 : (1 + 2 * k : ℝ) / 6 < 2 := by rw [← heq]; exact h2
  have h5 : (1 + 2 * k : ℝ) ≥ 0 := by linarith
  have h6 : (1 + 2 * k : ℝ) < 12 := by linarith
  have hk_lo : (2 : ℝ) * k ≥ -1 := by linarith
  have hk_hi : (2 : ℝ) * k < 11 := by linarith
  -- From 2k ≥ -1 and k : ℤ, we get k ≥ 0 (since 2k = -1 has no integer solution)
  have hk_lo' : k ≥ 0 := by
    by_contra h_neg
    push_neg at h_neg
    have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h_neg
    have : (2 : ℝ) * k ≤ -2 := by linarith
    linarith
  have hk_hi' : k ≤ 5 := by
    by_contra h_big
    push_neg at h_big
    have : (k : ℝ) ≥ 6 := by exact_mod_cast h_big
    linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Specialized for the trefoil z-equation: if sin(6πs) = sin(6πt) with s,t ∈ [0,1)

From sin(6πs) = sin(6πt) we get two families of solutions:
- Difference case: s - t = k/3 for k ∈ {-2, -1, 0, 1, 2}
- Sum case: s + t = (1 + 2k)/6 for k ∈ {0, 1, 2, 3, 4, 5}

Note: The sum case excludes k = -1 because that would give s + t = -1/6 < 0,
which is impossible since s, t ≥ 0.
-/
theorem trefoil_z_cases {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : sin (6 * π * s) = sin (6 * π * t)) :
    (∃ k : ℤ, k ∈ ({-2, -1, 0, 1, 2} : Set ℤ) ∧ s - t = k / 3) ∨
    (∃ k : ℤ, k ∈ ({0, 1, 2, 3, 4, 5} : Set ℤ) ∧ s + t = (1 + 2 * k) / 6) := by
  rw [sin_eq_sin_iff] at h
  -- h : ∃ k, 6πt = 2kπ + 6πs ∨ 6πt = (2k+1)π - 6πs
  obtain ⟨k, hk | hk⟩ := h
  · -- Case 1: 6πt = 2kπ + 6πs, so s - t = -k/3
    left
    have h1 : s - t = (-k : ℤ) / 3 := by
      have hpi : π ≠ 0 := pi_ne_zero
      simp only [Int.cast_neg]
      field_simp at hk ⊢
      linarith
    use -k
    constructor
    · -- Show -k ∈ {-2, -1, 0, 1, 2}
      have h1' : s - t = ((-k) : ℤ) / 3 := h1
      have hmem := bound_k_from_diff hs ht h1'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
      exact hmem
    · exact h1
  · -- Case 2: 6πt = (2k+1)π - 6πs, so s + t = (1 + 2k)/6
    right
    have h1 : s + t = (1 + 2 * k) / 6 := by
      have hpi : π ≠ 0 := pi_ne_zero
      field_simp at hk ⊢
      linarith
    exact ⟨k, bound_k_from_sum hs ht h1, h1⟩

/-! ## Specific Case Lemmas for Trefoil

Each case leads to specific constraints that can be individually analyzed.
-/

/-- Case k = 0 in difference: s = t -/
theorem trefoil_diff_case_0 {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s - t = 0) : s = t := by linarith

/-- Case k = 1 in difference: s = t + 1/3 -/
theorem trefoil_diff_case_1 {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s - t = 1 / 3) : s = t + 1 / 3 := by linarith

/-- Case k = -1 in difference: s = t - 1/3 -/
theorem trefoil_diff_case_neg1 {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s - t = -1 / 3) : s = t - 1 / 3 := by linarith

/-- Case k = 2 in difference: s = t + 2/3 -/
theorem trefoil_diff_case_2 {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s - t = 2 / 3) : s = t + 2 / 3 := by linarith

/-- Case k = -2 in difference: s = t - 2/3 -/
theorem trefoil_diff_case_neg2 {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s - t = -2 / 3) : s = t - 2 / 3 := by linarith

/-! ## Constraint Propagation

When we fix s - t or s + t, we can derive constraints on cos(2πs) and cos(2πt).
-/

/-- If s = t + 1/3, then cos(2πs) relates to cos(2πt) via 120° rotation -/
theorem cos_shift_by_third {s t : ℝ} (h : s = t + 1 / 3) :
    cos (2 * π * s) = cos (2 * π * t + 2 * π / 3) := by
  rw [h]
  ring_nf

/-- If s = t + 1/3, then sin(2πs) relates to sin(2πt) via 120° rotation -/
theorem sin_shift_by_third {s t : ℝ} (h : s = t + 1 / 3) :
    sin (2 * π * s) = sin (2 * π * t + 2 * π / 3) := by
  rw [h]
  ring_nf

/-- If s = t + 2/3, then cos(2πs) relates to cos(2πt) via 240° rotation -/
theorem cos_shift_by_two_thirds {s t : ℝ} (h : s = t + 2 / 3) :
    cos (2 * π * s) = cos (2 * π * t + 4 * π / 3) := by
  rw [h]
  ring_nf

/-- If s = t + 2/3, then sin(2πs) relates to sin(2πt) via 240° rotation -/
theorem sin_shift_by_two_thirds {s t : ℝ} (h : s = t + 2 / 3) :
    sin (2 * π * s) = sin (2 * π * t + 4 * π / 3) := by
  rw [h]
  ring_nf

/-- If s = t - 1/3, then cos(2πs) relates to cos(2πt) via -120° rotation -/
theorem cos_shift_by_neg_third {s t : ℝ} (h : s = t - 1 / 3) :
    cos (2 * π * s) = cos (2 * π * t - 2 * π / 3) := by
  rw [h]
  ring_nf

/-- If s = t - 1/3, then sin(2πs) relates to sin(2πt) via -120° rotation -/
theorem sin_shift_by_neg_third {s t : ℝ} (h : s = t - 1 / 3) :
    sin (2 * π * s) = sin (2 * π * t - 2 * π / 3) := by
  rw [h]
  ring_nf

/-- If s = t - 2/3, then cos(2πs) relates to cos(2πt) via -240° rotation -/
theorem cos_shift_by_neg_two_thirds {s t : ℝ} (h : s = t - 2 / 3) :
    cos (2 * π * s) = cos (2 * π * t - 4 * π / 3) := by
  rw [h]
  ring_nf

/-- If s = t - 2/3, then sin(2πs) relates to sin(2πt) via -240° rotation -/
theorem sin_shift_by_neg_two_thirds {s t : ℝ} (h : s = t - 2 / 3) :
    sin (2 * π * s) = sin (2 * π * t - 4 * π / 3) := by
  rw [h]
  ring_nf

/-! ## The `angle_cases` Tactic

A macro that applies the case split from a trigonometric equation.

The `angle_cases` tactic splits on a sin or cos equality hypothesis.

Usage:
```lean
example {s t : ℝ} (hs : s ∈ Set.Ico 0 1) (ht : t ∈ Set.Ico 0 1)
    (h : sin (6 * π * s) = sin (6 * π * t)) : s = t ∨ ... := by
  angle_cases h hs ht
  case diff_0 => exact Or.inl rfl
  case diff_1 => ...
  ...
```

Note: Full tactic implementation would require Lean 4 meta-programming.
For now, we provide helper lemmas that can be used manually.
-/

/-- Helper to split into all cases from trefoil z-equation

This provides 11 genuinely reachable cases (5 difference + 6 sum cases).
The k = -1 sum case (s + t = -1/6) is excluded because it's impossible
when s, t ≥ 0.
-/
theorem trefoil_z_all_cases {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : sin (6 * π * s) = sin (6 * π * t))
    (P : Prop)
    (case_diff_0 : s - t = 0 → P)
    (case_diff_1 : s - t = 1 / 3 → P)
    (case_diff_neg1 : s - t = -1 / 3 → P)
    (case_diff_2 : s - t = 2 / 3 → P)
    (case_diff_neg2 : s - t = -2 / 3 → P)
    (case_sum_0 : s + t = 1 / 6 → P)
    (case_sum_1 : s + t = 1 / 2 → P)
    (case_sum_2 : s + t = 5 / 6 → P)
    (case_sum_3 : s + t = 7 / 6 → P)
    (case_sum_4 : s + t = 3 / 2 → P)
    (case_sum_5 : s + t = 11 / 6 → P) :
    P := by
  rcases trefoil_z_cases hs ht h with ⟨k, hk_mem, hk_eq⟩ | ⟨k, hk_mem, hk_eq⟩
  · -- Difference cases: k ∈ {-2, -1, 0, 1, 2}
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk_mem
    rcases hk_mem with rfl | rfl | rfl | rfl | rfl
    · exact case_diff_neg2 (by simp only [Int.cast_neg, Int.cast_ofNat] at hk_eq; linarith)
    · exact case_diff_neg1 (by simp only [Int.cast_neg, Int.cast_one] at hk_eq; linarith)
    · exact case_diff_0 (by simp only [Int.cast_zero, zero_div] at hk_eq; linarith)
    · exact case_diff_1 (by simp only [Int.cast_one] at hk_eq; linarith)
    · exact case_diff_2 (by simp only [Int.cast_ofNat] at hk_eq; linarith)
  · -- Sum cases: k ∈ {0, 1, 2, 3, 4, 5}
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk_mem
    rcases hk_mem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact case_sum_0 (by simp only [Int.cast_zero] at hk_eq; linarith)
    · exact case_sum_1 (by simp only [Int.cast_one] at hk_eq; linarith)
    · exact case_sum_2 (by simp only [Int.cast_ofNat] at hk_eq; linarith)
    · exact case_sum_3 (by simp only [Int.cast_ofNat] at hk_eq; linarith)
    · exact case_sum_4 (by simp only [Int.cast_ofNat] at hk_eq; linarith)
    · exact case_sum_5 (by simp only [Int.cast_ofNat] at hk_eq; linarith)

/-! ## Impossible Cases and Constraints

Some cases can be ruled out immediately from the interval constraints.
Others require additional equations (x, y coordinates) to eliminate.

### Cases excluded from `trefoil_z_cases`

The k = -1 sum case (s + t = -1/6) is excluded from `bound_k_from_sum` and
`trefoil_z_cases` because it's impossible when s, t ≥ 0. We keep the lemma
below as a standalone result for completeness.
-/

/-- k = -1 in sum is impossible: s + t = -1/6 < 0 but s, t ≥ 0

Note: This case is already excluded from `trefoil_z_cases` via the tight
bound in `bound_k_from_sum`. This lemma is provided for reference.
-/
theorem trefoil_sum_neg1_impossible {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s + t = -1 / 6) : False := by
  have : s + t ≥ 0 := by linarith [hs.1, ht.1]
  linarith

/-! ### Cases that require x,y equations to eliminate

The following sum cases are geometrically possible from the z-equation alone:
- k = 4: s + t = 3/2 (e.g., s = 0.75, t = 0.75)
- k = 5: s + t = 11/6 ≈ 1.83 (e.g., s ≈ 0.9, t ≈ 0.93)

These require the full trefoil x,y equations to derive contradictions.
-/

/-- k = 2 in difference requires t ≤ 1/3 for s to be in [0,1) -/
theorem trefoil_diff_2_constraint {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s - t = 2 / 3) : t < 1 / 3 := by
  have : s = t + 2/3 := by linarith
  have : t + 2/3 < 1 := by rw [← this]; exact hs.2
  linarith

/-- k = -2 in difference requires s ≤ 1/3 -/
theorem trefoil_diff_neg2_constraint {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (h : s - t = -2 / 3) : s < 1 / 3 := by
  have : t = s + 2/3 := by linarith
  have : s + 2/3 < 1 := by rw [← this]; exact ht.2
  linarith

end ChiralGeometrogenesis.Tactics
