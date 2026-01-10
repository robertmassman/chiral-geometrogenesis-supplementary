/-
  ChiralGeometrogenesis/Tactics/Basic.lean

  Core utilities and imports for the custom tactic library.

  This module provides foundational lemmas and imports shared across
  all tactic modules in the ChiralGeometrogenesis framework.

  ## Purpose

  The theory of Chiral Geometrogenesis involves unique mathematical structures:
  - 120° phase separations (SU(3) root system geometry)
  - Coupled oscillator dynamics (Sakaguchi-Kuramoto model)
  - Topological knot invariants (trefoil injectivity)

  Standard Lean/Mathlib tactics cannot fully handle these domains because:
  - `nlinarith` works on polynomial inequalities but NOT transcendental functions
  - No existing tactic automates angle arithmetic or trig identity chains
  - Interval arithmetic for irrational bounds requires custom infrastructure

  This library fills those gaps.

  ## Module Structure

  ```
  Tactics/
  ├── Basic.lean           -- This file: core utilities
  ├── TrigSimplify.lean    -- Trigonometric identity automation
  ├── AngleCases.lean      -- Case analysis for sin/cos equations
  ├── IntervalArith.lean   -- Interval containment proofs
  ├── Phase120.lean        -- SU(3) phase dynamics
  └── Prelude.lean         -- Export all tactics
  ```
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Tactics

open Real

/-! ## π Bounds

Precise rational bounds for π that can be used in interval arithmetic.
-/

/-- Lower bound: π > 3.14 (from Mathlib) -/
lemma pi_gt_314 : π > 3.14 := pi_gt_d2

/-- Upper bound: π < 3.15 (from Mathlib) -/
lemma pi_lt_315 : π < 3.15 := pi_lt_d2

/-- π/3 bounds: 1.04 < π/3 < 1.05 -/
lemma pi_div_3_bounds : 1.04 < π / 3 ∧ π / 3 < 1.05 := by
  constructor
  · have h := pi_gt_314
    linarith
  · have h := pi_lt_315
    linarith

/-- 2π/3 bounds: 2.09 < 2π/3 < 2.1 -/
lemma two_pi_div_3_bounds : 2.09 < 2 * π / 3 ∧ 2 * π / 3 < 2.1 := by
  constructor
  · have h := pi_gt_314
    linarith
  · have h := pi_lt_315
    linarith

/-- 4π/3 bounds: 4.18 < 4π/3 < 4.2 -/
lemma four_pi_div_3_bounds : 4.18 < 4 * π / 3 ∧ 4 * π / 3 < 4.2 := by
  constructor
  · have h := pi_gt_314
    linarith
  · have h := pi_lt_315
    linarith

/-! ## √3 Properties

Bounds and properties for √3, which appears throughout SU(3) calculations.
-/

/-- √3 is positive -/
lemma sqrt3_pos : sqrt 3 > 0 := sqrt_pos.mpr (by norm_num)

/-- √3 squared equals 3 -/
lemma sqrt3_sq : sqrt 3 ^ 2 = 3 := sq_sqrt (by norm_num : (3:ℝ) ≥ 0)

/-- √3 is not zero -/
lemma sqrt3_ne_zero : sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos

/-- √3 bounds: 1.732 < √3 < 1.733 -/
lemma sqrt3_bounds : 1.732 < sqrt 3 ∧ sqrt 3 < 1.733 := by
  constructor
  · have h : (1.732 : ℝ)^2 < 3 := by norm_num
    have h2 : sqrt ((1.732 : ℝ)^2) < sqrt 3 := sqrt_lt_sqrt (by norm_num) h
    simp only [sqrt_sq (by norm_num : (1.732 : ℝ) ≥ 0)] at h2
    exact h2
  · have h : (3 : ℝ) < (1.733 : ℝ)^2 := by norm_num
    have h2 : sqrt 3 < sqrt ((1.733 : ℝ)^2) := sqrt_lt_sqrt (by norm_num) h
    simp only [sqrt_sq (by norm_num : (1.733 : ℝ) ≥ 0)] at h2
    exact h2

/-- √3/2 bounds: 0.866 < √3/2 < 0.867 -/
lemma sqrt3_div_2_bounds : 0.866 < sqrt 3 / 2 ∧ sqrt 3 / 2 < 0.867 := by
  have ⟨h1, h2⟩ := sqrt3_bounds
  constructor <;> linarith

/-! ## √33 Properties

Bounds for √33, which appears in the trefoil injectivity proof.
The trefoil quartic equation 4cos²α - cos α - 2 = 0 has roots (1 ± √33)/8.
-/

/-- √33 is positive -/
lemma sqrt33_pos : sqrt 33 > 0 := sqrt_pos.mpr (by norm_num)

/-- √33 squared equals 33 -/
lemma sqrt33_sq : sqrt 33 ^ 2 = 33 := sq_sqrt (by norm_num : (33:ℝ) ≥ 0)

/-- √33 is not zero -/
lemma sqrt33_ne_zero : sqrt 33 ≠ 0 := ne_of_gt sqrt33_pos

/-- √33 bounds: 5.744 < √33 < 5.745 -/
lemma sqrt33_bounds : 5.744 < sqrt 33 ∧ sqrt 33 < 5.745 := by
  constructor
  · have h : (5.744 : ℝ)^2 < 33 := by norm_num
    have h2 : sqrt ((5.744 : ℝ)^2) < sqrt 33 := sqrt_lt_sqrt (by norm_num) h
    simp only [sqrt_sq (by norm_num : (5.744 : ℝ) ≥ 0)] at h2
    exact h2
  · have h : (33 : ℝ) < (5.745 : ℝ)^2 := by norm_num
    have h2 : sqrt 33 < sqrt ((5.745 : ℝ)^2) := sqrt_lt_sqrt (by norm_num) h
    simp only [sqrt_sq (by norm_num : (5.745 : ℝ) ≥ 0)] at h2
    exact h2

/-- (1 + √33)/8 bounds (positive root of trefoil quartic)

The trefoil quartic 4x² - x - 2 = 0 has positive root x = (1 + √33)/8 ≈ 0.843.
This value is in the valid range for cos α when α ∈ [0, π/3].
-/
lemma quartic_root_bounds : 0.842 < (1 + sqrt 33) / 8 ∧ (1 + sqrt 33) / 8 < 0.844 := by
  have ⟨h1, h2⟩ := sqrt33_bounds
  constructor <;> linarith

/-- (1 - √33)/8 bounds (negative root of trefoil quartic)

The trefoil quartic 4x² - x - 2 = 0 has negative root x = (1 - √33)/8 ≈ -0.593.
This value is in the valid range for cos α when α ∈ [2π/3, π].
-/
lemma quartic_neg_root_bounds : -0.594 < (1 - sqrt 33) / 8 ∧ (1 - sqrt 33) / 8 < -0.592 := by
  have ⟨h1, h2⟩ := sqrt33_bounds
  constructor <;> linarith

/-! ## Angle Conversion Helpers

Convert between different angle representations.
-/

/-- 2π is positive -/
lemma two_pi_pos : 2 * π > 0 := by positivity

/-- 2π is not zero -/
lemma two_pi_ne_zero : 2 * π ≠ 0 := ne_of_gt two_pi_pos

/-- Conversion: t ∈ [0, 1) corresponds to θ = 2πt ∈ [0, 2π) -/
lemma angle_in_circle {t : ℝ} (ht_lo : 0 ≤ t) (ht_hi : t < 1) :
    0 ≤ 2 * π * t ∧ 2 * π * t < 2 * π := by
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt pi_pos)) ht_lo
  · have h1 : 2 * π * t < 2 * π * 1 := by
      apply mul_lt_mul_of_pos_left ht_hi
      exact two_pi_pos
    simp only [mul_one] at h1
    exact h1

/-! ## Integer Bounding Lemmas

For case analysis on angles, we often need to bound integer parameters.
-/

/-- If x ∈ (-1, 1) and x = k for some integer k, then k = 0 -/
lemma int_in_open_unit_interval {k : ℤ} (h1 : -1 < (k : ℝ)) (h2 : (k : ℝ) < 1) : k = 0 := by
  have hk_ge : k ≥ 0 := by
    by_contra h
    push_neg at h
    have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
    linarith
  have hk_le : k ≤ 0 := by
    by_contra h
    push_neg at h
    have : (k : ℝ) ≥ 1 := by exact_mod_cast h
    linarith
  omega

/-- If x ∈ [0, 2) and x = k for some integer k, then k ∈ {0, 1} -/
lemma int_in_half_open_02 {k : ℤ} (h1 : 0 ≤ (k : ℝ)) (h2 : (k : ℝ) < 2) : k = 0 ∨ k = 1 := by
  have hk_ge : k ≥ 0 := by
    by_contra h
    push_neg at h
    have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
    linarith
  have hk_lt : k < 2 := by
    by_contra h
    push_neg at h
    have : (k : ℝ) ≥ 2 := by exact_mod_cast h
    linarith
  omega

/-- If x ∈ (-3, 3) and x = k for some integer k, then k ∈ {-2, -1, 0, 1, 2} -/
lemma int_in_open_interval_neg3_3 {k : ℤ} (h1 : -3 < (k : ℝ)) (h2 : (k : ℝ) < 3) :
    k ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hk_gt : k > -3 := by exact_mod_cast h1
  have hk_lt : k < 3 := by exact_mod_cast h2
  omega

end ChiralGeometrogenesis.Tactics
