/-
  ChiralGeometrogenesis/Tactics/Prelude.lean

  Unified import point for all custom tactics.

  This file re-exports all the tactics and lemmas from the Tactics module,
  allowing downstream files to simply write:

    import ChiralGeometrogenesis.Tactics.Prelude

  ## Available Tactics

  1. **trig_simp** (from TrigSimplify.lean):
     Simplifies trigonometric expressions using standard identities.
     ```lean
     example (θ : ℝ) : sin (2 * θ) = 2 * sin θ * cos θ := by trig_simp
     ```

  2. **trig_simp!** (from TrigSimplify.lean):
     Extended version that also applies 120° sum identities.
     ```lean
     example (θ : ℝ) : sin θ + sin (θ + 2*π/3) + sin (θ + 4*π/3) = 0 := by trig_simp!
     ```

  3. **interval_check** (from IntervalArith.lean):
     Proves interval containments using known bounds on √2, √3, √5, √33, π.
     ```lean
     example : sqrt 33 < 6 := by interval_check
     ```

  4. **phase120** (from Phase120.lean):
     Applies results about the SU(3) 120° phase separation.
     ```lean
     example (cfg : Phase120Config) : coupling_R cfg.φ_R cfg.φ_G cfg.φ_B = 0 := by phase120
     ```

  ## Available Lemma Sets

  ### From Basic.lean
  - `pi_gt_314`, `pi_lt_315` — Rational bounds for π (2 decimal places)
  - `sqrt3_bounds`, `sqrt33_bounds` — Bounds for square roots
  - `sqrt33_pos`, `sqrt33_sq`, `sqrt33_ne_zero` — √33 properties
  - `quartic_root_bounds`, `quartic_neg_root_bounds` — Trefoil quartic roots
  - `angle_in_circle` — Angle range preservation
  - `int_in_open_unit_interval`, `int_in_half_open_02`, `int_in_open_interval_neg3_3` — Integer bounding

  ### From TrigSimplify.lean
  - `sum_sin_120`, `sum_cos_120` — 120° sum identities
  - `sin_two_mul'`, `cos_two_mul_cos_sq` — Double angle formulas
  - `sin_three_mul'`, `cos_three_mul'` — Triple angle formulas
  - `sin_add_two_pi_int`, `cos_add_two_pi_int` — Periodicity
  - Special values: `sin_two_pi_div_three`, `cos_four_pi_div_three`, etc.
  - `trefoil_x_factored`, `trefoil_y_expanded` — Trefoil-specific

  ### From AngleCases.lean
  - `sin_eq_cases`, `cos_eq_cases` — Case splits from angle equations
  - `trefoil_z_cases` — Full case analysis for trefoil z-equation
  - `trefoil_z_all_cases` — Helper for exhaustive case analysis
  - Various constraint propagation lemmas

  ### From IntervalArith.lean
  - `sqrt2_bounds`, `sqrt5_bounds` — More square root bounds
  - `quartic_positive_root`, `quartic_negative_root` — Trefoil quartic roots
  - `quartic_positive_root_bounds`, `quartic_negative_root_bounds`
  - `arccos_of_quartic_root` — Arccos bounds

  ### From Phase120.lean
  - `Phase120Config` — Structure for 120° phase configuration
  - `coupling_R`, `coupling_G`, `coupling_B` — Kuramoto coupling terms
  - `all_couplings_vanish_at_equilibrium` — Equilibrium theorem
  - `JacobianAtEquilibrium` — Stability analysis structure
  - `asymptotically_stable` — Stability theorem
  - `complex_phase_sum_zero` — Complex representation

  ## Usage Example

  ```lean
  import ChiralGeometrogenesis.Tactics.Prelude

  open ChiralGeometrogenesis.Tactics

  -- Use trig simplification
  example (θ : ℝ) : Real.sin θ + Real.sin (θ + 2*Real.pi/3) + Real.sin (θ + 4*Real.pi/3) = 0 := by
    exact sum_sin_120 θ

  -- Use interval bounds
  example : Real.sqrt 33 > 5 := by
    have ⟨h, _⟩ := sqrt33_bounds
    linarith

  -- Use phase configuration
  example (cfg : Phase120Config) : cfg.φ_G - cfg.φ_R = 2 * Real.pi / 3 :=
    cfg.phase_diff_RG
  ```
-/

-- Import all tactic modules
import ChiralGeometrogenesis.Tactics.Basic
import ChiralGeometrogenesis.Tactics.TrigSimplify
import ChiralGeometrogenesis.Tactics.AngleCases
import ChiralGeometrogenesis.Tactics.IntervalArith
import ChiralGeometrogenesis.Tactics.Phase120

namespace ChiralGeometrogenesis.Tactics.Prelude

-- Re-export everything from the Tactics namespace
open ChiralGeometrogenesis.Tactics

/-! ## Convenience Aliases

Shorter names for commonly used results.
-/

-- From Basic
export ChiralGeometrogenesis.Tactics (
  pi_gt_314 pi_lt_315
  pi_div_3_bounds two_pi_div_3_bounds four_pi_div_3_bounds
  sqrt3_pos sqrt3_sq sqrt3_ne_zero sqrt3_bounds sqrt3_div_2_bounds
  sqrt33_pos sqrt33_sq sqrt33_ne_zero sqrt33_bounds
  quartic_root_bounds quartic_neg_root_bounds
  two_pi_pos two_pi_ne_zero
  angle_in_circle
  int_in_open_unit_interval int_in_half_open_02 int_in_open_interval_neg3_3
)

-- From TrigSimplify
export ChiralGeometrogenesis.Tactics (
  sum_sin_120 sum_cos_120
  sum_sin_120_general sum_cos_120_general
  sin_two_mul' cos_two_mul_cos_sq cos_two_mul_sin_sq
  sin_three_mul' cos_three_mul'
  sin_add_two_pi_int cos_add_two_pi_int
  sin_two_pi_int cos_two_pi_int
  sin_two_pi_div_three cos_two_pi_div_three
  sin_four_pi_div_three cos_four_pi_div_three
  sin_mul_cos cos_mul_sin cos_mul_cos sin_mul_sin
  trefoil_x_factored trefoil_y_expanded trefoil_z_constraint
)

-- From AngleCases
export ChiralGeometrogenesis.Tactics (
  sin_eq_cases cos_eq_cases
  bound_k_from_diff bound_k_from_sum
  trefoil_z_cases trefoil_z_all_cases
  trefoil_diff_case_0 trefoil_diff_case_1 trefoil_diff_case_neg1
  trefoil_diff_case_2 trefoil_diff_case_neg2
  cos_shift_by_third sin_shift_by_third
  cos_shift_by_two_thirds sin_shift_by_two_thirds
  trefoil_sum_neg1_impossible
  trefoil_diff_2_constraint trefoil_diff_neg2_constraint
)

-- From IntervalArith
export ChiralGeometrogenesis.Tactics (
  sqrt2_bounds sqrt5_bounds
  pi_gt_314159 pi_lt_3142 pi_gt_3_1415 pi_lt_3_1416
  quartic_positive_root quartic_negative_root
  quartic_positive_root_bounds quartic_negative_root_bounds
  positive_root_in_cos_range negative_root_outside_high_range
  arccos_of_quartic_root arccos_positive_root_lt_four_pi_div_three
  sin_sq_from_quartic_root sin_sq_bounds_from_quartic
)

-- From Phase120
export ChiralGeometrogenesis.Tactics (
  Phase120Config
  coupling_R coupling_G coupling_B
  coupling_R_at_equilibrium coupling_G_at_equilibrium coupling_B_at_equilibrium
  all_couplings_vanish_at_equilibrium
  JacobianAtEquilibrium
  rotationPeriod floquet_multiplier_bound
  complex_phase_sum_zero
)

end ChiralGeometrogenesis.Tactics.Prelude
