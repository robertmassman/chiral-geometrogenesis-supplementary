/-
  Phase0/Theorem_0_2_1/PhaseSum.lean

  Phase Sum Properties for Theorem 0.2.1

  Key result: The three unit phasors e^{i·0}, e^{i·2π/3}, e^{i·4π/3} sum to zero.
  This is the mathematical heart of color neutrality.

  Contains:
  - Trigonometric helper lemmas (cos/sin of 2π/3, 4π/3)
  - Phase exponential explicit forms
  - phase_sum_zero: phaseR + phaseG + phaseB = 0
  - symmetric_field_is_zero

  Reference: docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md §2
-/

import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.Core

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase0.Theorem_0_2_1

open ChiralGeometrogenesis
open ChiralGeometrogenesis.ColorFields
open ChiralGeometrogenesis.PureMath.Polyhedra
open Complex Real

/-! ## Key Property: Phases Sum to Zero

The three unit phasors e^{i·0}, e^{i·2π/3}, e^{i·4π/3} sum to zero.
This is the mathematical heart of color neutrality.

**Mathematical Background:**
These are the three cube roots of unity: 1, ω, ω² where ω = e^{i2π/3}.
The identity 1 + ω + ω² = 0 is a fundamental result in algebra.

**Proof Strategy:**
We use Euler's formula e^{iθ} = cos(θ) + i·sin(θ) and the explicit values:
  cos(0) = 1,           sin(0) = 0
  cos(2π/3) = -1/2,     sin(2π/3) = √3/2
  cos(4π/3) = -1/2,     sin(4π/3) = -√3/2

**Citations:**
- Euler's formula: Mathlib `Complex.exp_mul_I`
- cos(π/3) = 1/2, sin(π/3) = √3/2: Mathlib `Real.cos_pi_div_three`, `Real.sin_pi_div_three`
- Cube roots of unity summing to zero: Standard result, see
  Lang, "Algebra" (Springer, 3rd ed.), Chapter IV, §1, or
  Dummit & Foote, "Abstract Algebra" (Wiley, 3rd ed.), §13.6.
-/

/-- Helper: cos(2π/3) = -1/2 -/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1/2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub]
  simp only [Real.cos_pi_div_three]
  ring

/-- Helper: sin(2π/3) = √3/2 -/
theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub]
  simp only [Real.sin_pi_div_three]

/-- Helper: cos(4π/3) = -1/2 -/
theorem cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -1/2 := by
  have h1 : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [h1, Real.cos_add_pi]
  simp only [Real.cos_pi_div_three]
  ring

/-- Helper: sin(4π/3) = -√3/2 -/
theorem sin_four_pi_div_three : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
  have h1 : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [h1, Real.sin_add_pi]
  simp only [Real.sin_pi_div_three]

/-- Complex exponential in terms of cos and sin -/
theorem exp_I_mul (θ : ℝ) : Complex.exp (Complex.I * θ) = ⟨Real.cos θ, Real.sin θ⟩ := by
  rw [mul_comm, Complex.exp_mul_I]
  apply Complex.ext
  · -- Real part: (cos ↑θ + sin ↑θ * I).re = cos θ
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring
  · -- Imaginary part: (cos ↑θ + sin ↑θ * I).im = sin θ
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring

/-- Phase R exponential: e^{i·0} = 1 -/
theorem phaseR_eq_one : phaseR = 1 := by
  unfold phaseR phaseExp
  simp only [ColorPhase.angle, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- Phase G exponential: e^{i·2π/3} = -1/2 + i√3/2 -/
theorem phaseG_explicit : phaseG = ⟨-1/2, Real.sqrt 3 / 2⟩ := by
  unfold phaseG phaseExp
  simp only [ColorPhase.angle]
  rw [exp_I_mul, cos_two_pi_div_three, sin_two_pi_div_three]

/-- Phase B exponential: e^{i·4π/3} = -1/2 - i√3/2 -/
theorem phaseB_explicit : phaseB = ⟨-1/2, -(Real.sqrt 3 / 2)⟩ := by
  unfold phaseB phaseExp
  simp only [ColorPhase.angle]
  rw [exp_I_mul, cos_four_pi_div_three, sin_four_pi_div_three]

/-- The sum of the three phase exponentials is zero -/
theorem phase_sum_zero : phaseR + phaseG + phaseB = 0 := by
  rw [phaseR_eq_one, phaseG_explicit, phaseB_explicit]
  -- 1 + (-1/2 + i√3/2) + (-1/2 - i√3/2) = 0
  apply Complex.ext
  · -- Real part: 1 + (-1/2) + (-1/2) = 0
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re]
    ring
  · -- Imaginary part: 0 + √3/2 + (-√3/2) = 0
    simp only [Complex.add_im, Complex.one_im, Complex.zero_im]
    ring

/-- Corollary: At symmetric configuration, total field is zero at any point -/
theorem symmetric_field_is_zero (a₀ : ℝ) (ha : 0 ≤ a₀) (x : Point3D) :
    totalChiralField (symmetricConfig a₀ ha) x = 0 := by
  unfold totalChiralField symmetricConfig colorContribution
  simp only
  -- Factor out a₀: a₀·e^{i·0} + a₀·e^{i·2π/3} + a₀·e^{i·4π/3} = a₀·(1 + ω + ω²)
  -- where 1 + ω + ω² = 0 (cube roots of unity)
  calc (↑a₀ : ℂ) * phaseExp ColorPhase.R + ↑a₀ * phaseExp ColorPhase.G + ↑a₀ * phaseExp ColorPhase.B
      = ↑a₀ * (phaseExp ColorPhase.R + phaseExp ColorPhase.G + phaseExp ColorPhase.B) := by ring
    _ = ↑a₀ * (phaseR + phaseG + phaseB) := by rfl
    _ = ↑a₀ * 0 := by rw [phase_sum_zero]
    _ = 0 := by ring

/-- The cube roots of unity sum to zero (real part) -/
theorem cube_roots_sum_zero_re :
    Real.cos 0 + Real.cos (2 * Real.pi / 3) + Real.cos (4 * Real.pi / 3) = 0 := by
  rw [Real.cos_zero, cos_two_pi_div_three, cos_four_pi_div_three]
  ring

/-- The cube roots of unity sum to zero (imaginary part) -/
theorem cube_roots_sum_zero_im :
    Real.sin 0 + Real.sin (2 * Real.pi / 3) + Real.sin (4 * Real.pi / 3) = 0 := by
  rw [Real.sin_zero, sin_two_pi_div_three, sin_four_pi_div_three]
  ring

/-- The sum of phase exponentials e^{iφ_R} + e^{iφ_G} + e^{iφ_B} = 0

    This is the fundamental result that ensures cross-terms cancel.

    **NOTE:** This theorem is equivalent to `phase_sum_zero` since
    `phaseExp c = phaseX` for the corresponding color X.
    We provide both forms for API convenience:
    - `phase_sum_zero`: Uses the named constants phaseR, phaseG, phaseB
    - `phase_exponentials_sum_zero`: Uses the general phaseExp function

    The equivalence follows from: phaseExp ColorPhase.X = phaseX by definition. -/
theorem phase_exponentials_sum_zero :
    phaseExp ColorPhase.R + phaseExp ColorPhase.G + phaseExp ColorPhase.B = 0 := by
  -- Equivalent to phase_sum_zero via the definitions of phaseR, phaseG, phaseB
  have h : phaseExp ColorPhase.R + phaseExp ColorPhase.G + phaseExp ColorPhase.B =
           phaseR + phaseG + phaseB := rfl
  rw [h, phase_sum_zero]

end ChiralGeometrogenesis.Phase0.Theorem_0_2_1
