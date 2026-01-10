/-
  Phase0/Definition_0_1_2.lean

  Definition 0.1.2: Three Color Fields with Relative Phases — Complex Formalization

  This file EXTENDS the existing ColorPhase definitions (Basic.lean) and
  ColorFields/Basic.lean by adding the COMPLEX NUMBER formalization:

  - The primitive cube root of unity ω = e^{2πi/3}
  - Complex phase factors e^{iφ_c} for each color
  - Key algebraic properties: 1 + ω + ω² = 0, ω³ = 1
  - Anti-color phases as complex conjugates
  - Gauge invariance of relative phases

  This completes the bridge from real phase angles to complex field values
  χ_c(x) = a_c(x) · e^{iφ_c}.

  Reference: docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md

  Status: ✅ COMPLETE — FOUNDATIONAL (Peer-Review Ready)

  Adversarial Review (2025-12-26):
  - Fixed: Section ordering (§2→§3→§4→§5→§6→§7→§8→§9)
  - Fixed: Added omega_sq_eq_conj (inverse of omega_conj_eq_sq)
  - Fixed: Added gauge_sum_transform theorem
  - Fixed: Made helper lemmas public (sqrt3_div2_im, sqrt3_div2_re)
  - Fixed: Added explicit citations for Complex.exp properties
  - Fixed: Added omega_ne_omega_cubed distinctness theorem
  - Added: Complete verification notes for each section

  Key NEW results (not in Basic.lean or ColorFields/Basic.lean):
  - §2: Complex phase factors and cube roots of unity
  - §3: 1 + ω + ω² = 0 (algebraic color neutrality)
  - §4: Anti-color phase factors as conjugates
  - §5: Complete field specification χ_c = a_c · e^{iφ_c}
  - §6: Gauge invariance theorems
  - §7: Connection to SU(3) generators
  - §8: ℤ₃ cyclic symmetry
  - §9: Connection to weight space

  Dependencies (IMPORTS, not duplicates):
  - ✅ Basic.lean — ColorPhase, ColorPhase.angle
  - ✅ ColorFields/Basic.lean — colorToWeight, phase separation theorems
  - ✅ Weights.lean — SU(3) weight vectors
-/

import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.ColorFields.Basic
import ChiralGeometrogenesis.PureMath.LieAlgebra.Weights
import ChiralGeometrogenesis.PureMath.LieAlgebra.SU3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Phase0.Definition_0_1_2

open ChiralGeometrogenesis
open ChiralGeometrogenesis.PureMath.LieAlgebra
open ChiralGeometrogenesis.ColorFields
open Complex

/-! ## Section 2: Complex Phase Factors

While Basic.lean defines the REAL phase angles (0, 2π/3, 4π/3),
this section defines the COMPLEX phase factors e^{iφ_c}.

These are the cube roots of unity: 1, ω, ω².
-/

/-- Complex phase factor e^{iφ_c} for each color.
    Uses ColorPhase.angle from Basic.lean. -/
noncomputable def phaseFactor (c : ColorPhase) : ℂ :=
  Complex.exp (Complex.I * (c.angle : ℂ))

/-- The primitive cube root of unity ω = e^{2πi/3} -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-! ### Key Properties of ω -/

/-- ω³ = 1 (ω is a cube root of unity)

    **Proof:** Uses Mathlib's `Complex.exp_nat_mul` and `Complex.exp_two_pi_mul_I`.
    - exp_nat_mul: exp(z)^n = exp(n*z)
    - exp_two_pi_mul_I: exp(2πi) = 1

    Calculation: ω³ = exp(2πi/3)³ = exp(3 · 2πi/3) = exp(2πi) = 1 -/
theorem omega_cubed : omega ^ 3 = 1 := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have h : (3 : ℂ) * (2 * ↑Real.pi * I / 3) = 2 * ↑Real.pi * I := by ring
  rw [h]
  exact Complex.exp_two_pi_mul_I

/-- Explicit form: ω = -1/2 + i√3/2

    **Proof:** Uses Euler's formula exp(iθ) = cos(θ) + i·sin(θ) with θ = 2π/3.

    **Citations:**
    - `Complex.exp_mul_I`: exp(i·θ) = cos(θ) + i·sin(θ)
    - `Real.cos_pi_sub`: cos(π - x) = -cos(x)
    - `Real.sin_pi_sub`: sin(π - x) = sin(x)
    - `Real.cos_pi_div_three`: cos(π/3) = 1/2
    - `Real.sin_pi_div_three`: sin(π/3) = √3/2

    **Calculation:**
    ω = exp(2πi/3) = cos(2π/3) + i·sin(2π/3)
      = cos(π - π/3) + i·sin(π - π/3)
      = -cos(π/3) + i·sin(π/3)
      = -1/2 + i·(√3/2) -/
theorem omega_explicit : omega = -1/2 + Complex.I * (Real.sqrt 3 / 2) := by
  unfold omega
  -- Rewrite the exponent to match exp_mul_I form
  have harg : (2 : ℂ) * ↑Real.pi * I / 3 = I * ↑(2 * Real.pi / 3) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [harg, mul_comm I, Complex.exp_mul_I]
  -- Now the goal is: cos(2π/3) + I * sin(2π/3) = -1/2 + I * (√3/2)
  -- Use the ofReal_cos and ofReal_sin lemmas
  have hcos : Real.cos (2 * Real.pi / 3) = -1/2 := by
    have eq1 : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [eq1, Real.cos_pi_sub, Real.cos_pi_div_three]
    ring
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have eq1 : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [eq1, Real.sin_pi_sub, Real.sin_pi_div_three]
  -- Convert Complex.cos to Real.cos via ofReal
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- ω² = -1/2 - i√3/2 (complex conjugate of ω)

    Computed directly using exp and trig identities for 4π/3. -/
theorem omega_sq_explicit : omega ^ 2 = -1/2 - Complex.I * (Real.sqrt 3 / 2) := by
  -- Compute ω² = exp(4πi/3) directly using trig values for 4π/3
  unfold omega
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have harg : (2 : ℂ) * (2 * ↑Real.pi * I / 3) = I * ↑(4 * Real.pi / 3) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [harg, mul_comm I, Complex.exp_mul_I]
  -- Now: cos(4π/3) + I * sin(4π/3) = -1/2 - I * (√3/2)
  have hcos : Real.cos (4 * Real.pi / 3) = -1/2 := by
    have eq1 : (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [eq1, Real.cos_add_pi, Real.cos_pi_div_three]
    ring
  have hsin : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    have eq1 : (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [eq1, Real.sin_add_pi, Real.sin_pi_div_three]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- ω̄ = ω² (conjugate equals square)

    **Citation:** Standard property of primitive cube roots of unity.
    For ω = e^{2πi/3}, we have ω̄ = e^{-2πi/3} = e^{4πi/3} = ω². -/
theorem omega_conj_eq_sq : starRingEnd ℂ omega = omega ^ 2 := by
  -- First rewrite omega on LHS, then omega^2 on RHS
  conv_lhs => rw [omega_explicit]
  conv_rhs => rw [omega_sq_explicit]
  -- Goal: starRingEnd ℂ (-1/2 + I * (√3/2)) = -1/2 - I * (√3/2)
  -- The conjugate of (-1/2 + I * (√3/2)) is (-1/2 - I * (√3/2))
  simp only [map_add, map_neg, map_div₀, map_one, map_ofNat, map_mul,
             Complex.conj_I, Complex.conj_ofReal]
  ring

/-- ω² = ω̄ (square equals conjugate — inverse of omega_conj_eq_sq)

    This is the symmetric form: ω² = conj(ω).
    Both directions are useful in different proof contexts. -/
theorem omega_sq_eq_conj : omega ^ 2 = starRingEnd ℂ omega :=
  omega_conj_eq_sq.symm

/-- ω ≠ 1 (ω is a primitive cube root of unity, not the trivial one)

    This follows from the explicit form: ω = -1/2 + i√3/2 has real part -1/2 ≠ 1. -/
theorem omega_ne_one : omega ≠ 1 := by
  rw [omega_explicit]
  intro h
  have : (-1/2 : ℂ) + I * (↑(Real.sqrt 3) / 2) = 1 := h
  have hre : ((-1/2 : ℂ) + I * (↑(Real.sqrt 3) / 2)).re = (1 : ℂ).re := by rw [this]
  simp only [add_re, neg_re, one_re, div_ofNat_re, I_re, mul_re, ofReal_re, I_im] at hre
  norm_num at hre

/-- ω ≠ ω² (the three cube roots of unity are distinct)

    This follows from ω² = ω̄ and ω having nonzero imaginary part. -/
theorem omega_ne_omega_sq : omega ≠ omega ^ 2 := by
  rw [omega_sq_explicit]  -- First rewrite omega^2
  rw [omega_explicit]     -- Then rewrite omega
  intro h
  -- If -1/2 + i√3/2 = -1/2 - i√3/2, then imaginary parts must be equal
  have him : ((-1/2 : ℂ) + I * (↑(Real.sqrt 3) / 2)).im =
             ((-1/2 : ℂ) - I * (↑(Real.sqrt 3) / 2)).im := by rw [h]
  simp only [add_im, neg_im, one_im, div_ofNat_im, I_im, mul_im, I_re,
             ofReal_im, sub_im, zero_div, one_mul, mul_zero, zero_add] at him
  -- him : (↑√3 / 2).re = -(↑√3 / 2).re
  -- Need to simplify (↑√3 / 2).re to √3 / 2
  have hsqrt3_re : (↑(Real.sqrt 3) / 2 : ℂ).re = Real.sqrt 3 / 2 := by
    simp only [div_ofNat_re, ofReal_re]
  rw [hsqrt3_re] at him
  have hpos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  linarith

/-- ω² ≠ 1 (ω² is also a primitive cube root, not trivial)

    Combined with omega_ne_one and omega_ne_omega_sq, this proves all three
    cube roots {1, ω, ω²} are mutually distinct. -/
theorem omega_sq_ne_one : omega ^ 2 ≠ 1 := by
  rw [omega_sq_explicit]
  intro h
  have hre : ((-1/2 : ℂ) - I * (↑(Real.sqrt 3) / 2)).re = (1 : ℂ).re := by rw [h]
  simp only [sub_re, neg_re, one_re, div_ofNat_re, I_re, mul_re, ofReal_re, I_im] at hre
  norm_num at hre

/-- All three cube roots of unity are mutually distinct.

    This is the complete distinctness result: {1, ω, ω²} are three different complex numbers. -/
theorem cube_roots_distinct :
    (1 : ℂ) ≠ omega ∧ omega ≠ omega ^ 2 ∧ omega ^ 2 ≠ 1 :=
  ⟨omega_ne_one.symm, omega_ne_omega_sq, omega_sq_ne_one⟩

/-! ### Phase Factor Correspondence with ω -/

/-- Phase factor for R is 1 = ω⁰ -/
theorem phaseFactor_R : phaseFactor ColorPhase.R = 1 := by
  unfold phaseFactor ColorPhase.angle
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- Phase factor for G is ω = ω¹ -/
theorem phaseFactor_G : phaseFactor ColorPhase.G = omega := by
  unfold phaseFactor ColorPhase.angle omega
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Phase factor for B is ω² -/
theorem phaseFactor_B : phaseFactor ColorPhase.B = omega ^ 2 := by
  unfold phaseFactor ColorPhase.angle omega
  rw [← Complex.exp_nat_mul]
  congr 1
  simp only [Nat.cast_ofNat, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-! ## Section 3: The Cube Roots of Unity — Algebraic Properties

The fundamental identity 1 + ω + ω² = 0 is the algebraic form of
color neutrality. This is why RGB combines to "white" (color neutral).
-/

/-- Sum of cube roots of unity is zero: 1 + ω + ω² = 0

    This is the ALGEBRAIC color neutrality condition.
    Compare to fundamental_weights_neutral in ColorFields/Basic.lean
    which proves the same property for weight vectors. -/
theorem cube_roots_sum_zero : 1 + omega + omega ^ 2 = 0 := by
  -- Use ω³ - 1 = 0 factorization: (ω - 1)(ω² + ω + 1) = 0
  -- Since ω ≠ 1 (by omega_ne_one), we have ω² + ω + 1 = 0
  have h3 : omega ^ 3 = 1 := omega_cubed
  have factored : omega ^ 3 - 1 = (omega - 1) * (omega ^ 2 + omega + 1) := by ring
  have h_diff : omega ^ 3 - 1 = 0 := by rw [h3]; ring
  rw [factored] at h_diff
  have h_sum : omega ^ 2 + omega + 1 = 0 := by
    have hne : omega - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
    exact (mul_eq_zero.mp h_diff).resolve_left hne
  -- From h_sum: ω² + ω + 1 = 0, we need 1 + ω + ω² = 0
  calc 1 + omega + omega ^ 2 = omega ^ 2 + omega + 1 := by ring
    _ = 0 := h_sum

/-- Phase factors sum to zero: e^{iφ_R} + e^{iφ_G} + e^{iφ_B} = 0

    This is the COMPLEX form of color neutrality.
    Direct corollary of cube_roots_sum_zero. -/
theorem phase_factors_sum_zero :
    phaseFactor ColorPhase.R + phaseFactor ColorPhase.G + phaseFactor ColorPhase.B = 0 := by
  rw [phaseFactor_R, phaseFactor_G, phaseFactor_B]
  exact cube_roots_sum_zero

/-- Product of cube roots of unity is 1: 1 · ω · ω² = ω³ = 1 -/
theorem cube_roots_product : 1 * omega * omega ^ 2 = 1 := by
  simp only [one_mul]
  have h : omega * omega ^ 2 = omega ^ 3 := by ring
  rw [h, omega_cubed]

/-- Phase factors product is 1: e^{iφ_R} · e^{iφ_G} · e^{iφ_B} = 1

    Physical meaning: The total phase of a baryon (RGB) is trivial. -/
theorem phase_factors_product :
    phaseFactor ColorPhase.R * phaseFactor ColorPhase.G * phaseFactor ColorPhase.B = 1 := by
  rw [phaseFactor_R, phaseFactor_G, phaseFactor_B]
  exact cube_roots_product

/-! ## Section 4: Anti-Color Phases

Anti-colors have conjugate phase factors: e^{iφ_c̄} = e^{-iφ_c} = (e^{iφ_c})*.

This follows from the anti-fundamental representation 3̄ of SU(3).
-/

/-- Anti-phase factor e^{-iφ_c} = conjugate of phase factor -/
noncomputable def antiPhaseFactor (c : ColorPhase) : ℂ :=
  Complex.exp (-Complex.I * (c.angle : ℂ))

/-- Anti-phase factor equals conjugate of phase factor -/
theorem antiPhaseFactor_eq_conj (c : ColorPhase) :
    antiPhaseFactor c = starRingEnd ℂ (phaseFactor c) := by
  unfold antiPhaseFactor phaseFactor
  -- Goal: exp(-I * c.angle) = starRingEnd ℂ (exp(I * c.angle))
  -- We use: conj(exp(z)) = exp(conj(z)) and conj(I * θ) = -I * θ for real θ
  -- Use Complex.exp_conj: exp (conj x) = conj (exp x)
  -- So we need: exp(-I * θ) = conj (exp(I * θ)) for real θ
  -- conj (exp(I * θ)) = exp(conj(I * θ)) = exp(-I * θ) since conj(I) = -I and conj(θ) = θ
  have h : starRingEnd ℂ (Complex.exp (I * ↑c.angle)) =
           Complex.exp (starRingEnd ℂ (I * ↑c.angle)) := by
    rw [← Complex.exp_conj]
  rw [h]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]

/-- Anti-R phase factor is 1 (since φ_R = 0) -/
theorem antiPhaseFactor_R : antiPhaseFactor ColorPhase.R = 1 := by
  rw [antiPhaseFactor_eq_conj, phaseFactor_R]
  simp

/-- Anti-G phase factor is ω² (same phase as B) -/
theorem antiPhaseFactor_G : antiPhaseFactor ColorPhase.G = omega ^ 2 := by
  rw [antiPhaseFactor_eq_conj, phaseFactor_G, omega_conj_eq_sq]

/-- Anti-B phase factor is ω (same phase as G) -/
theorem antiPhaseFactor_B : antiPhaseFactor ColorPhase.B = omega := by
  rw [antiPhaseFactor_eq_conj, phaseFactor_B]
  rw [map_pow, omega_conj_eq_sq]
  have h3 : omega ^ 3 = 1 := omega_cubed
  calc (omega ^ 2) ^ 2 = omega ^ 4 := by ring
    _ = omega ^ 3 * omega := by ring
    _ = 1 * omega := by rw [h3]
    _ = omega := by ring

/-! ## Section 6: Gauge Invariance

Only RELATIVE phases are physically meaningful. An overall phase rotation
χ_c → e^{iα}χ_c is a gauge transformation that leaves observables unchanged.
-/

/-- Gauge transformation preserves phase factor ratios -/
theorem gauge_preserves_relative_phases (α : ℝ) :
    let rotation := Complex.exp (Complex.I * (α : ℂ))
    (rotation * phaseFactor ColorPhase.G) / (rotation * phaseFactor ColorPhase.R) =
    phaseFactor ColorPhase.G / phaseFactor ColorPhase.R := by
  simp only
  rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-- Under gauge transformation, the product picks up e^{3iα} -/
theorem gauge_product_transform (α : ℝ) :
    let rotation := Complex.exp (Complex.I * (α : ℂ))
    (rotation * phaseFactor ColorPhase.R) * (rotation * phaseFactor ColorPhase.G) *
    (rotation * phaseFactor ColorPhase.B) =
    rotation ^ 3 * (phaseFactor ColorPhase.R * phaseFactor ColorPhase.G * phaseFactor ColorPhase.B) := by
  simp only
  ring

/-- Under gauge transformation, the sum picks up a factor of rotation.

    Since 1 + ω + ω² = 0, the sum remains zero after rotation:
    rotation * (1 + ω + ω²) = rotation * 0 = 0

    This shows color neutrality is preserved under gauge transformations. -/
theorem gauge_sum_transform (α : ℝ) :
    let rotation := Complex.exp (Complex.I * (α : ℂ))
    rotation * phaseFactor ColorPhase.R + rotation * phaseFactor ColorPhase.G +
    rotation * phaseFactor ColorPhase.B = 0 := by
  simp only
  have h : Complex.exp (I * ↑α) * phaseFactor ColorPhase.R +
           Complex.exp (I * ↑α) * phaseFactor ColorPhase.G +
           Complex.exp (I * ↑α) * phaseFactor ColorPhase.B =
           Complex.exp (I * ↑α) * (phaseFactor ColorPhase.R + phaseFactor ColorPhase.G +
                                    phaseFactor ColorPhase.B) := by ring
  rw [h, phase_factors_sum_zero, mul_zero]

/-- Gauge transformation preserves the phase factor sum (zero remains zero) -/
theorem gauge_preserves_neutrality (α : ℝ) :
    let rotation := Complex.exp (Complex.I * (α : ℂ))
    (phaseFactor ColorPhase.R + phaseFactor ColorPhase.G + phaseFactor ColorPhase.B = 0) →
    (rotation * phaseFactor ColorPhase.R + rotation * phaseFactor ColorPhase.G +
     rotation * phaseFactor ColorPhase.B = 0) := by
  intro rotation h
  have factored : rotation * phaseFactor ColorPhase.R + rotation * phaseFactor ColorPhase.G +
                  rotation * phaseFactor ColorPhase.B =
                  rotation * (phaseFactor ColorPhase.R + phaseFactor ColorPhase.G +
                              phaseFactor ColorPhase.B) := by ring
  rw [factored, h, mul_zero]

/-! ## Section 8: ℤ₃ Cyclic Symmetry

The ℤ₃ generator ω acts by cyclic permutation: R → G → B → R.
Multiplication by ω advances the color by one step.
-/

/-- The ℤ₃ generator ω acts by cyclic permutation on phase factors -/
theorem Z3_action (c : ColorPhase) :
    omega * phaseFactor c = phaseFactor (match c with | .R => .G | .G => .B | .B => .R) := by
  cases c
  · -- R case: ω · 1 = ω = phaseFactor G
    simp only [phaseFactor_R, phaseFactor_G]; ring
  · -- G case: ω · ω = ω² = phaseFactor B
    simp only [phaseFactor_G, phaseFactor_B]; ring
  · -- B case: ω · ω² = ω³ = 1 = phaseFactor R
    simp only [phaseFactor_B, phaseFactor_R]
    have h : omega * omega ^ 2 = omega ^ 3 := by ring
    rw [h, omega_cubed]

/-- Cyclic permutation is equivalent to overall phase shift by ω -/
theorem cyclic_permutation_is_phase_shift :
    phaseFactor ColorPhase.G = omega * phaseFactor ColorPhase.R ∧
    phaseFactor ColorPhase.B = omega * phaseFactor ColorPhase.G ∧
    phaseFactor ColorPhase.R = omega * phaseFactor ColorPhase.B := by
  constructor
  · rw [phaseFactor_R, phaseFactor_G]; ring
  constructor
  · rw [phaseFactor_G, phaseFactor_B]; ring
  · rw [phaseFactor_B, phaseFactor_R]
    have h : omega * omega ^ 2 = omega ^ 3 := by ring
    rw [h, omega_cubed]

/-! ## Section 5: Complete Field Specification

The color fields χ_c(x) = a_c(x) · e^{iφ_c} combine:
- Amplitude a_c(x) from pressure functions (Definition 0.1.3, ColorFields/Basic.lean)
- Phase factors e^{iφ_c} = ω^{c} (defined in this file)

Cross-reference: ColorField structure is defined in ColorFields/Basic.lean.
This section provides the complex formulation connecting to that structure.
-/

/-- Complete complex color field: amplitude times phase factor.

    This is the formal version of χ_c(x) = a_c(x) · e^{iφ_c}.
    The amplitude function comes from ColorFields/Basic.lean (ColorField.amplitude).
    The phase factor comes from phaseFactor defined above. -/
noncomputable def complexColorField (c : ColorPhase) (amplitude : ℝ) : ℂ :=
  (amplitude : ℂ) * phaseFactor c

/-- Red field explicit form: χ_R = a · 1 = a -/
theorem complexColorField_R (a : ℝ) :
    complexColorField ColorPhase.R a = (a : ℂ) := by
  unfold complexColorField
  rw [phaseFactor_R, mul_one]

/-- Green field explicit form: χ_G = a · ω = a(-1/2 + i√3/2) -/
theorem complexColorField_G (a : ℝ) :
    complexColorField ColorPhase.G a = (a : ℂ) * omega := by
  unfold complexColorField
  rw [phaseFactor_G]

/-- Blue field explicit form: χ_B = a · ω² = a(-1/2 - i√3/2) -/
theorem complexColorField_B (a : ℝ) :
    complexColorField ColorPhase.B a = (a : ℂ) * omega ^ 2 := by
  unfold complexColorField
  rw [phaseFactor_B]

/-- The total field for equal amplitudes.

    χ_total = a(1 + ω + ω²) = 0 when all amplitudes are equal.
    This is the complex form of color neutrality. -/
theorem totalField_equal_amplitude (a : ℝ) :
    complexColorField ColorPhase.R a + complexColorField ColorPhase.G a +
    complexColorField ColorPhase.B a = 0 := by
  unfold complexColorField
  have h : (a : ℂ) * phaseFactor ColorPhase.R + (a : ℂ) * phaseFactor ColorPhase.G +
           (a : ℂ) * phaseFactor ColorPhase.B =
           (a : ℂ) * (phaseFactor ColorPhase.R + phaseFactor ColorPhase.G + phaseFactor ColorPhase.B) := by
    ring
  rw [h, phase_factors_sum_zero, mul_zero]

/-- The imaginary part of √3/2 (as a complex number) is 0.

    This is because √3 is a real number, so (√3 : ℂ) = √3 + 0·i.
    Useful for simplifying complex arithmetic with explicit ω forms. -/
theorem sqrt3_div2_im : (↑(Real.sqrt 3) / 2 : ℂ).im = 0 := by
  simp only [div_ofNat_im, ofReal_im]
  norm_num

/-- The real part of √3/2 (as a complex number) is √3/2.

    This extracts the real component from the complex embedding of √3/2.
    Useful for simplifying complex arithmetic with explicit ω forms. -/
theorem sqrt3_div2_re : (↑(Real.sqrt 3) / 2 : ℂ).re = Real.sqrt 3 / 2 := by
  simp only [div_ofNat_re, ofReal_re]

/-- Real and imaginary parts of total field with different amplitudes.

    χ_total = a_R - (a_G + a_B)/2 + i·√3/2·(a_G - a_B)

    The real part: a_R - (a_G + a_B)/2
    The imaginary part: √3/2 · (a_G - a_B) -/
theorem totalField_real_part (a_R a_G a_B : ℝ) :
    (complexColorField ColorPhase.R a_R + complexColorField ColorPhase.G a_G +
     complexColorField ColorPhase.B a_B).re =
    a_R - (a_G + a_B) / 2 := by
  unfold complexColorField
  rw [phaseFactor_R, phaseFactor_G, phaseFactor_B, omega_sq_explicit, omega_explicit]
  simp only [mul_one, add_re, mul_re, ofReal_re, ofReal_im, sub_re, neg_re, one_re,
             div_ofNat_re, I_re, I_im]
  simp only [sub_zero, zero_mul]
  rw [sqrt3_div2_im]
  ring

theorem totalField_imag_part (a_R a_G a_B : ℝ) :
    (complexColorField ColorPhase.R a_R + complexColorField ColorPhase.G a_G +
     complexColorField ColorPhase.B a_B).im =
    Real.sqrt 3 / 2 * (a_G - a_B) := by
  unfold complexColorField
  rw [phaseFactor_R, phaseFactor_G, phaseFactor_B, omega_sq_explicit, omega_explicit]
  simp only [mul_one, add_im, mul_im, ofReal_re, ofReal_im, sub_im, neg_im, one_im,
             div_ofNat_im, I_re, I_im]
  simp only [zero_add, one_mul, zero_mul]
  rw [sqrt3_div2_re]
  ring

/-! ## Section 7: Connection to SU(3) Generators

The color states |R⟩, |G⟩, |B⟩ are eigenstates of the Cartan generators T₃ = λ₃/2 and T₈ = λ₈/2.
This connects the phase structure to the diagonal generators of SU(3).

**Mathematical Background:**

The Cartan subalgebra of su(3) is spanned by T₃ and T₈ (or equivalently λ₃ and λ₈).
The weight vectors (t3, t8) encode the eigenvalues of these generators on each state:
- T₃|R⟩ = (1/2)|R⟩,  T₈|R⟩ = (1/(2√3))|R⟩
- T₃|G⟩ = (-1/2)|G⟩, T₈|G⟩ = (1/(2√3))|G⟩
- T₃|B⟩ = 0,         T₈|B⟩ = (-1/√3)|B⟩

**Citation:** These eigenvalue assignments are standard in the physics literature.
See Georgi, "Lie Algebras in Particle Physics" (1999), Chapter 7, or
Peskin & Schroeder, "An Introduction to Quantum Field Theory" (1995), Appendix.

**Implementation Note:** Rather than computing explicit matrix-vector products
(which require complex unfolding of Matrix.mulVec in Lean), we verify that the
weight vector components match the expected eigenvalues. The weight vectors
are defined in Weights.lean with these precise values.
-/

/-- The color basis vectors in ℂ³ -/
def colorBasisR : Fin 3 → ℂ := ![1, 0, 0]
def colorBasisG : Fin 3 → ℂ := ![0, 1, 0]
def colorBasisB : Fin 3 → ℂ := ![0, 0, 1]

/-- The eigenvalues of λ₃ for the color states.

    These correspond to the T₃ values in the weight diagram:
    - |R⟩: T₃ = +1/2 → eigenvalue = +1 (for λ₃ = 2T₃)
    - |G⟩: T₃ = -1/2 → eigenvalue = -1
    - |B⟩: T₃ = 0 → eigenvalue = 0

    Cross-reference: w_R.t3 = 1/2, w_G.t3 = -1/2, w_B.t3 = 0 from Weights.lean -/
theorem lambda3_eigenvalues :
    w_R.t3 = 1/2 ∧ w_G.t3 = -1/2 ∧ w_B.t3 = 0 := by
  constructor
  · rfl  -- w_R.t3 = 1/2
  constructor
  · rfl  -- w_G.t3 = -1/2
  · rfl  -- w_B.t3 = 0

/-- The eigenvalues of λ₈ for the color states.

    These correspond to the T₈ values in the weight diagram:
    - |R⟩: T₈ = 1/(2√3) → eigenvalue = 1/√3 (for λ₈ = 2T₈)
    - |G⟩: T₈ = 1/(2√3) → eigenvalue = 1/√3
    - |B⟩: T₈ = -1/√3 → eigenvalue = -2/√3

    Cross-reference: w_R.t8, w_G.t8, w_B.t8 from Weights.lean -/
theorem lambda8_eigenvalues :
    w_R.t8 = 1 / (2 * Real.sqrt 3) ∧
    w_G.t8 = 1 / (2 * Real.sqrt 3) ∧
    w_B.t8 = -1 / Real.sqrt 3 := by
  constructor
  · rfl  -- w_R.t8 = 1/(2√3)
  constructor
  · rfl  -- w_G.t8 = 1/(2√3)
  · rfl  -- w_B.t8 = -1/√3

/-- The weight vectors encode both λ₃ and λ₈ eigenvalues.

    This is the key connection: the 2D weight space of SU(3)
    corresponds to simultaneous eigenvalues of the two Cartan generators. -/
theorem weight_encodes_cartan_eigenvalues :
    (w_R.t3, w_R.t8) = (1/2, 1/(2 * Real.sqrt 3)) ∧
    (w_G.t3, w_G.t8) = (-1/2, 1/(2 * Real.sqrt 3)) ∧
    (w_B.t3, w_B.t8) = (0, -1/Real.sqrt 3) := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The center element ω·I generates ℤ₃ symmetry.

    The center of SU(3) is {I, ωI, ω²I} ≅ ℤ₃.
    Multiplying by ω advances each color by one step in the phase cycle.

    This is already captured by the Z3_action theorem above:
    ω · e^{iφ_c} = e^{iφ_{next(c)}} -/
theorem center_element_phase_action :
    omega * phaseFactor ColorPhase.R = phaseFactor ColorPhase.G ∧
    omega * phaseFactor ColorPhase.G = phaseFactor ColorPhase.B ∧
    omega * phaseFactor ColorPhase.B = phaseFactor ColorPhase.R := by
  constructor
  · rw [phaseFactor_R, phaseFactor_G]; ring
  constructor
  · rw [phaseFactor_G, phaseFactor_B]; ring
  · rw [phaseFactor_B, phaseFactor_R]
    have h : omega * omega ^ 2 = omega ^ 3 := by ring
    rw [h, omega_cubed]

/-! ## Section 9: Connection to Weight Space

The complex phase factor formulation connects to the weight vector
formulation in Weights.lean and ColorFields/Basic.lean.

The 120° separation (cos θ = -1/2) corresponds to 1 + ω + ω² = 0.
-/

/-- The 120° angular separation corresponds to cos(θ) = -1/2.
    This is the geometric manifestation of 1 + ω + ω² = 0.

    Uses cosine_angle_R_G from Weights.lean. -/
theorem weight_angle_corresponds_to_phase :
    weightDot w_R w_G / weightNormSq w_R = -1/2 :=
  cosine_angle_R_G

/-- Color fields at equal amplitude satisfy complex color neutrality -/
theorem equal_amplitude_color_neutral (a : ℝ) :
    (a : ℂ) * phaseFactor ColorPhase.R + (a : ℂ) * phaseFactor ColorPhase.G +
    (a : ℂ) * phaseFactor ColorPhase.B = 0 := by
  have h : (a : ℂ) * phaseFactor ColorPhase.R + (a : ℂ) * phaseFactor ColorPhase.G +
           (a : ℂ) * phaseFactor ColorPhase.B =
           (a : ℂ) * (phaseFactor ColorPhase.R + phaseFactor ColorPhase.G + phaseFactor ColorPhase.B) := by
    ring
  rw [h, phase_factors_sum_zero, mul_zero]

/-! ## Summary: Definition 0.1.2 Complete Characterization

This file adds the COMPLEX formalization to the existing ColorPhase definitions:

| Existing (Basic.lean, ColorFields/Basic.lean) | New (this file) |
|-----------------------------------------------|-----------------|
| ColorPhase.angle : ℝ (real phases) | phaseFactor : ℂ (complex) |
| color_phases_equally_spaced (2π/3) | ω and its properties |
| fundamental_weights_neutral (weight sum = 0) | 1 + ω + ω² = 0 |
| colorToAntiWeight (negation) | antiPhaseFactor (conjugate) |
| — | Gauge invariance theorems |
| — | ℤ₃ cyclic action |
| — | Complete field specification χ_c = a_c · e^{iφ_c} |
| — | SU(3) generator eigenvalue correspondence |

**Adversarial Review Additions (2025-12-26):**
| New theorems added | Purpose |
|-------------------|---------|
| omega_sq_eq_conj | Symmetric form of ω̄ = ω² |
| omega_sq_ne_one | All cube roots distinct |
| cube_roots_distinct | Complete distinctness |
| gauge_sum_transform | Gauge transform of sum |
| gauge_preserves_neutrality | Neutrality is gauge-invariant |
| sqrt3_div2_im, sqrt3_div2_re | Made public for reuse |
-/

/-- Complete characterization of Definition 0.1.2 (complex formulation)

    This theorem consolidates all the key results from this file:

    1. **Phase factor ↔ ω correspondence**: e^{iφ_R} = 1, e^{iφ_G} = ω, e^{iφ_B} = ω²
    2. **Algebraic color neutrality**: 1 + ω + ω² = 0
    3. **Phase factors sum to zero**: Direct consequence of (2)
    4. **Phase product is unity**: 1 · ω · ω² = ω³ = 1
    5. **ω is a cube root of unity**: ω³ = 1
    6. **Anti-colors are conjugates**: e^{iφ_c̄} = (e^{iφ_c})*
    7. **Equal amplitude neutrality**: χ_R + χ_G + χ_B = 0 when a_R = a_G = a_B
    8. **ℤ₃ cyclic action**: ω · e^{iφ_c} = e^{iφ_{next(c)}}
    9. **Weight vector correspondence**: T₃, T₈ eigenvalues match Weights.lean
    10. **120° angular separation**: cos(θ_RG) = -1/2
    11. **Cube roots distinct**: 1 ≠ ω ≠ ω² ≠ 1 -/
theorem definition_0_1_2_complete :
    -- (1) Phase factor correspondence with ω
    (phaseFactor ColorPhase.R = 1 ∧
     phaseFactor ColorPhase.G = omega ∧
     phaseFactor ColorPhase.B = omega ^ 2) ∧
    -- (2) Algebraic color neutrality
    (1 + omega + omega ^ 2 = 0) ∧
    -- (3) Phase factors sum to zero
    (phaseFactor ColorPhase.R + phaseFactor ColorPhase.G + phaseFactor ColorPhase.B = 0) ∧
    -- (4) Phase product is unity
    (phaseFactor ColorPhase.R * phaseFactor ColorPhase.G * phaseFactor ColorPhase.B = 1) ∧
    -- (5) ω is a cube root of unity
    (omega ^ 3 = 1) ∧
    -- (6) Anti-colors are conjugates
    (antiPhaseFactor ColorPhase.R = starRingEnd ℂ (phaseFactor ColorPhase.R) ∧
     antiPhaseFactor ColorPhase.G = starRingEnd ℂ (phaseFactor ColorPhase.G) ∧
     antiPhaseFactor ColorPhase.B = starRingEnd ℂ (phaseFactor ColorPhase.B)) ∧
    -- (7) Equal amplitude color neutrality (for complex fields)
    (∀ a : ℝ, complexColorField ColorPhase.R a + complexColorField ColorPhase.G a +
              complexColorField ColorPhase.B a = 0) ∧
    -- (8) ℤ₃ cyclic action
    (omega * phaseFactor ColorPhase.R = phaseFactor ColorPhase.G ∧
     omega * phaseFactor ColorPhase.G = phaseFactor ColorPhase.B ∧
     omega * phaseFactor ColorPhase.B = phaseFactor ColorPhase.R) ∧
    -- (9) Weight vector T₃ correspondence
    (w_R.t3 = 1/2 ∧ w_G.t3 = -1/2 ∧ w_B.t3 = 0) ∧
    -- (10) 120° angular separation
    (weightDot w_R w_G / weightNormSq w_R = -1/2) ∧
    -- (11) Cube roots are distinct
    ((1 : ℂ) ≠ omega ∧ omega ≠ omega ^ 2 ∧ omega ^ 2 ≠ 1) := by
  refine ⟨⟨phaseFactor_R, phaseFactor_G, phaseFactor_B⟩,
          cube_roots_sum_zero,
          phase_factors_sum_zero,
          phase_factors_product,
          omega_cubed,
          ⟨antiPhaseFactor_eq_conj ColorPhase.R, antiPhaseFactor_eq_conj ColorPhase.G,
           antiPhaseFactor_eq_conj ColorPhase.B⟩,
          totalField_equal_amplitude,
          center_element_phase_action,
          lambda3_eigenvalues,
          cosine_angle_R_G,
          cube_roots_distinct⟩

/-! ## Verification: #check Tests for Key Theorems

These #check statements verify that Lean accepts all key theorems and definitions.
-/

section CheckTests

-- Core omega properties
#check omega
#check omega_cubed
#check omega_explicit
#check omega_sq_explicit
#check omega_conj_eq_sq
#check omega_sq_eq_conj
#check omega_ne_one
#check omega_ne_omega_sq
#check omega_sq_ne_one
#check cube_roots_distinct

-- Phase factors
#check phaseFactor
#check phaseFactor_R
#check phaseFactor_G
#check phaseFactor_B
#check phase_factors_sum_zero
#check phase_factors_product

-- Algebraic properties
#check cube_roots_sum_zero
#check cube_roots_product

-- Anti-phase factors
#check antiPhaseFactor
#check antiPhaseFactor_eq_conj
#check antiPhaseFactor_R
#check antiPhaseFactor_G
#check antiPhaseFactor_B

-- Gauge invariance
#check gauge_preserves_relative_phases
#check gauge_product_transform
#check gauge_sum_transform
#check gauge_preserves_neutrality

-- Z3 symmetry
#check Z3_action
#check cyclic_permutation_is_phase_shift
#check center_element_phase_action

-- Complex fields
#check complexColorField
#check complexColorField_R
#check complexColorField_G
#check complexColorField_B
#check totalField_equal_amplitude
#check totalField_real_part
#check totalField_imag_part

-- Helper lemmas (now public)
#check sqrt3_div2_im
#check sqrt3_div2_re

-- SU(3) connections
#check colorBasisR
#check colorBasisG
#check colorBasisB
#check lambda3_eigenvalues
#check lambda8_eigenvalues
#check weight_encodes_cartan_eigenvalues

-- Weight space connection
#check weight_angle_corresponds_to_phase
#check equal_amplitude_color_neutral

-- Complete characterization
#check definition_0_1_2_complete

end CheckTests

end ChiralGeometrogenesis.Phase0.Definition_0_1_2
