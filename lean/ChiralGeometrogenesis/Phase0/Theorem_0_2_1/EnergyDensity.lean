/-
  Phase0/Theorem_0_2_1/EnergyDensity.lean

  Energy Density for Theorem 0.2.1

  The energy density is always positive, even when the field itself is zero.

  Contains:
  - colorEnergy, totalEnergy definitions
  - energy_nonneg: ρ(x) ≥ 0
  - symmetric_energy_pos: ρ > 0 for a₀ > 0
  - symmetric_energy_formula: ρ = 3a₀²
  - center_is_node_but_has_energy: χ(0) = 0 but ρ(0) > 0

  Reference: docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md §3
-/

import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.Core
import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.PhaseSum

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase0.Theorem_0_2_1

open ChiralGeometrogenesis
open ChiralGeometrogenesis.PureMath.Polyhedra
open Complex Real

/-! ## Energy Density

The energy density is always positive, even when the field itself is zero.
-/

/-- Energy density from a single color field -/
noncomputable def colorEnergy (a : AmplitudeFunction) (x : Point3D) : ℝ :=
  (a.amplitude x) ^ 2

/-- Total energy density (sum of squared amplitudes) -/
noncomputable def totalEnergy (cfg : ColorAmplitudes) (x : Point3D) : ℝ :=
  colorEnergy cfg.aR x + colorEnergy cfg.aG x + colorEnergy cfg.aB x

/-- Energy density is non-negative -/
theorem energy_nonneg (cfg : ColorAmplitudes) (x : Point3D) :
    0 ≤ totalEnergy cfg x := by
  unfold totalEnergy colorEnergy
  apply add_nonneg
  · apply add_nonneg
    · exact sq_nonneg _
    · exact sq_nonneg _
  · exact sq_nonneg _

/-- For symmetric config with a₀ > 0, energy is positive -/
theorem symmetric_energy_pos (a₀ : ℝ) (ha : 0 < a₀) (x : Point3D) :
    0 < totalEnergy (symmetricConfig a₀ (le_of_lt ha)) x := by
  unfold totalEnergy symmetricConfig colorEnergy
  simp only
  have h : a₀ ^ 2 + a₀ ^ 2 + a₀ ^ 2 = 3 * a₀ ^ 2 := by ring
  rw [h]
  apply mul_pos
  · norm_num
  · exact sq_pos_of_pos ha

/-! ## The Central Node

At the center of the stella octangula (with symmetric pressure),
the total field is zero but energy persists.
-/

/-- At center with equal pressures: field is zero but energy is not -/
theorem center_is_node_but_has_energy (a₀ : ℝ) (ha : 0 < a₀) :
    totalChiralField (symmetricConfig a₀ (le_of_lt ha)) stellaCenter = 0 ∧
    0 < totalEnergy (symmetricConfig a₀ (le_of_lt ha)) stellaCenter := by
  constructor
  · exact symmetric_field_is_zero a₀ (le_of_lt ha) stellaCenter
  · exact symmetric_energy_pos a₀ ha stellaCenter

/-! ## Physical Interpretation

The key insight: at the stella center:
1. The three color contributions cancel (χ = 0)
2. But each color has non-zero amplitude (ρ > 0)
3. This is NOT equilibrium - the phases are still evolving

The energy density ρ(x) = Σ_c |a_c(x)|² represents the "presence of field"
even when the phases conspire to make the total field vanish.
-/

/-- Energy formula: ρ = 3a₀² for symmetric configuration -/
theorem symmetric_energy_formula (a₀ : ℝ) (ha : 0 ≤ a₀) (x : Point3D) :
    totalEnergy (symmetricConfig a₀ ha) x = 3 * a₀ ^ 2 := by
  unfold totalEnergy symmetricConfig colorEnergy
  simp only
  ring

/-! ## Coherent Field Magnitude (§4 of Theorem 0.2.1)

⚠️ CRITICAL DISTINCTION (from §3.0 of markdown):
- |χ_total|² = coherent field magnitude (includes interference)
- ρ(x) = Σ|a_c|² = energy density (incoherent sum)

At the center: |χ_total(0)|² = 0 but ρ(0) ≠ 0
-/

/-- Squared magnitude of total chiral field (coherent, with interference) -/
noncomputable def coherentFieldMagnitude (cfg : ColorAmplitudes) (x : Point3D) : ℝ :=
  Complex.normSq (totalChiralField cfg x)

/-- Alternative form for coherent magnitude (§4.2)
    |χ_total|² = (a₀²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]

    This elegant form shows that the magnitude depends only on
    the DIFFERENCES between pressure values, not their absolute values.

    ⚠️ CONNECTION TO coherentFieldMagnitude: For a PressureModulatedConfig,
    coherentFieldMagnitude cfg x = coherentMagnitudeAltForm a₀ P_R(x) P_G(x) P_B(x)
    This requires expanding totalChiralField and applying Complex.normSq.
    The proof follows from coherent_from_real_imag and the definitions.
-/
noncomputable def coherentMagnitudeAltForm (a₀ P_R P_G P_B : ℝ) : ℝ :=
  (a₀^2 / 2) * ((P_R - P_G)^2 + (P_G - P_B)^2 + (P_B - P_R)^2)

/-- The alternative form is equivalent to the standard expansion (§4.2 proof)
    |χ_total|² = a₀²[P_R² + P_G² + P_B² - P_R·P_G - P_G·P_B - P_B·P_R]
              = (a₀²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]
-/
theorem alternative_form_equivalence (a₀ P_R P_G P_B : ℝ) :
    coherentMagnitudeAltForm a₀ P_R P_G P_B =
    a₀^2 * (P_R^2 + P_G^2 + P_B^2 - P_R*P_G - P_G*P_B - P_B*P_R) := by
  unfold coherentMagnitudeAltForm
  ring

/-- Critical result: At center with equal pressures, coherent magnitude vanishes (§4.3)
    This is because all pressure differences are zero -/
theorem coherent_magnitude_zero_at_equal_pressures (a₀ P₀ : ℝ) :
    coherentMagnitudeAltForm a₀ P₀ P₀ P₀ = 0 := by
  unfold coherentMagnitudeAltForm
  ring

/-- The distinction between |χ_total|² and ρ (§3.0 clarification)

    For symmetric configuration at center:
    - |χ_total(0)|² = 0 (phases cancel, destructive interference)
    - ρ(0) = 3a₀²P₀² > 0 (energy persists)

    This is the "node paradox": the field vanishes but energy doesn't.
-/
theorem field_energy_distinction (a₀ : ℝ) (ha : 0 < a₀) :
    let P₀ := (1 : ℝ)  -- Equal pressure at center
    coherentMagnitudeAltForm a₀ P₀ P₀ P₀ = 0 ∧
    3 * a₀^2 * P₀^2 > 0 := by
  constructor
  · exact coherent_magnitude_zero_at_equal_pressures a₀ 1
  · have h : 3 * a₀^2 * 1^2 = 3 * a₀^2 := by ring
    rw [h]
    apply mul_pos
    · norm_num
    · exact sq_pos_of_pos ha

/-- Real and imaginary parts of the total field (§2.3)
    Re[χ_total] = a₀[P_R - (P_G + P_B)/2]
    Im[χ_total] = a₀·(√3/2)·(P_G - P_B)
-/
noncomputable def totalFieldRealPart (a₀ P_R P_G P_B : ℝ) : ℝ :=
  a₀ * (P_R - (P_G + P_B) / 2)

noncomputable def totalFieldImagPart (a₀ P_G P_B : ℝ) : ℝ :=
  a₀ * (Real.sqrt 3 / 2) * (P_G - P_B)

/-- The coherent magnitude from real/imaginary parts

    We verify the algebraic identity:
    Re² + Im² = a₀²[P_R² + P_G² + P_B² - P_R·P_G - P_G·P_B - P_B·P_R]

    where Re = a₀[P_R - (P_G + P_B)/2] and Im = a₀·(√3/2)·(P_G - P_B)

    NOTE: This proves the algebraic form. The connection to `coherentFieldMagnitude`
    (which uses `Complex.normSq`) requires additionally showing that for
    z = Re + i·Im, we have Complex.normSq z = Re² + Im². This is immediate
    from the Mathlib definition `Complex.normSq z = z.re² + z.im²`.
-/
theorem coherent_from_real_imag (a₀ P_R P_G P_B : ℝ) :
    (totalFieldRealPart a₀ P_R P_G P_B)^2 + (totalFieldImagPart a₀ P_G P_B)^2 =
    a₀^2 * (P_R^2 + P_G^2 + P_B^2 - P_R*P_G - P_G*P_B - P_B*P_R) := by
  unfold totalFieldRealPart totalFieldImagPart
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
  -- Expand and simplify
  calc (a₀ * (P_R - (P_G + P_B) / 2))^2 + (a₀ * (Real.sqrt 3 / 2) * (P_G - P_B))^2
      = a₀^2 * (P_R - (P_G + P_B) / 2)^2 + a₀^2 * (Real.sqrt 3 / 2)^2 * (P_G - P_B)^2 := by ring
    _ = a₀^2 * (P_R - (P_G + P_B) / 2)^2 + a₀^2 * (3 / 4) * (P_G - P_B)^2 := by
        rw [div_pow, h3]; ring
    _ = a₀^2 * ((P_R - (P_G + P_B) / 2)^2 + (3 / 4) * (P_G - P_B)^2) := by ring
    _ = a₀^2 * (P_R^2 + P_G^2 + P_B^2 - P_R*P_G - P_G*P_B - P_B*P_R) := by ring

/-! ## §4.4: Coherent Magnitude Equivalence

**CRITICAL LINKING THEOREM**: This section proves the equivalence between
the abstract definition `coherentFieldMagnitude` (using Complex.normSq)
and the concrete formula `coherentMagnitudeAltForm`.

This closes the logical gap between:
1. The definition: coherentFieldMagnitude cfg x = Complex.normSq (totalChiralField cfg x)
2. The formula: coherentMagnitudeAltForm a₀ P_R P_G P_B = (a₀²/2)[sum of squared differences]

For a PressureModulatedConfig, these are provably equal.
-/

/-- Helper: The total chiral field for a pressure-modulated config has explicit form

    χ_total(x) = a₀·P_R(x)·1 + a₀·P_G(x)·e^{i·2π/3} + a₀·P_B(x)·e^{i·4π/3}
               = a₀·[P_R + P_G·(-1/2 + i√3/2) + P_B·(-1/2 - i√3/2)]

    Real part: a₀·[P_R - P_G/2 - P_B/2] = a₀·[P_R - (P_G + P_B)/2]
    Imag part: a₀·[P_G·√3/2 - P_B·√3/2] = a₀·(√3/2)·(P_G - P_B)
-/
theorem pressureModulatedField_components (cfg : PressureModulatedConfig) (x : Point3D) :
    (totalChiralField cfg.toAmplitudes x).re =
      cfg.a₀ * (cfg.pressure ColorPhase.R x - (cfg.pressure ColorPhase.G x +
        cfg.pressure ColorPhase.B x) / 2) ∧
    (totalChiralField cfg.toAmplitudes x).im =
      cfg.a₀ * (Real.sqrt 3 / 2) * (cfg.pressure ColorPhase.G x - cfg.pressure ColorPhase.B x) := by
  -- Expand the total field
  unfold totalChiralField colorContribution PressureModulatedConfig.toAmplitudes
  simp only
  -- Unfold phaseR, phaseG, phaseB to phaseExp form first
  have hR : phaseExp ColorPhase.R = phaseR := rfl
  have hG : phaseExp ColorPhase.G = phaseG := rfl
  have hB : phaseExp ColorPhase.B = phaseB := rfl
  rw [hR, hG, hB]
  -- Expand using phase values
  rw [phaseR_eq_one, phaseG_explicit, phaseB_explicit]
  constructor
  · -- Real part
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_one]
    ring
  · -- Imaginary part
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
               add_zero, mul_one, zero_mul]
    ring

/-- **KEY LINKING THEOREM**: coherentFieldMagnitude equals coherentMagnitudeAltForm

    For a PressureModulatedConfig cfg with base amplitude a₀ and pressure functions
    P_R, P_G, P_B, we have:

    coherentFieldMagnitude cfg.toAmplitudes x = coherentMagnitudeAltForm a₀ P_R(x) P_G(x) P_B(x)

    This theorem closes the logical gap by connecting:
    - The abstract definition using Complex.normSq of the total field
    - The concrete algebraic formula in terms of pressure differences

    The proof strategy:
    1. Show Complex.normSq z = z.re² + z.im² (Mathlib definition)
    2. Compute z.re and z.im explicitly using pressureModulatedField_components
    3. Apply coherent_from_real_imag to get the standard form
    4. Apply alternative_form_equivalence to get the difference form
-/
theorem coherentFieldMagnitude_eq_altForm (cfg : PressureModulatedConfig) (x : Point3D) :
    coherentFieldMagnitude cfg.toAmplitudes x =
    coherentMagnitudeAltForm cfg.a₀
      (cfg.pressure ColorPhase.R x)
      (cfg.pressure ColorPhase.G x)
      (cfg.pressure ColorPhase.B x) := by
  -- Abbreviations for readability
  set P_R := cfg.pressure ColorPhase.R x with hPR
  set P_G := cfg.pressure ColorPhase.G x with hPG
  set P_B := cfg.pressure ColorPhase.B x with hPB
  set a₀ := cfg.a₀ with ha₀
  -- Step 1: coherentFieldMagnitude = Complex.normSq z
  unfold coherentFieldMagnitude
  -- The field z = totalChiralField cfg.toAmplitudes x
  have h_components := pressureModulatedField_components cfg x
  -- Step 2: Get explicit real and imaginary parts
  have h_re : (totalChiralField cfg.toAmplitudes x).re = a₀ * (P_R - (P_G + P_B) / 2) :=
    h_components.1
  have h_im : (totalChiralField cfg.toAmplitudes x).im = a₀ * (Real.sqrt 3 / 2) * (P_G - P_B) :=
    h_components.2
  -- Step 3: normSq z = z.re² + z.im² (from Mathlib)
  rw [Complex.normSq_apply]
  rw [h_re, h_im]
  -- Step 4: Convert from x * x to x^2 form
  have h_real_sq : (a₀ * (P_R - (P_G + P_B) / 2)) * (a₀ * (P_R - (P_G + P_B) / 2)) =
      (totalFieldRealPart a₀ P_R P_G P_B)^2 := by
    unfold totalFieldRealPart; ring
  have h_imag_sq : (a₀ * (Real.sqrt 3 / 2) * (P_G - P_B)) * (a₀ * (Real.sqrt 3 / 2) * (P_G - P_B)) =
      (totalFieldImagPart a₀ P_G P_B)^2 := by
    unfold totalFieldImagPart; ring
  rw [h_real_sq, h_imag_sq]
  -- Step 5: Apply coherent_from_real_imag to get the standard form
  rw [coherent_from_real_imag]
  -- Step 6: Apply alternative_form_equivalence (in reverse)
  rw [← alternative_form_equivalence]

/-- Corollary: At equal pressures, coherentFieldMagnitude vanishes

    This directly follows from coherentFieldMagnitude_eq_altForm and
    coherent_magnitude_zero_at_equal_pressures.
-/
theorem coherentFieldMagnitude_zero_at_equal_pressures
    (cfg : PressureModulatedConfig) (x : Point3D)
    (h_equal : cfg.pressure ColorPhase.R x = cfg.pressure ColorPhase.G x ∧
               cfg.pressure ColorPhase.G x = cfg.pressure ColorPhase.B x) :
    coherentFieldMagnitude cfg.toAmplitudes x = 0 := by
  rw [coherentFieldMagnitude_eq_altForm]
  -- All pressures equal P₀
  have hRG : cfg.pressure ColorPhase.R x = cfg.pressure ColorPhase.G x := h_equal.1
  have hGB : cfg.pressure ColorPhase.G x = cfg.pressure ColorPhase.B x := h_equal.2
  rw [hRG, hGB]
  exact coherent_magnitude_zero_at_equal_pressures cfg.a₀ (cfg.pressure ColorPhase.B x)

/-- Corollary: coherentFieldMagnitude is always non-negative

    Since it equals Complex.normSq, which is always ≥ 0.
-/
theorem coherentFieldMagnitude_nonneg (cfg : ColorAmplitudes) (x : Point3D) :
    0 ≤ coherentFieldMagnitude cfg x := by
  unfold coherentFieldMagnitude
  exact Complex.normSq_nonneg _

/-- The coherent magnitude alternative form is also non-negative

    This follows from its expression as a sum of squares.
-/
theorem coherentMagnitudeAltForm_nonneg (a₀ P_R P_G P_B : ℝ) :
    0 ≤ coherentMagnitudeAltForm a₀ P_R P_G P_B := by
  unfold coherentMagnitudeAltForm
  apply mul_nonneg
  · apply div_nonneg (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  · apply add_nonneg
    · apply add_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact sq_nonneg _

end ChiralGeometrogenesis.Phase0.Theorem_0_2_1
