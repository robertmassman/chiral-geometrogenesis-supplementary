/-
  Foundations/DynamicsFoundation.lean

  Comprehensive Dynamics Infrastructure for Chiral Geometrogenesis

  This module provides the foundational structures for field dynamics, addressing
  three critical gaps in the formal framework:

  1. **Complex Chiral Field Structure** (§1)
     - Complex scalar fields χ_c : V → ℂ with amplitude and phase
     - Color field triplet (R, G, B) with 120° phase separation
     - Total field superposition χ_total = Σ_c a_c(x) e^{iφ_c}

  2. **Internal Time Parameter** (§2)
     - Evolution parameter λ that breaks the bootstrap circularity
     - Phase evolution dφ/dλ = ω[χ] without external metric
     - Physical time emergence t = ∫dλ/ω

  3. **Pre-Geometric Energy Functional** (§3)
     - Algebraic energy E[χ] = Σ|a_c|² + λ(Σ|a_c|² - v₀²)²
     - Resolves Noether circularity: energy defined without spacetime
     - Positive semi-definiteness and VEV structure

  ## Mathematical Background

  The bootstrap problem in Chiral Geometrogenesis:

  ```
  Emergent Metric (5.2.1)
      ↓ requires
  Phase-Gradient Mass Generation Mass (3.1.1)
      ↓ requires
  Time-Dependent VEV χ(t) = v e^{iωt}
      ↓ requires
  Background spacetime metric to define ∂_t
      ↓ requires
  Emergent Metric ← CIRCULAR!
  ```

  **Resolution**: Time emerges from relative phase evolution, not external coordinates.
  The three color fields oscillate with respect to each other, creating an internal
  evolution parameter λ. Physical time t is then derived from λ.

  ## References

  - Theorem 0.2.2 (Internal Time Emergence): docs/proofs/Phase0/Theorem-0.2.2-Internal-Time-Emergence.md
  - Theorem 0.2.4 (Pre-Geometric Energy Functional): docs/proofs/Phase0/Theorem-0.2.4-Pre-Geometric-Energy-Functional.md
  - Definition 0.1.2 (Three Color Fields): docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md
-/

import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.Tactics.Phase120
import ChiralGeometrogenesis.Phase0.Definition_0_1_3
import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.Core
import ChiralGeometrogenesis.Phase0.Definition_0_1_4
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Foundations

open Real Complex
open ChiralGeometrogenesis
open ChiralGeometrogenesis.Tactics  -- Gap 2: SK dynamics connection

/-! ## Section 1: Complex Chiral Field Structure

The chiral field χ_c for each color c is a complex scalar field:
  χ_c(x) = a_c(x) · e^{iφ_c}

where:
- a_c(x) ≥ 0 is the amplitude (pressure-modulated)
- φ_c is the phase (fixed by SU(3) geometry: 0, 2π/3, 4π/3)

The key insight is that phases are RELATIVE, not referenced to external time.
-/

/-- A chiral field configuration at a single spatial point.

This represents the complex scalar field χ_c = a · e^{iφ} for a specific color.
The amplitude a is real and non-negative; the phase φ is in radians.

**Dimensional Convention:**
- amplitude a has dimensions [length]² (matches pressure function)
- phase φ is dimensionless (radians)
- The product a · e^{iφ} is dimensionless (field value)
-/
structure ChiralFieldValue where
  /-- Amplitude of the chiral field (non-negative) -/
  amplitude : ℝ
  /-- Phase angle in radians -/
  phase : ℝ
  /-- Amplitude is non-negative -/
  amplitude_nonneg : 0 ≤ amplitude

namespace ChiralFieldValue

/-- The complex value of a chiral field: a · e^{iφ} -/
noncomputable def toComplex (χ : ChiralFieldValue) : ℂ :=
  χ.amplitude * Complex.exp (Complex.I * χ.phase)

/-- Zero amplitude gives zero complex value -/
theorem toComplex_zero : (⟨0, 0, le_refl 0⟩ : ChiralFieldValue).toComplex = 0 := by
  simp only [toComplex]
  norm_cast
  ring

/-- |exp(i·θ)|² = 1 for any real θ -/
theorem normSq_exp_I_mul_real (θ : ℝ) : Complex.normSq (Complex.exp (Complex.I * θ)) = 1 := by
  have h1 : (Complex.I * ↑θ).re = 0 := by simp
  have h2 : (Complex.exp (Complex.I * ↑θ)).re = Real.cos θ := by
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
    simp only [h1]
    simp [Complex.cos_ofReal_re]
  have h3 : (Complex.exp (Complex.I * ↑θ)).im = Real.sin θ := by
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
    simp only [h1]
    simp [Complex.sin_ofReal_re]
  simp only [Complex.normSq_apply, h2, h3]
  have := Real.cos_sq_add_sin_sq θ
  linarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]

/-- The amplitude squared is the norm squared of the complex value -/
theorem amplitude_sq_eq_normSq (χ : ChiralFieldValue) :
    χ.amplitude ^ 2 = Complex.normSq χ.toComplex := by
  unfold toComplex
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [normSq_exp_I_mul_real]
  rw [mul_one]
  ring

end ChiralFieldValue

/-- A spatially-dependent chiral field assigns a ChiralFieldValue to each point.

This represents χ_c : V → ℂ as a pair of functions (amplitude, phase).
The color c determines which of the three fundamental phases (0, 2π/3, 4π/3)
the field oscillates around.
-/
structure ChiralField (V : Type*) where
  /-- The color of this field (R, G, or B) -/
  color : ColorPhase
  /-- Amplitude function a(x) ≥ 0 -/
  amplitude : V → ℝ
  /-- Amplitude is non-negative everywhere -/
  amplitude_nonneg : ∀ x, 0 ≤ amplitude x
  /-- Base phase (the color-specific offset is added automatically) -/
  basePhase : ℝ := 0

namespace ChiralField

/-- The total phase at a point, including the color offset.

**IMPORTANT (Issue 2 clarification):** This is the EQUILIBRIUM PHASE, which is
spatially constant. In the full dynamical theory, phase gradients ∇φ can exist
and are responsible for phase-gradient mass generation mass (Theorem 3.1.1). This simplified structure
represents the Phase 0 equilibrium configuration where phases are uniform.

For spatially-varying phases, use the `PressureFieldConfig` from Definition_0_1_3.
-/
noncomputable def phase {V : Type*} (χ : ChiralField V) : V → ℝ :=
  fun _ => χ.basePhase + χ.color.angle  -- Spatially constant at equilibrium

/-- The complex value at a point -/
noncomputable def value {V : Type*} (χ : ChiralField V) (x : V) : ℂ :=
  χ.amplitude x * Complex.exp (Complex.I * (χ.basePhase + χ.color.angle))

/-- The value squared is the amplitude squared -/
theorem value_normSq {V : Type*} (χ : ChiralField V) (x : V) :
    Complex.normSq (χ.value x) = (χ.amplitude x) ^ 2 := by
  unfold value
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  -- The phase is (basePhase + color.angle) which is real, so I * phase has re = 0
  have h_phase : Complex.normSq (Complex.exp (Complex.I * (↑χ.basePhase + ↑χ.color.angle))) = 1 := by
    have : (↑χ.basePhase + ↑χ.color.angle : ℂ) = ↑(χ.basePhase + χ.color.angle) := by push_cast; rfl
    rw [this]
    exact ChiralFieldValue.normSq_exp_I_mul_real _
  rw [h_phase, mul_one]
  ring

end ChiralField

/-- A triplet of color fields (R, G, B) at the same base phase.

This is the fundamental configuration of the chiral field:
  χ_R = a_R · e^{iφ₀}
  χ_G = a_G · e^{i(φ₀ + 2π/3)}
  χ_B = a_B · e^{i(φ₀ + 4π/3)}

The three fields share a common base phase φ₀ but are offset by 120°.
-/
structure ColorFieldTriplet (V : Type*) where
  /-- Red amplitude function -/
  amplitude_R : V → ℝ
  /-- Green amplitude function -/
  amplitude_G : V → ℝ
  /-- Blue amplitude function -/
  amplitude_B : V → ℝ
  /-- Common base phase -/
  basePhase : ℝ
  /-- Amplitudes are non-negative -/
  amplitudes_nonneg : ∀ x, 0 ≤ amplitude_R x ∧ 0 ≤ amplitude_G x ∧ 0 ≤ amplitude_B x

namespace ColorFieldTriplet

/-- Complex value of the red field at a point -/
noncomputable def value_R {V : Type*} (cfg : ColorFieldTriplet V) (x : V) : ℂ :=
  cfg.amplitude_R x * Complex.exp (Complex.I * cfg.basePhase)

/-- Complex value of the green field at a point -/
noncomputable def value_G {V : Type*} (cfg : ColorFieldTriplet V) (x : V) : ℂ :=
  cfg.amplitude_G x * Complex.exp (Complex.I * (cfg.basePhase + 2 * Real.pi / 3))

/-- Complex value of the blue field at a point -/
noncomputable def value_B {V : Type*} (cfg : ColorFieldTriplet V) (x : V) : ℂ :=
  cfg.amplitude_B x * Complex.exp (Complex.I * (cfg.basePhase + 4 * Real.pi / 3))

/-- The total chiral field: χ_total = χ_R + χ_G + χ_B -/
noncomputable def totalField {V : Type*} (cfg : ColorFieldTriplet V) (x : V) : ℂ :=
  cfg.value_R x + cfg.value_G x + cfg.value_B x

/-- When all amplitudes are equal, the total field vanishes.

This is the "phase-lock" at the center of the stella octangula where
all three colors have equal pressure.
-/
theorem totalField_zero_when_equal {V : Type*} (cfg : ColorFieldTriplet V) (x : V)
    (h_eq_RG : cfg.amplitude_R x = cfg.amplitude_G x)
    (h_eq_GB : cfg.amplitude_G x = cfg.amplitude_B x) :
    cfg.totalField x = 0 := by
  unfold totalField value_R value_G value_B
  rw [h_eq_RG, h_eq_GB]
  set a := cfg.amplitude_B x with ha
  set φ := cfg.basePhase with hφ
  -- The goal is: a * exp(I * φ) + a * exp(I * (φ + 2π/3)) + a * exp(I * (φ + 4π/3)) = 0
  -- First show the sum of cube roots of unity (times exp(iφ)) is zero
  have h_roots : exp (I * ↑φ) + exp (I * (↑φ + 2 * Real.pi / 3)) + exp (I * (↑φ + 4 * Real.pi / 3)) = 0 := by
    -- Factor out exp(iφ)
    have h1 : exp (I * (↑φ + 2 * Real.pi / 3)) = exp (I * ↑φ) * exp (I * (2 * Real.pi / 3)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h2 : exp (I * (↑φ + 4 * Real.pi / 3)) = exp (I * ↑φ) * exp (I * (4 * Real.pi / 3)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [h1, h2]
    have h_sum : exp (I * ↑φ) + exp (I * ↑φ) * exp (I * (2 * Real.pi / 3)) +
                 exp (I * ↑φ) * exp (I * (4 * Real.pi / 3)) =
                 exp (I * ↑φ) * (1 + exp (I * (2 * Real.pi / 3)) + exp (I * (4 * Real.pi / 3))) := by ring
    rw [h_sum]
    -- The cube roots of unity sum: 1 + ω + ω² = 0
    have h_omega : (1 : ℂ) + exp (I * (2 * Real.pi / 3)) + exp (I * (4 * Real.pi / 3)) = 0 := by
      -- Rewrite I * θ to θ * I so we can use exp_mul_I
      have h_comm1 : I * (2 * Real.pi / 3 : ℂ) = (2 * Real.pi / 3 : ℂ) * I := by ring
      have h_comm2 : I * (4 * Real.pi / 3 : ℂ) = (4 * Real.pi / 3 : ℂ) * I := by ring
      rw [h_comm1, h_comm2]
      rw [Complex.exp_mul_I, Complex.exp_mul_I]
      have harg1 : (2 : ℂ) * ↑Real.pi / 3 = ↑((2 : ℝ) * Real.pi / 3) := by push_cast; ring
      have harg2 : (4 : ℂ) * ↑Real.pi / 3 = ↑((4 : ℝ) * Real.pi / 3) := by push_cast; ring
      simp only [harg1, harg2]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      -- cos(2π/3) = -1/2, sin(2π/3) = √3/2
      have h_cos2 : Real.cos (2 * Real.pi / 3) = -1/2 := by
        rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
        rw [Real.cos_pi_sub, Real.cos_pi_div_three]
        ring
      have h_sin2 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
        rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
        rw [Real.sin_pi_sub, Real.sin_pi_div_three]
      have h_cos4 : Real.cos (4 * Real.pi / 3) = -1/2 := by
        rw [show (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi by ring]
        rw [Real.cos_add_pi, Real.cos_pi_div_three]
        norm_num
      have h_sin4 : Real.sin (4 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
        rw [show (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi by ring]
        rw [Real.sin_add_pi, Real.sin_pi_div_three]
        ring
      rw [h_cos2, h_sin2, h_cos4, h_sin4]
      push_cast
      ring
    rw [h_omega, mul_zero]
  -- Now factor out a and use h_roots
  calc (↑a : ℂ) * exp (I * ↑φ) + ↑a * exp (I * (↑φ + 2 * Real.pi / 3)) + ↑a * exp (I * (↑φ + 4 * Real.pi / 3))
      = ↑a * (exp (I * ↑φ) + exp (I * (↑φ + 2 * Real.pi / 3)) + exp (I * (↑φ + 4 * Real.pi / 3))) := by ring
    _ = ↑a * 0 := by rw [h_roots]
    _ = 0 := by ring

/-- Incoherent amplitude sum: Σ_c |a_c|² (NO phase interference).

**Naming clarification (Issue 6):** This is the INCOHERENT sum of amplitudes squared,
not the full energy density. The distinction matters:

- **Incoherent sum** Σ_c |a_c|²: Each color contributes independently, no phase cancellation
- **Coherent sum** |Σ_c a_c e^{iφ_c}|²: Phase interference can cause cancellation

For the full energy functional with Mexican hat potential, see:
- `PreGeometricEnergyConfig.totalEnergy` (real amplitudes, incoherent, this file)
- `Phase0.Theorem_0_2_4.preLorentzianEnergy` (complex amplitudes, coherent potential)

**Physical interpretation:** This represents the "kinetic-like" contribution from
field occupation, before accounting for potential energy or phase coherence effects.
-/
noncomputable def incoherentAmplitudeSq {V : Type*} (cfg : ColorFieldTriplet V) (x : V) : ℝ :=
  (cfg.amplitude_R x) ^ 2 + (cfg.amplitude_G x) ^ 2 + (cfg.amplitude_B x) ^ 2

/-- Alias for backward compatibility -/
noncomputable abbrev energyDensity {V : Type*} := @incoherentAmplitudeSq V

/-- Incoherent amplitude sum is non-negative -/
theorem incoherentAmplitudeSq_nonneg {V : Type*} (cfg : ColorFieldTriplet V) (x : V) :
    0 ≤ cfg.incoherentAmplitudeSq x := by
  unfold incoherentAmplitudeSq
  apply add_nonneg
  · apply add_nonneg
    · exact sq_nonneg _
    · exact sq_nonneg _
  · exact sq_nonneg _

/-- Incoherent amplitude sum is zero iff all amplitudes are zero -/
theorem incoherentAmplitudeSq_eq_zero_iff {V : Type*} (cfg : ColorFieldTriplet V) (x : V) :
    cfg.incoherentAmplitudeSq x = 0 ↔ cfg.amplitude_R x = 0 ∧ cfg.amplitude_G x = 0 ∧ cfg.amplitude_B x = 0 := by
  unfold incoherentAmplitudeSq
  constructor
  · intro h
    have h_nonneg := cfg.amplitudes_nonneg x
    have hR_sq := sq_nonneg (cfg.amplitude_R x)
    have hG_sq := sq_nonneg (cfg.amplitude_G x)
    have hB_sq := sq_nonneg (cfg.amplitude_B x)
    have h1 : (cfg.amplitude_R x) ^ 2 = 0 := by nlinarith
    have h2 : (cfg.amplitude_G x) ^ 2 = 0 := by nlinarith
    have h3 : (cfg.amplitude_B x) ^ 2 = 0 := by nlinarith
    -- If a² = 0 and a ≥ 0, then a = 0
    have hR_zero : cfg.amplitude_R x = 0 := by nlinarith
    have hG_zero : cfg.amplitude_G x = 0 := by nlinarith
    have hB_zero : cfg.amplitude_B x = 0 := by nlinarith
    exact ⟨hR_zero, hG_zero, hB_zero⟩
  · intro ⟨hR, hG, hB⟩
    simp only [hR, hG, hB, sq, mul_zero, add_zero]

end ColorFieldTriplet

/-! ## Section 1.5: Phase Configuration

A phase configuration represents the instantaneous phases of all three color
fields. This is the canonical structure used across Phase 0 and Phase 2 theorems.

The phases satisfy the SU(3) constraint: φ_G - φ_R = 2π/3, φ_B - φ_G = 2π/3.
-/

/-- A phase configuration for the three color oscillators.

This represents the instantaneous phases (φ_R, φ_G, φ_B) of the color fields.
For a valid configuration, these satisfy the 120° separation constraint.

**Usage**:
- Theorem 0.2.2 (Internal Time Emergence): Phase evolution dφ/dλ
- Theorem 2.2.1 (Phase-Locked Oscillation): Stability analysis

**Naming Convention**: Uses underscore (phi_R) for consistency across codebase.

**Cross-reference (Issue 4):** Related structure `Tactics.Phase120Config` uses a single
base phase φ₀ parameterization: (φ₀, φ₀+2π/3, φ₀+4π/3). Use `fromBasePhase` to construct
a `PhaseConfig` from a base phase, or see Theorem_0_2_2.lean for conversion functions.
The two structures represent the SAME mathematical object with different parameterizations:
- `PhaseConfig`: Explicit (φ_R, φ_G, φ_B) — useful when phases may deviate from equilibrium
- `Phase120Config`: Single φ₀ parameter — convenient at 120° equilibrium
-/
structure PhaseConfig where
  /-- Phase of red oscillator φ_R -/
  phi_R : ℝ
  /-- Phase of green oscillator φ_G -/
  phi_G : ℝ
  /-- Phase of blue oscillator φ_B -/
  phi_B : ℝ

namespace PhaseConfig

/-- A phase configuration is valid if phases are 120° apart.

This is the SU(3) constraint from the stella octangula geometry:
  φ_G - φ_R = 2π/3
  φ_B - φ_G = 2π/3
-/
def isValid (cfg : PhaseConfig) : Prop :=
  cfg.phi_G - cfg.phi_R = 2 * Real.pi / 3 ∧
  cfg.phi_B - cfg.phi_G = 2 * Real.pi / 3

/-- The equilibrium phase configuration: (0, 2π/3, 4π/3).

This is the reference configuration aligned with ColorPhase.angle. -/
noncomputable def equilibrium : PhaseConfig where
  phi_R := 0
  phi_G := 2 * Real.pi / 3
  phi_B := 4 * Real.pi / 3

/-- The equilibrium configuration is valid -/
theorem equilibrium_isValid : equilibrium.isValid := by
  unfold isValid equilibrium
  simp only
  constructor <;> ring

/-- Construct a valid phase configuration from a base phase.

Given base phase θ, produces (θ, θ + 2π/3, θ + 4π/3). -/
noncomputable def fromBasePhase (θ : ℝ) : PhaseConfig where
  phi_R := θ
  phi_G := θ + 2 * Real.pi / 3
  phi_B := θ + 4 * Real.pi / 3

/-- Configuration from base phase is always valid -/
theorem fromBasePhase_isValid (θ : ℝ) : (fromBasePhase θ).isValid := by
  unfold isValid fromBasePhase
  simp only
  constructor <;> ring

/-- The collective phase (average of three phases) -/
noncomputable def collectivePhase (cfg : PhaseConfig) : ℝ :=
  (cfg.phi_R + cfg.phi_G + cfg.phi_B) / 3

/-- For valid configs, collective phase determines all three phases.

Given Φ = (φ_R + φ_G + φ_B)/3 and the constraints:
- φ_R = Φ - 2π/3
- φ_G = Φ
- φ_B = Φ + 2π/3
-/
theorem collective_determines_phases (cfg : PhaseConfig) (h : cfg.isValid) :
    cfg.phi_R = cfg.collectivePhase - 2 * Real.pi / 3 ∧
    cfg.phi_G = cfg.collectivePhase ∧
    cfg.phi_B = cfg.collectivePhase + 2 * Real.pi / 3 := by
  unfold isValid at h
  unfold collectivePhase
  obtain ⟨hRG, hGB⟩ := h
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end PhaseConfig

/-! ## Section 2: Internal Time Parameter (λ)

The bootstrap circularity is resolved by recognizing that time emerges from
the relative phase evolution of the three color fields.

**Key insight**: The phases φ_c are defined RELATIVE to each other, not to
an external clock. The evolution parameter λ tracks this internal oscillation.

Evolution equations:
  dφ_c/dλ = ω[χ]

where ω is determined by energy minimization. Physical time then emerges:
  dt = dλ/ω

This means:
- λ is the "internal clock" of the field system
- ω is the frequency functional (depends on field configuration)
- t is the emergent physical time
-/

/-- Configuration for the internal evolution parameter.

The evolution parameter λ parameterizes the collective phase oscillation
of the three color fields. It exists BEFORE physical time.

**Bootstrap Resolution**:
- Traditional: ∂_t χ = iωχ requires background time coordinate
- Here: ∂_λ χ = iω[χ]·χ uses internal parameter λ
- Time emerges: t = ∫₀^λ dλ'/ω[χ(λ')]
-/
structure EvolutionConfig where
  /-- Current value of the internal parameter -/
  lambda : ℝ
  /-- The frequency functional (depends on field configuration) -/
  omega : ℝ
  /-- Frequency is positive (ensures forward evolution) -/
  omega_pos : 0 < omega

namespace EvolutionConfig

/-- Physical time increment corresponding to an internal parameter increment -/
noncomputable def dt (cfg : EvolutionConfig) (dlambda : ℝ) : ℝ :=
  dlambda / cfg.omega

/-- Physical time increment is positive when dlambda is positive -/
theorem dt_pos_of_dlambda_pos (cfg : EvolutionConfig) {dlambda : ℝ} (h : 0 < dlambda) :
    0 < cfg.dt dlambda := by
  unfold dt
  exact div_pos h cfg.omega_pos

end EvolutionConfig

/-- The phase evolution equation in abstract form.

For a field configuration with base phase φ₀ evolving with internal parameter λ:
  dφ₀/dλ = ω

This is the key equation that breaks the bootstrap: phases evolve with respect
to the internal parameter, not external time.
-/
structure PhaseEvolution where
  /-- Initial base phase -/
  phi_0 : ℝ
  /-- Frequency -/
  omega : ℝ
  /-- Internal parameter value -/
  lambda : ℝ

namespace PhaseEvolution

/-- The current phase value: φ(λ) = φ₀ + ω·λ -/
noncomputable def currentPhase (ev : PhaseEvolution) : ℝ :=
  ev.phi_0 + ev.omega * ev.lambda

/-- Phase advances linearly with λ -/
theorem phase_at_lambda (ev : PhaseEvolution) :
    ev.currentPhase = ev.phi_0 + ev.omega * ev.lambda := rfl

/-- The phase increment for a given λ increment -/
noncomputable def phaseIncrement (ev : PhaseEvolution) (dlambda : ℝ) : ℝ :=
  ev.omega * dlambda

/-- **Phase derivative theorem (Issue 7):**
    The phase function φ(λ) = φ₀ + ω·λ satisfies dφ/dλ = ω.

    This is the fundamental evolution equation that breaks the bootstrap:
    - Phases evolve with respect to the internal parameter λ
    - No external time coordinate is required
    - The frequency ω emerges from energy minimization (Theorem 0.2.2 §4.4)

    Mathematical derivation:
      φ(λ) = φ₀ + ω·λ
      dφ/dλ = d(φ₀)/dλ + d(ω·λ)/dλ = 0 + ω = ω
-/
theorem phase_derivative (ev : PhaseEvolution) :
    deriv (fun lam => ev.phi_0 + ev.omega * lam) ev.lambda = ev.omega := by
  -- d/dλ(φ₀ + ω·λ) = d/dλ(φ₀) + d/dλ(ω·λ) = 0 + ω = ω
  have h : deriv (fun lam => ev.phi_0 + ev.omega * lam) ev.lambda =
           deriv (fun lam => ev.phi_0) ev.lambda + deriv (fun lam => ev.omega * lam) ev.lambda := by
    apply deriv_add
    · exact differentiableAt_const ev.phi_0
    · exact DifferentiableAt.const_mul differentiableAt_id ev.omega
  rw [h]
  rw [deriv_const, deriv_const_mul _ differentiableAt_id, deriv_id'']
  ring

/-- Phase function is differentiable everywhere -/
theorem phase_differentiable (ev : PhaseEvolution) :
    Differentiable ℝ (fun lam => ev.phi_0 + ev.omega * lam) := by
  apply Differentiable.add
  · exact differentiable_const ev.phi_0
  · exact Differentiable.const_mul differentiable_id ev.omega

/-- Phase is monotonically increasing when ω > 0 -/
theorem phase_strictly_mono (ev : PhaseEvolution) (hω : ev.omega > 0) :
    StrictMono (fun lam => ev.phi_0 + ev.omega * lam) := by
  intro a b hab
  simp only
  have : ev.omega * a < ev.omega * b := mul_lt_mul_of_pos_left hab hω
  linarith

end PhaseEvolution

/-! ## Section 3: Pre-Geometric Energy Functional

**The Noether Circularity Problem**:
Traditional QFT defines energy via Noether's theorem, which requires:
- A spacetime manifold with translation symmetry
- An integral over space of the energy density

But in Phase 0 of Chiral Geometrogenesis, there IS no spacetime yet!
We need energy to be defined BEFORE the metric emerges.

**Resolution**: Define energy as an algebraic functional on configuration space:
  E[χ] = Σ_c |a_c|² + λ_χ(Σ_c |a_c|² - v₀²)²

This is:
- A sum of norms (no integration required)
- Positive semi-definite
- Has a minimum at the VEV |χ| = v₀

After the metric emerges, this becomes consistent with Noether energy.
-/

/-- Pre-geometric energy configuration (REAL AMPLITUDE, SIMPLIFIED MODEL).

**CRITICAL DISTINCTION (Issue 1 — Coherent vs Incoherent):**

This structure uses REAL amplitudes (a_R, a_G, a_B ∈ ℝ) and an INCOHERENT potential:
  E[χ] = Σ_c a_c² + λ_χ(Σ_c a_c² - v₀²)²

The FULL complex coherent model (Theorem 0.2.4) uses:
  E[χ] = Σ_c |a_c|² + λ_χ(|χ_total|² - v₀²)²

where χ_total = Σ_c a_c e^{iφ_c} is the COHERENT superposition.

**When to use which:**
- **This structure:** For internal evolution dynamics where phase coherence effects
  are handled separately (e.g., by ColorFieldTriplet.totalField_zero_when_equal)
- **Theorem_0_2_4:** For spontaneous symmetry breaking analysis where the coherent
  |χ_total|² in the Mexican hat potential is critical

**The key difference:**
- Coherent (Thm 0.2.4): At equal amplitudes a_R=a_G=a_B=a, |χ_total|²=0 due to phase cancellation
- Incoherent (this): At equal amplitudes, Σa_c²=3a² (no cancellation)

Both are mathematically valid energy functionals; they represent different physical regimes:
- Pre-coherent (this): Energy from individual field occupation
- Post-coherent (Thm 0.2.4): Energy accounting for phase interference

For the complete framework, see `Phase0.Theorem_0_2_4.preLorentzianEnergy`.
-/
structure PreGeometricEnergyConfig where
  /-- The VEV: v₀ > 0 -/
  vev : ℝ
  /-- VEV is positive -/
  vev_pos : 0 < vev
  /-- The coupling constant λ_χ > 0 -/
  coupling : ℝ
  /-- Coupling is non-negative -/
  coupling_nonneg : 0 ≤ coupling

namespace PreGeometricEnergyConfig

/-- The potential energy for a given total amplitude.

V(Σ|a|²) = λ_χ(Σ|a|² - v₀²)²

This is the Mexican hat potential that drives spontaneous symmetry breaking.
-/
noncomputable def potential (cfg : PreGeometricEnergyConfig) (totalAmplitudeSq : ℝ) : ℝ :=
  cfg.coupling * (totalAmplitudeSq - cfg.vev ^ 2) ^ 2

/-- Potential is non-negative -/
theorem potential_nonneg (cfg : PreGeometricEnergyConfig) (s : ℝ) :
    0 ≤ cfg.potential s := by
  unfold potential
  apply mul_nonneg cfg.coupling_nonneg (sq_nonneg _)

/-- Potential is zero at the VEV -/
theorem potential_zero_at_vev (cfg : PreGeometricEnergyConfig) :
    cfg.potential (cfg.vev ^ 2) = 0 := by
  unfold potential
  simp only [sub_self, sq, mul_zero]

/-- Potential is minimized at the VEV -/
theorem potential_min_at_vev (cfg : PreGeometricEnergyConfig) (s : ℝ) :
    cfg.potential (cfg.vev ^ 2) ≤ cfg.potential s := by
  rw [potential_zero_at_vev]
  exact potential_nonneg cfg s

/-- Total pre-geometric energy for given amplitudes.

E = Σ|a|² + V(Σ|a|²)

This is the full energy functional without spacetime integration.
-/
noncomputable def totalEnergy (cfg : PreGeometricEnergyConfig) (a_R a_G a_B : ℝ) : ℝ :=
  let s := a_R ^ 2 + a_G ^ 2 + a_B ^ 2
  s + cfg.potential s

/-- Total energy is non-negative (for non-negative amplitudes) -/
theorem totalEnergy_nonneg (cfg : PreGeometricEnergyConfig) (a_R a_G a_B : ℝ)
    (hR : 0 ≤ a_R) (hG : 0 ≤ a_G) (hB : 0 ≤ a_B) :
    0 ≤ cfg.totalEnergy a_R a_G a_B := by
  unfold totalEnergy
  have h_s_nonneg : 0 ≤ a_R ^ 2 + a_G ^ 2 + a_B ^ 2 := by
    have := sq_nonneg a_R
    have := sq_nonneg a_G
    have := sq_nonneg a_B
    linarith
  apply add_nonneg h_s_nonneg (potential_nonneg cfg _)

end PreGeometricEnergyConfig

/-! ## Section 4: Integration with Phase 0 Structures

This section connects the dynamics infrastructure to the existing Phase 0
definitions, particularly the pressure-modulated field configurations.
-/

/-- A dynamics configuration combines field structure with evolution parameters.

This is the complete specification needed for field evolution in the
pre-geometric phase, before spacetime emerges.
-/
structure DynamicsConfig (V : Type*) where
  /-- The color field triplet -/
  fields : ColorFieldTriplet V
  /-- Evolution configuration -/
  evolution : EvolutionConfig
  /-- Energy configuration -/
  energy : PreGeometricEnergyConfig

namespace DynamicsConfig

/-- The base phase advances according to evolution -/
noncomputable def currentBasePhase {V : Type*} (cfg : DynamicsConfig V) : ℝ :=
  cfg.fields.basePhase + cfg.evolution.omega * cfg.evolution.lambda

/-- Total energy of the configuration at a point -/
noncomputable def totalEnergyAt {V : Type*} (cfg : DynamicsConfig V) (x : V) : ℝ :=
  cfg.energy.totalEnergy (cfg.fields.amplitude_R x) (cfg.fields.amplitude_G x) (cfg.fields.amplitude_B x)

/-- Total energy is non-negative at every point -/
theorem totalEnergyAt_nonneg {V : Type*} (cfg : DynamicsConfig V) (x : V) :
    0 ≤ cfg.totalEnergyAt x := by
  unfold totalEnergyAt
  apply PreGeometricEnergyConfig.totalEnergy_nonneg
  · exact (cfg.fields.amplitudes_nonneg x).1
  · exact (cfg.fields.amplitudes_nonneg x).2.1
  · exact (cfg.fields.amplitudes_nonneg x).2.2

end DynamicsConfig

/-! ## Key Theorems

The following theorems establish the fundamental properties needed for
the Phase 0 → Phase 1 transition in the proof framework.
-/

/-- **Bootstrap Resolution Theorem (Strengthened, Issue 3)**

The internal evolution parameter λ provides a well-defined notion of
"evolution" without requiring a background spacetime metric.

**Substantive content:** This theorem establishes that:
1. Phase evolution exists (∃ phaseEvol)
2. The evolution satisfies dφ/dλ = ω (proven derivative)
3. Phase is monotonic when ω > 0 (time has a direction)
4. No metric tensor g_μν appears in any hypothesis

The "bootstrap" is broken because:
- Traditional QFT: ∂_t χ = iωχ requires time coordinate t from metric
- Here: ∂_λ χ = iωχ uses internal parameter λ defined by relative phases
- Physical time emerges later: t = ∫dλ/ω (see Theorem 0.2.2)

**What this theorem does NOT claim:**
- That λ equals physical time (it doesn't; t = λ/ω)
- That ω is determined here (it comes from energy minimization in Thm 0.2.2 §4.4)
- That this replaces Theorem 0.2.2 (this is infrastructure; 0.2.2 is the physics)
-/
theorem bootstrap_resolution {V : Type*} (cfg : DynamicsConfig V) :
    ∃ (phaseEvol : PhaseEvolution),
      phaseEvol.omega = cfg.evolution.omega ∧
      phaseEvol.phi_0 = cfg.fields.basePhase ∧
      -- Substantive property: derivative exists and equals ω
      deriv (fun lam => phaseEvol.phi_0 + phaseEvol.omega * lam) phaseEvol.lambda = phaseEvol.omega := by
  refine ⟨{ phi_0 := cfg.fields.basePhase,
            omega := cfg.evolution.omega,
            lambda := cfg.evolution.lambda }, rfl, rfl, ?_⟩
  -- Apply the phase_derivative theorem
  exact PhaseEvolution.phase_derivative _

/-- **Phase evolution is forward-directed when ω > 0**

This establishes that the internal parameter λ induces a well-defined
"arrow of time" before physical time emerges.
-/
theorem phase_evolution_monotonic {V : Type*} (cfg : DynamicsConfig V)
    (hω : cfg.evolution.omega > 0) :
    StrictMono (fun lam => cfg.fields.basePhase + cfg.evolution.omega * lam) := by
  intro a b hab
  simp only
  have : cfg.evolution.omega * a < cfg.evolution.omega * b := mul_lt_mul_of_pos_left hab hω
  linarith

/-- **Phase-Lock Stability Theorem**

When all three color amplitudes are equal, the total field vanishes
(creating a "node"), but the energy density remains non-zero.

This is the stable point at the center of the stella octangula.
-/
theorem phaseLock_stability {V : Type*} (cfg : DynamicsConfig V) (x : V)
    (h_eq_RG : cfg.fields.amplitude_R x = cfg.fields.amplitude_G x)
    (h_eq_GB : cfg.fields.amplitude_G x = cfg.fields.amplitude_B x)
    (h_nonzero : cfg.fields.amplitude_B x ≠ 0) :
    cfg.fields.totalField x = 0 ∧ cfg.fields.incoherentAmplitudeSq x > 0 := by
  constructor
  · exact ColorFieldTriplet.totalField_zero_when_equal cfg.fields x h_eq_RG h_eq_GB
  · unfold ColorFieldTriplet.incoherentAmplitudeSq
    have h : (cfg.fields.amplitude_B x)^2 > 0 := sq_pos_of_ne_zero h_nonzero
    have hR := sq_nonneg (cfg.fields.amplitude_R x)
    have hG := sq_nonneg (cfg.fields.amplitude_G x)
    linarith

/-- **Noether Circularity Resolution**

Energy is well-defined algebraically without requiring spacetime structure.
This resolves the circular dependency:

OLD: Energy ← Noether ← Spacetime integral ← Metric ← Energy
NEW: Energy is algebraic (sum of norms) → no metric required
-/
theorem noether_circularity_resolution {V : Type*} (cfg : DynamicsConfig V) (x : V) :
    ∃ (E : ℝ), E = cfg.totalEnergyAt x ∧ 0 ≤ E := by
  exact ⟨cfg.totalEnergyAt x, rfl, cfg.totalEnergyAt_nonneg x⟩

/-! ## Section 5: Time Emergence Infrastructure (Gaps 1, 3)

This section provides the conceptual and mathematical foundation for
how physical time emerges from the internal evolution parameter.
-/

/-- **Physical time from internal parameter (Gap 3)**

Physical time t is defined by counting oscillation cycles:
  t = λ / ω

where:
- λ is the internal evolution parameter (radians of accumulated phase)
- ω is the angular frequency (radians per unit time)

**Pre-gravitational regime:** ω = ω₀ is constant globally, so t is global.
**Post-gravitational regime:** ω_local(x) varies spatially, so t becomes local.

This structure represents the pre-gravitational case with constant ω.
-/
structure TimeEmergence where
  /-- Internal parameter (dimensionless: radians) -/
  lambda : ℝ
  /-- Angular frequency (dimension: [time]⁻¹) -/
  omega : ℝ
  /-- Frequency is positive -/
  omega_pos : 0 < omega

namespace TimeEmergence

/-- Emergent physical time: t = λ/ω -/
noncomputable def physicalTime (te : TimeEmergence) : ℝ :=
  te.lambda / te.omega

/-- Time is well-defined (ω > 0 ensures no division by zero) -/
theorem physicalTime_wellDefined (te : TimeEmergence) :
    te.physicalTime = te.lambda / te.omega ∧ te.omega ≠ 0 :=
  ⟨rfl, ne_of_gt te.omega_pos⟩

/-- Time increases with λ -/
theorem physicalTime_mono (te : TimeEmergence) :
    StrictMono (fun lam => lam / te.omega) := by
  intro a b hab
  exact div_lt_div_of_pos_right hab te.omega_pos

/-- Inverse relation: λ = ω·t -/
theorem lambda_from_time (te : TimeEmergence) :
    te.lambda = te.omega * te.physicalTime := by
  unfold physicalTime
  have h : te.omega ≠ 0 := ne_of_gt te.omega_pos
  field_simp [h]

end TimeEmergence

/-- **Spatial evolution note (Gap 1)**

The `EvolutionConfig` in this file uses a GLOBAL constant ω. This is appropriate
for Phase 0 (pre-gravitational), but after metric emergence (Theorem 5.2.1),
ω becomes position-dependent:

  ω_local(x) = ω₀ · √(-g₀₀(x))

where g₀₀ is the time-time component of the emergent metric.

This structure represents the extension to spatially-varying frequency.
-/
structure SpatialEvolutionConfig (V : Type*) where
  /-- Position-dependent frequency ω(x) -/
  omega_local : V → ℝ
  /-- Frequency is positive everywhere -/
  omega_local_pos : ∀ x, 0 < omega_local x
  /-- Reference frequency at spatial infinity -/
  omega_infinity : ℝ
  /-- Reference frequency is positive -/
  omega_infinity_pos : 0 < omega_infinity

namespace SpatialEvolutionConfig

/-- Local physical time at position x -/
noncomputable def localTime {V : Type*} (cfg : SpatialEvolutionConfig V) (x : V) (lam : ℝ) : ℝ :=
  lam / cfg.omega_local x

/-- Gravitational time dilation factor: ω_local(x) / ω_∞ -/
noncomputable def timeDilationFactor {V : Type*} (cfg : SpatialEvolutionConfig V) (x : V) : ℝ :=
  cfg.omega_local x / cfg.omega_infinity

/-- Time dilation is positive -/
theorem timeDilationFactor_pos {V : Type*} (cfg : SpatialEvolutionConfig V) (x : V) :
    0 < cfg.timeDilationFactor x := by
  unfold timeDilationFactor
  exact div_pos (cfg.omega_local_pos x) cfg.omega_infinity_pos

end SpatialEvolutionConfig

/-! ## Section 6: Sakaguchi-Kuramoto Connection (Gap 2)

The phase dynamics of the three color fields are governed by the
Sakaguchi-Kuramoto (SK) model — a generalization of the Kuramoto model
for coupled oscillators with phase lag.

Connection to this infrastructure:
- `Phase120Config` in Tactics/Phase120.lean: Equilibrium configuration
- `coupling_R/G/B`: SK coupling terms (vanish at equilibrium)
- `JacobianAtEquilibrium`: Stability analysis (eigenvalues < 0 ⟹ stable)

The 120° phase separation emerges as the unique stable equilibrium.
-/

/-- **Connection to Sakaguchi-Kuramoto dynamics (Gap 2)**

This definition connects our `PhaseConfig` to the SK stability analysis
in `Tactics.Phase120`. At equilibrium (120° separation), all SK coupling
terms vanish and the Jacobian eigenvalues are negative.
-/
def isSkEquilibrium (cfg : PhaseConfig) : Prop :=
  cfg.isValid ∧  -- 120° separation
  coupling_R cfg.phi_R cfg.phi_G cfg.phi_B = 0 ∧
  coupling_G cfg.phi_R cfg.phi_G cfg.phi_B = 0 ∧
  coupling_B cfg.phi_R cfg.phi_G cfg.phi_B = 0

/-- Valid phase configurations are SK equilibria -/
theorem valid_is_sk_equilibrium (cfg : PhaseConfig) (hValid : cfg.isValid) :
    isSkEquilibrium cfg := by
  unfold isSkEquilibrium
  have ⟨hRG, hGB⟩ := hValid
  refine ⟨hValid, ?_, ?_, ?_⟩
  -- Show all coupling terms vanish at 120° separation
  · unfold coupling_R
    -- φ_G - φ_R - 2π/3 = 2π/3 - 2π/3 = 0
    have h1 : cfg.phi_G - cfg.phi_R - 2 * Real.pi / 3 = 0 := by linarith
    -- φ_B - φ_R - 4π/3 = (φ_G + 2π/3) - φ_R - 4π/3 = 2π/3 + 2π/3 - 4π/3 = 0
    have h2 : cfg.phi_B - cfg.phi_R - 4 * Real.pi / 3 = 0 := by linarith
    simp [h1, h2, Real.sin_zero]
  · unfold coupling_G
    have h1 : cfg.phi_R - cfg.phi_G + 2 * Real.pi / 3 = 0 := by linarith
    have h2 : cfg.phi_B - cfg.phi_G - 2 * Real.pi / 3 = 0 := by linarith
    simp [h1, h2, Real.sin_zero]
  · unfold coupling_B
    have h1 : cfg.phi_R - cfg.phi_B + 4 * Real.pi / 3 = 0 := by linarith
    have h2 : cfg.phi_G - cfg.phi_B + 2 * Real.pi / 3 = 0 := by linarith
    simp [h1, h2, Real.sin_zero]

/-! ## Section 7: Pressure Function Connection (Gap 4)

The amplitudes a_c(x) in this dynamics infrastructure are related to
the pressure functions P_c(x) from Definition 0.1.3:

  a_c(x) = a₀ · P_c(x) = a₀ / (|x - x_c|² + ε²)

where x_c is the color vertex position and ε is the regularization parameter.
-/

/-- **Pressure-modulated amplitude configuration (Gap 4)**

This connects the abstract `ColorFieldTriplet` to the concrete pressure
functions from Definition 0.1.3.
-/
structure PressureModulatedTriplet where
  /-- Base amplitude scale a₀ -/
  a₀ : ℝ
  /-- Base amplitude is positive -/
  a₀_pos : 0 < a₀
  /-- Regularization parameter ε > 0 -/
  ε : ℝ
  /-- Regularization is positive -/
  ε_pos : 0 < ε

namespace PressureModulatedTriplet

open ChiralGeometrogenesis.Phase0.Theorem_0_2_1
open ChiralGeometrogenesis.Phase0.Definition_0_1_4
open ChiralGeometrogenesis.PureMath.Polyhedra (Point3D)

/-- Amplitude at position x for red field: a_R(x) = a₀ / (|x - x_R|² + ε²) -/
noncomputable def amplitude_R (cfg : PressureModulatedTriplet) (x : Point3D) : ℝ :=
  cfg.a₀ / (distSq x vertexR + cfg.ε ^ 2)

/-- Amplitude at position x for green field -/
noncomputable def amplitude_G (cfg : PressureModulatedTriplet) (x : Point3D) : ℝ :=
  cfg.a₀ / (distSq x vertexG + cfg.ε ^ 2)

/-- Amplitude at position x for blue field -/
noncomputable def amplitude_B (cfg : PressureModulatedTriplet) (x : Point3D) : ℝ :=
  cfg.a₀ / (distSq x vertexB + cfg.ε ^ 2)

/-- All pressure-modulated amplitudes are positive -/
theorem amplitudes_pos (cfg : PressureModulatedTriplet) (x : Point3D) :
    0 < cfg.amplitude_R x ∧ 0 < cfg.amplitude_G x ∧ 0 < cfg.amplitude_B x := by
  unfold amplitude_R amplitude_G amplitude_B
  have hε2_pos : 0 < cfg.ε ^ 2 := sq_pos_of_pos cfg.ε_pos
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply div_pos cfg.a₀_pos
    apply add_pos_of_nonneg_of_pos
    · exact distSq_nonneg _ _
    · exact hε2_pos

/-- Convert to a ColorFieldTriplet at a fixed point -/
noncomputable def toColorFieldTriplet (cfg : PressureModulatedTriplet) (basePhase : ℝ) :
    ColorFieldTriplet Point3D where
  amplitude_R := cfg.amplitude_R
  amplitude_G := cfg.amplitude_G
  amplitude_B := cfg.amplitude_B
  basePhase := basePhase
  amplitudes_nonneg := fun x => by
    have ⟨hR, hG, hB⟩ := cfg.amplitudes_pos x
    exact ⟨le_of_lt hR, le_of_lt hG, le_of_lt hB⟩

end PressureModulatedTriplet

end ChiralGeometrogenesis.Foundations
