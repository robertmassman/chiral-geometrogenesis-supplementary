/-
  Phase0/Theorem_0_2_1/Normalization.lean

  Normalization Constant a₀ = f_π · ε² (§12.4)

  The normalization constant a₀ is fixed to physical observables through the
  pion decay constant f_π:

    a₀ = f_π · ε²

  Contains:
  - pionDecayConstant definition
  - NormalizationParameters structure
  - normalizationConstant and related theorems
  - vertex_amplitude_equals_f_pi
  - vertex_energy_from_normalization

  Reference: docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md §12.4
-/

import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.Core
import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.Integrability

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase0.Theorem_0_2_1

open ChiralGeometrogenesis
open ChiralGeometrogenesis.PureMath.Polyhedra
open Real

/-! ## Normalization Constant a₀ = f_π · ε² (§12.4 of Theorem 0.2.1)

The normalization constant a₀ is fixed to physical observables through the
pion decay constant f_π:

  a₀ = f_π · ε²

where:
- f_π = 92.1 ± 0.6 MeV (Peskin-Schroeder convention, PDG 2024)
- ε is the regularization parameter with dimensions [length]
- a₀ has dimensions [length] when physical units are restored

**Physical Meaning:**
- f_π sets the ENERGY SCALE of chiral symmetry breaking
- ε² provides the GEOMETRIC FACTOR from regularization
- The combination ensures maximum field amplitude (at a vertex) equals f_π
-/

/-- The pion decay constant f_π in natural units.

    Physical value: f_π = 92.1 ± 0.6 MeV (Peskin-Schroeder convention)

    **UNITS (Natural Units with ℏ = c = 1):**
    - [f_π] = [energy] = [mass] = [length]⁻¹ = [time]⁻¹
    - In SI: f_π ≈ 92.1 MeV ≈ 1.48 × 10⁻¹¹ J
    - As inverse length: f_π ≈ (2.1 fm)⁻¹

    Note: The PDG standard convention gives f_{π±} = 130.2 MeV,
    differing by √2. We use the Peskin-Schroeder convention.

    **SOURCE:** PDG 2024, Particle Data Group -/
noncomputable def pionDecayConstant : ℝ := 92.1  -- MeV in natural units

/-- Structure capturing the physical normalization parameters -/
structure NormalizationParameters where
  /-- Pion decay constant (energy scale) -/
  f_pi : ℝ
  /-- Regularization parameter (length scale) -/
  ε : ℝ
  /-- f_π is positive -/
  f_pi_pos : 0 < f_pi
  /-- ε is positive -/
  ε_pos : 0 < ε

/-- The normalization constant a₀ = f_π · ε² (Definition 0.1.2 §5.1) -/
noncomputable def normalizationConstant (params : NormalizationParameters) : ℝ :=
  params.f_pi * params.ε ^ 2

/-- Alternative form: normalization from f_π and ε directly -/
noncomputable def a₀_from_f_pi_epsilon (f_pi ε : ℝ) : ℝ := f_pi * ε ^ 2

/-- The normalization constant is positive -/
theorem normalizationConstant_pos (params : NormalizationParameters) :
    0 < normalizationConstant params := by
  unfold normalizationConstant
  apply mul_pos params.f_pi_pos (sq_pos_of_pos params.ε_pos)

/-- Alternative form positivity -/
theorem a₀_from_f_pi_epsilon_pos (f_pi ε : ℝ) (hf : 0 < f_pi) (hε : 0 < ε) :
    0 < a₀_from_f_pi_epsilon f_pi ε := by
  unfold a₀_from_f_pi_epsilon
  apply mul_pos hf (sq_pos_of_pos hε)

/-- Scaling property: a₀ scales quadratically with ε -/
theorem normalization_scaling (f_pi ε k : ℝ) (hk : 0 < k) :
    a₀_from_f_pi_epsilon f_pi (k * ε) = k^2 * a₀_from_f_pi_epsilon f_pi ε := by
  unfold a₀_from_f_pi_epsilon
  ring

/-- At a vertex, the amplitude reaches its maximum value f_π -/
theorem vertex_amplitude_equals_f_pi (params : NormalizationParameters) :
    normalizationConstant params * vertexPressure params.ε = params.f_pi := by
  unfold normalizationConstant vertexPressure
  have hε_ne : params.ε ≠ 0 := ne_of_gt params.ε_pos
  have hε2_ne : params.ε ^ 2 ≠ 0 := pow_ne_zero 2 hε_ne
  field_simp [hε2_ne]

/-- The energy density at vertex equals f_π² -/
theorem vertex_energy_from_normalization (params : NormalizationParameters) :
    energyAtVertex (normalizationConstant params) params.ε = params.f_pi ^ 2 := by
  unfold energyAtVertex normalizationConstant vertexPressure
  have hε_ne : params.ε ≠ 0 := ne_of_gt params.ε_pos
  have hε2_ne : params.ε ^ 2 ≠ 0 := pow_ne_zero 2 hε_ne
  have hε4_ne : params.ε ^ 4 ≠ 0 := pow_ne_zero 4 hε_ne
  field_simp [hε2_ne, hε4_ne]

/-! ### Physical interpretation

The normalization ensures that the chiral field amplitude at vertices equals
the pion decay constant f_π, which is the characteristic scale of chiral
symmetry breaking in QCD.
-/

/-- Vertex amplitude reaches f_π with normalization a₀ = f_π · ε² -/
theorem normalization_vertex_amplitude (f_pi ε : ℝ) (hf : 0 < f_pi) (hε : 0 < ε) :
    a₀_from_f_pi_epsilon f_pi ε * (1 / ε^2) = f_pi := by
  simp only [a₀_from_f_pi_epsilon]
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hε2_ne : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε_ne
  field_simp [hε2_ne]

/-- Physical energy scale at vertex is f_π² -/
theorem normalization_energy_scale (f_pi ε : ℝ) (hf : 0 < f_pi) (hε : 0 < ε) :
    (a₀_from_f_pi_epsilon f_pi ε)^2 * (1 / ε^2)^2 = f_pi^2 := by
  simp only [a₀_from_f_pi_epsilon]
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hε2_ne : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε_ne
  field_simp [hε2_ne]

/-- Connection to Definition 0.1.2 §5.1: verification chain -/
theorem normalization_verification_chain :
    (∀ (f_pi ε : ℝ), a₀_from_f_pi_epsilon f_pi ε = f_pi * ε^2) ∧
    (∀ (f_pi ε : ℝ), 0 < ε → a₀_from_f_pi_epsilon f_pi ε / ε^2 = f_pi) ∧
    (∀ (f_pi ε : ℝ), 0 < ε → (a₀_from_f_pi_epsilon f_pi ε / ε^2)^2 = f_pi^2) := by
  refine ⟨?_, ?_, ?_⟩
  · intros f_pi ε
    rfl
  · intros f_pi ε hε
    simp only [a₀_from_f_pi_epsilon]
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    have hε2_ne : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε_ne
    field_simp [hε2_ne]
  · intros f_pi ε hε
    simp only [a₀_from_f_pi_epsilon]
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    have hε2_ne : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε_ne
    field_simp [hε2_ne]

/-! ## Dimensional Analysis and Natural Units Convention

This section provides a comprehensive dimensional analysis for all quantities
in the Chiral Geometrogenesis framework. Understanding dimensions is essential
for connecting Lean formalizations to physical predictions.

### Natural Units Convention (ℏ = c = 1)

In natural units, there is only ONE fundamental dimension. We choose [energy]:

| Quantity        | Symbol | SI Dimension           | Natural Dimension |
|-----------------|--------|------------------------|-------------------|
| Energy          | E      | kg⋅m²/s²              | [energy]          |
| Mass            | m      | kg                     | [energy]          |
| Length          | L      | m                      | [energy]⁻¹        |
| Time            | t      | s                      | [energy]⁻¹        |
| Momentum        | p      | kg⋅m/s                | [energy]          |
| Angular freq.   | ω      | s⁻¹                   | [energy]          |

**Conversion factors:**
- 1 MeV = 1.602 × 10⁻¹³ J
- 1 MeV⁻¹ = 0.197 fm (length)
- 1 MeV⁻¹ = 6.58 × 10⁻²² s (time)

### Framework Quantities and Their Dimensions

| Quantity                | Symbol    | Natural Dimension      | Notes                          |
|-------------------------|-----------|------------------------|--------------------------------|
| Pion decay constant     | f_π       | [energy]               | Sets the chiral scale          |
| Regularization param.   | ε         | [energy]⁻¹             | UV cutoff length               |
| Normalization constant  | a₀        | [energy]⁻¹             | a₀ = f_π ⋅ ε²                  |
| Pressure function       | P_c(x)    | dimensionless          | Regularized 1/r profile        |
| Chiral field            | χ_c(x)    | [energy]^(1/2)         | |χ|² has dim [energy]           |
| Energy density          | ε(x)      | [energy]⁴              | [energy]/[volume]              |
| Phase                   | φ_c       | dimensionless          | Radians                        |
| Internal time           | τ         | dimensionless          | Evolution parameter            |
| Physical time           | t         | [energy]⁻¹             | t = τ/ω                        |

### Dimensional Verification

The key consistency checks for the normalization are:

1. **Vertex amplitude = f_π:**
   [a₀] × [1/ε²] = [energy]⁻¹ × [energy]² = [energy] ✓

2. **Energy density at vertex = f_π²:**
   [a₀²/ε⁴] = [energy]⁻² × [energy]⁴ = [energy]² = [χ]⁴ → integrable ✓

3. **Total energy is finite:**
   ∫ [energy]⁴ × [length]³ = [energy]⁴ × [energy]⁻³ = [energy] ✓

**Note on Lean Formalization:**
In Lean, all quantities are represented as ℝ-valued without explicit unit tracking.
The dimensional analysis above serves as a meta-level consistency check and should
be verified when connecting formal proofs to physical predictions.
-/

/-- Dimensional consistency: a₀ has the same dimensions as ε (both [energy]⁻¹).

This is a type-level reminder that in natural units:
- [f_π] = [energy]
- [ε] = [energy]⁻¹
- [a₀] = [f_π] × [ε]² = [energy] × [energy]⁻² = [energy]⁻¹

The formula a₀ = f_π × ε² is dimensionally consistent. -/
theorem dimensional_consistency_a0 :
    ∀ (f_pi ε : ℝ), a₀_from_f_pi_epsilon f_pi ε = f_pi * ε * ε := by
  intros f_pi ε
  simp only [a₀_from_f_pi_epsilon, sq]
  ring

/-- The ratio a₀/ε² = f_π recovers the energy scale.

Dimensional check: [a₀]/[ε²] = [energy]⁻¹/[energy]⁻² = [energy] = [f_π] ✓ -/
theorem energy_scale_recovery (f_pi ε : ℝ) (hε : 0 < ε) :
    a₀_from_f_pi_epsilon f_pi ε / ε^2 = f_pi := by
  simp only [a₀_from_f_pi_epsilon]
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hε2_ne : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε_ne
  field_simp [hε2_ne]

/-- Physical reference values for dimensional estimates.

These are the numerical values used to convert between Lean's dimensionless
ℝ values and physical predictions:

| Constant        | Symbol  | Value                     | Uncertainty |
|-----------------|---------|---------------------------|-------------|
| Pion decay      | f_π     | 92.1 MeV                  | ± 0.6 MeV   |
| Proton mass     | m_p     | 938.3 MeV                 | PDG 2024    |
| Ratio           | m_p/f_π | 10.19                     | ≈ 10        |

The framework predicts m_p ∝ f_π through the phase-gradient mass generation mechanism.
-/
noncomputable def protonMassReference : ℝ := 938.3  -- MeV

/-- The proton-to-pion ratio is approximately 10 -/
theorem proton_pion_ratio_approx :
    protonMassReference / pionDecayConstant > 10 ∧
    protonMassReference / pionDecayConstant < 11 := by
  simp only [protonMassReference, pionDecayConstant]
  constructor <;> norm_num

/-! ### Summary: Connecting Lean to Physics

When translating Lean theorems to physical predictions:

1. **Identify the dimensionless combination** in the Lean proof
2. **Restore dimensions** using the natural units table above
3. **Substitute numerical values** for f_π, ε, etc.
4. **Convert to SI units** if needed for comparison with experiment

Example workflow:
- Lean proves: `vertex_amplitude_equals_f_pi` with a₀ × P(0) = f_π
- Dimension check: [a₀] × [P] = [energy]⁻¹ × [1] × [ε⁻²] ... needs P to have [ε⁻²]
- Actually: P(0) = 1/ε² so [P(0)] = [energy]², giving [a₀ × P] = [energy] ✓
- Physical value: f_π = 92.1 MeV sets the chiral symmetry breaking scale

This dimensional analysis ensures our formal proofs connect correctly to
measurable physics.
-/

end ChiralGeometrogenesis.Phase0.Theorem_0_2_1
