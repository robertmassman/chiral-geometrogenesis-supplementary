/-
  Constants/Neutrino.lean — Neutrino mixing constants, PMNS parameters,
  and mass squared differences.

  Section 14 from the original Constants.lean.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Constants

open Real

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 14: NEUTRINO MIXING CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Neutrino mixing angles and related parameters from NuFIT 6.0.
    These are used in Phase 8 predictions (θ₁₃, θ₂₃ corrections).

    Reference: NuFIT 6.0 (2024), Normal Ordering
-/

/-! ### Wolfenstein Parameter λ

The Wolfenstein parameter λ = sin θ_C (sine of Cabibbo angle) governs quark mixing.
We maintain two values:

| Definition | Value | Source | Use |
|------------|-------|--------|-----|
| `wolfenstein_lambda_geometric` | 0.22451 | CG prediction: (1/φ³) × sin(72°) | Theoretical |
| `wolfenstein_lambda_PDG` | 0.22497 ± 0.00070 | PDG 2024 CKM fit | Experimental |

Agreement: |0.22497 - 0.22451| / 0.00070 ≈ 0.65σ (excellent)
-/

/-- Wolfenstein parameter (GEOMETRIC PREDICTION): λ_geo = (1/φ³) × sin(72°) ≈ 0.22451.

    **Physical meaning:**
    The sine of the Cabibbo angle, governing quark mixing strength.

    **Derivation (Chiral Geometrogenesis):**
    λ = (1/φ³) × sin(72°) where:
    - 1/φ³ ≈ 0.2361 from three icosahedral projections (ThreePhiFactors.lean)
    - sin(72°) ≈ 0.9511 from pentagonal angular factor (Theorem_3_1_1.lean)
    - Product: 0.2361 × 0.9511 ≈ 0.22451

    **Reference:** ThreePhiFactors.lean, Lemma 3.1.2a -/
noncomputable def wolfenstein_lambda_geometric : ℝ := 0.22451

/-- Wolfenstein parameter (PDG OBSERVED): λ_PDG = 0.22497 ± 0.00070.

    **Physical meaning:**
    Experimentally measured value from global CKM matrix fit.

    **Citation:** PDG 2024, "CKM Quark-Mixing Matrix"
    - Central value: 0.22497
    - Uncertainty: ± 0.00070 (1σ)

    **Note:** The Wolfenstein parameterization value (0.22650 ± 0.00048) differs
    slightly from the CKM fit value. We use the CKM fit for comparison.

    **Reference:** https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf -/
noncomputable def wolfenstein_lambda_PDG : ℝ := 0.22497

/-- PDG uncertainty on λ (1σ) -/
noncomputable def wolfenstein_lambda_PDG_uncertainty : ℝ := 0.00070

/-- Legacy alias for geometric prediction (backward compatibility) -/
noncomputable abbrev wolfenstein_lambda : ℝ := wolfenstein_lambda_geometric

/-- λ_geo > 0 -/
theorem wolfenstein_lambda_geometric_pos : wolfenstein_lambda_geometric > 0 := by
  unfold wolfenstein_lambda_geometric; norm_num

/-- Convenience accessor: wolfenstein_lambda > 0 -/
theorem wolfenstein_lambda_pos : wolfenstein_lambda > 0 := wolfenstein_lambda_geometric_pos

/-- λ_geo < 1 (physical constraint) -/
theorem wolfenstein_lambda_geometric_lt_one : wolfenstein_lambda_geometric < 1 := by
  unfold wolfenstein_lambda_geometric; norm_num

/-- λ_PDG > 0 -/
theorem wolfenstein_lambda_PDG_pos : wolfenstein_lambda_PDG > 0 := by
  unfold wolfenstein_lambda_PDG; norm_num

/-- λ_PDG < 1 (physical constraint) -/
theorem wolfenstein_lambda_PDG_lt_one : wolfenstein_lambda_PDG < 1 := by
  unfold wolfenstein_lambda_PDG; norm_num

/-- Agreement: |λ_geo - λ_PDG| < 0.001 (sub-permille) -/
theorem wolfenstein_lambda_agreement :
    |wolfenstein_lambda_geometric - wolfenstein_lambda_PDG| < 0.001 := by
  unfold wolfenstein_lambda_geometric wolfenstein_lambda_PDG
  norm_num

/-- Statistical agreement: deviation < 1σ -/
theorem wolfenstein_lambda_within_1sigma :
    |wolfenstein_lambda_geometric - wolfenstein_lambda_PDG| <
    wolfenstein_lambda_PDG_uncertainty := by
  unfold wolfenstein_lambda_geometric wolfenstein_lambda_PDG wolfenstein_lambda_PDG_uncertainty
  norm_num

/-- Solar mixing angle: θ₁₂ = 33.41° (NuFIT 6.0, normal ordering).

    **Physical meaning:**
    The angle governing solar neutrino oscillations.

    **Citation:** NuFIT 6.0 (2024) -/
noncomputable def theta12_deg : ℝ := 33.41

/-- θ₁₂ in radians -/
noncomputable def theta12_rad : ℝ := theta12_deg * Real.pi / 180

/-- θ₁₂ > 0 -/
theorem theta12_pos : theta12_deg > 0 := by unfold theta12_deg; norm_num

/-- Reactor mixing angle: θ₁₃ = 8.54° (NuFIT 6.0, normal ordering).

    **Physical meaning:**
    The smallest mixing angle, discovered in 2012.
    TBM prediction was θ₁₃ = 0°.

    **Citation:** NuFIT 6.0 (2024) -/
noncomputable def theta13_deg : ℝ := 8.54

/-- θ₁₃ in radians -/
noncomputable def theta13_rad : ℝ := theta13_deg * Real.pi / 180

/-- θ₁₃ > 0 -/
theorem theta13_pos : theta13_deg > 0 := by unfold theta13_deg; norm_num

/-- Atmospheric mixing angle: θ₂₃ = 49.1° (NuFIT 6.0, observed).

    **Physical meaning:**
    Governs atmospheric neutrino oscillations.
    TBM prediction is 45° (maximal mixing).

    **Citation:** NuFIT 6.0 (2024), normal ordering, higher octant -/
noncomputable def theta23_observed_deg : ℝ := 49.1

/-- θ₂₃ observed in radians -/
noncomputable def theta23_observed_rad : ℝ := theta23_observed_deg * Real.pi / 180

/-- Experimental uncertainty in θ₂₃: ±1.0° -/
noncomputable def theta23_uncertainty_deg : ℝ := 1.0

/-- θ₂₃ > 0 -/
theorem theta23_observed_pos : theta23_observed_deg > 0 := by
  unfold theta23_observed_deg; norm_num

/-- sin²θ₂₃ observed value: 0.573 ± 0.020 (NuFIT 6.0).

    **Citation:** NuFIT 6.0 (2024) -/
noncomputable def sin_sq_theta23_observed : ℝ := 0.573

/-- Uncertainty in sin²θ₂₃: ±0.020 -/
noncomputable def sin_sq_theta23_uncertainty : ℝ := 0.020

/-- sin²θ₂₃ > 0 -/
theorem sin_sq_theta23_pos : sin_sq_theta23_observed > 0 := by
  unfold sin_sq_theta23_observed; norm_num

/-- Tribimaximal θ₂₃ prediction: 45° (maximal mixing).

    **Physical meaning:**
    The A₄ symmetric TBM pattern predicts sin²θ₂₃ = 1/2.

    **Citation:** Harrison, Perkins, Scott (2002) -/
noncomputable def theta23_TBM_deg : ℝ := 45

/-- TBM sin²θ₂₃ = 1/2 -/
noncomputable def sin_sq_theta23_TBM : ℝ := 1 / 2

/-- Leptonic CP phase: δ_CP = 197° (NuFIT 6.0 best fit).

    **Physical meaning:**
    Source of CP violation in neutrino sector.

    **Citation:** NuFIT 6.0 (2024) -/
noncomputable def delta_CP_deg : ℝ := 197

/-- δ_CP in radians -/
noncomputable def delta_CP_rad : ℝ := delta_CP_deg * Real.pi / 180

/-- Muon mass: m_μ = 105.6584 MeV (PDG 2024) -/
noncomputable def m_muon_MeV : ℝ := 105.6584

/-- m_μ > 0 -/
theorem m_muon_pos : m_muon_MeV > 0 := by unfold m_muon_MeV; norm_num

/-- Tau mass: m_τ = 1776.86 MeV (PDG 2024) -/
noncomputable def m_tau_MeV : ℝ := 1776.86

/-- m_τ > 0 -/
theorem m_tau_pos : m_tau_MeV > 0 := by unfold m_tau_MeV; norm_num

/-- Mass ratio function f(x) = (1-x)/(1+x) for charged lepton corrections.

    **Physical meaning:**
    Kinematic factor appearing in charged lepton contributions to PMNS.

    **Citation:** Antusch & King (2005) -/
noncomputable def mass_ratio_function (x : ℝ) : ℝ := (1 - x) / (1 + x)

/-- f(m_μ/m_τ) ≈ 0.889 -/
noncomputable def f_mu_tau : ℝ := mass_ratio_function (m_muon_MeV / m_tau_MeV)

/-! ### NuFIT 6.0 PMNS Observables (Extension 3.1.2d)

Additional NuFIT 6.0 values needed for the complete PMNS parameter derivation.
Two datasets are maintained: IC19 (without SK atmospheric) and IC24 (with SK atmospheric).

Reference: NuFIT 6.0, arXiv:2410.05380 (Esteban et al. 2024)
-/

/-- sin²θ₁₂ observed (NuFIT 6.0, IC19, NO): 0.307 ± 0.012.

    **Physical meaning:**
    The solar mixing angle squared sine, governing ν_e ↔ ν₂ oscillations.

    **Citation:** NuFIT 6.0 (2024), Table 1, Normal Ordering, IC19 -/
noncomputable def sin_sq_theta12_observed : ℝ := 0.307

/-- sin²θ₁₂ > 0 -/
theorem sin_sq_theta12_observed_pos : sin_sq_theta12_observed > 0 := by
  unfold sin_sq_theta12_observed; norm_num

/-- sin²θ₁₂ < 1 -/
theorem sin_sq_theta12_observed_lt_one : sin_sq_theta12_observed < 1 := by
  unfold sin_sq_theta12_observed; norm_num

/-- Uncertainty in sin²θ₁₂: ±0.012 (1σ) -/
noncomputable def sin_sq_theta12_uncertainty : ℝ := 0.012

/-- NuFIT 6.0 θ₁₂ best fit: 33.68° ± 0.72° (IC19, NO).

    **Note:** This differs slightly from the generic theta12_deg = 33.41° above,
    which may use a different NuFIT extraction. For Extension 3.1.2d comparisons,
    use this value.

    **Citation:** NuFIT 6.0 (2024), IC19 -/
noncomputable def theta12_nufit60_IC19_deg : ℝ := 33.68

/-- θ₁₂ uncertainty: ±0.72° (1σ) -/
noncomputable def theta12_nufit60_uncertainty_deg : ℝ := 0.72

/-- sin²θ₁₃ observed (NuFIT 6.0, IC19, NO): 0.02195 ± 0.00054.

    **Citation:** NuFIT 6.0 (2024), IC19, Normal Ordering -/
noncomputable def sin_sq_theta13_observed : ℝ := 0.02195

/-- sin²θ₁₃ > 0 -/
theorem sin_sq_theta13_observed_pos : sin_sq_theta13_observed > 0 := by
  unfold sin_sq_theta13_observed; norm_num

/-- NuFIT 6.0 δ_CP best fit (IC19, NO): 177° ± 20°.

    **Note:** IC19 (without SK atmospheric) gives δ_CP near CP conservation.

    **Citation:** NuFIT 6.0 (2024), IC19 -/
noncomputable def delta_CP_nufit60_IC19_deg : ℝ := 177

/-- NuFIT 6.0 δ_CP best fit (IC24, NO): 212° ± 34°.

    **Note:** IC24 (with SK atmospheric) gives significant CP violation.

    **Citation:** NuFIT 6.0 (2024), IC24 -/
noncomputable def delta_CP_nufit60_IC24_deg : ℝ := 212

/-- Neutrino mass squared difference Δm²₂₁ = 7.49 × 10⁻⁵ eV² (NuFIT 6.0).

    **Physical meaning:**
    The solar mass splitting governing ν_e → ν_μ oscillations in the Sun.
    This value is common to both IC19 and IC24 datasets.

    **Citation:** NuFIT 6.0 (2024), Normal Ordering -/
noncomputable def delta_m2_21_eV2 : ℝ := 7.49e-5

/-- Δm²₂₁ > 0 -/
theorem delta_m2_21_pos : delta_m2_21_eV2 > 0 := by
  unfold delta_m2_21_eV2; norm_num

/-- Uncertainty in Δm²₂₁: ±0.19 × 10⁻⁵ eV² (1σ range: 7.30–7.68) -/
noncomputable def delta_m2_21_uncertainty_eV2 : ℝ := 0.19e-5

/-- Neutrino mass squared difference Δm²₃₁ = 2.534 × 10⁻³ eV² (NuFIT 6.0, IC19, NO).

    **Physical meaning:**
    The atmospheric mass splitting governing ν_μ → ν_τ oscillations.
    Positive value indicates normal mass ordering (m₃ > m₂ > m₁).

    **Citation:** NuFIT 6.0 (2024), IC19, Normal Ordering -/
noncomputable def delta_m2_31_IC19_eV2 : ℝ := 2.534e-3

/-- Δm²₃₁ > 0 (normal ordering) -/
theorem delta_m2_31_IC19_pos : delta_m2_31_IC19_eV2 > 0 := by
  unfold delta_m2_31_IC19_eV2; norm_num

/-- Observed mass squared ratio r = Δm²₂₁/Δm²₃₁ ≈ 0.0296 (NuFIT 6.0, IC19).

    **Physical meaning:**
    The ratio of solar to atmospheric mass splittings. A key structural
    parameter predicted by the A₄ → Z₃ breaking pattern.

    **Calculation:** 7.49e-5 / 2.534e-3 = 0.02956 -/
noncomputable def mass_squared_ratio_observed : ℝ := delta_m2_21_eV2 / delta_m2_31_IC19_eV2

/-- r_obs > 0 -/
theorem mass_squared_ratio_observed_pos : mass_squared_ratio_observed > 0 := by
  unfold mass_squared_ratio_observed
  exact div_pos delta_m2_21_pos delta_m2_31_IC19_pos

end ChiralGeometrogenesis.Constants
