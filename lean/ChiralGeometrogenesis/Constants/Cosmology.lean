/-
  Constants/Cosmology.lean — Dark matter, cosmological density fractions,
  precision cosmological predictions, and anthropic bounds.

  Sections 15a, 16, 17, 17a, 15-anth from the original Constants.lean.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import ChiralGeometrogenesis.Constants.Core
import ChiralGeometrogenesis.Constants.Geometry
import ChiralGeometrogenesis.Constants.Electroweak

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Constants

open Real

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 15: DARK MATTER AND COSMOLOGY CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Constants for dark matter predictions (Prediction 8.3.1).
    Reference: docs/proofs/Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md
-/

-- NOTE: v_H_GeV, v_H_GeV_pos, m_h_GeV, m_h_GeV_pos relocated to Electroweak.lean

/-- Observed dark matter density: Ω_{DM} h² = 0.12.

    **Physical meaning:**
    Dark matter contribution to critical density times h².

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def Omega_DM_h2 : ℝ := 0.12

/-- Ω_{DM} h² > 0 -/
theorem Omega_DM_h2_pos : Omega_DM_h2 > 0 := by unfold Omega_DM_h2; norm_num

/-- Observed baryon density: Ω_b h² = 0.022.

    **Citation:** Planck 2018 -/
noncomputable def Omega_b_h2 : ℝ := 0.022

/-- Ω_b h² > 0 -/
theorem Omega_b_h2_pos : Omega_b_h2 > 0 := by unfold Omega_b_h2; norm_num

/-- Dark matter to baryon ratio: Ω_{DM}/Ω_b ≈ 5.5 -/
noncomputable def DM_baryon_ratio : ℝ := Omega_DM_h2 / Omega_b_h2

/-- Observed baryon asymmetry: η_B = 6.1 × 10⁻¹⁰.

    **Physical meaning:**
    Baryon-to-photon ratio from CMB measurements.

    **Citation:** Planck 2018 -/
noncomputable def eta_B : ℝ := 6.1e-10

/-- η_B > 0 -/
theorem eta_B_pos : eta_B > 0 := by unfold eta_B; norm_num

/-- Proton mass: m_p = 0.938 GeV.

    **Citation:** PDG 2024 -/
noncomputable def m_p_GeV : ℝ := 0.938

/-- m_p > 0 -/
theorem m_p_GeV_pos : m_p_GeV > 0 := by unfold m_p_GeV; norm_num

/-- Skyrme parameter: e ≈ 4.84.

    **Physical meaning:**
    Dimensionless coupling that stabilizes Skyrme solitons.

    **Citation:** Adkins-Nappi-Witten, Nucl. Phys. B228, 552 (1983) -/
noncomputable def skyrme_e : ℝ := 4.84

/-- e > 0 -/
theorem skyrme_e_pos : skyrme_e > 0 := by unfold skyrme_e; norm_num

/-- Nuclear form factor: f_N ≈ 0.30.

    **Physical meaning:**
    Effective Higgs-nucleon coupling strength.

    **Citation:** Lattice QCD -/
noncomputable def f_N_nuclear : ℝ := 0.30

/-- f_N > 0 -/
theorem f_N_nuclear_pos : f_N_nuclear > 0 := by unfold f_N_nuclear; norm_num

/-- Entropy-to-photon ratio: s_0/n_γ ≈ 7.04.

    **Physical meaning:**
    Relates number density to entropy density in early universe.

    **Citation:** Standard cosmology -/
noncomputable def entropy_photon_ratio : ℝ := 7.04

/-- s_0/n_γ > 0 -/
theorem entropy_photon_ratio_pos : entropy_photon_ratio > 0 := by
  unfold entropy_photon_ratio; norm_num

/-- LZ direct detection bound at 2 TeV: σ_{SI} < 10⁻⁴⁶ cm².

    **Citation:** LZ Collaboration, PRL 135, 011802 (2025), arXiv:2410.17036 -/
noncomputable def LZ_bound_cm2 : ℝ := 1e-46

/-- LZ bound > 0 -/
theorem LZ_bound_pos : LZ_bound_cm2 > 0 := by unfold LZ_bound_cm2; norm_num

/-- DARWIN projected sensitivity: σ_{SI} ~ 10⁻⁴⁹ cm².

    **Citation:** DARWIN Collaboration, JCAP 11, 017 (2016), arXiv:1606.07001 -/
noncomputable def DARWIN_sensitivity_cm2 : ℝ := 1e-49

/-- DARWIN sensitivity > 0 -/
theorem DARWIN_sensitivity_pos : DARWIN_sensitivity_cm2 > 0 := by
  unfold DARWIN_sensitivity_cm2; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 16: COSMOLOGICAL DENSITY FRACTIONS
    ═══════════════════════════════════════════════════════════════════════════

    Density fractions for matter, dark energy, radiation.
    Reference: docs/proofs/Phase5/Proposition-5.1.2a-Matter-Density-From-Geometry.md
-/

/-- Observed baryon density fraction: Ω_b = 0.0493 (Planck 2018).

    **Physical meaning:**
    Fraction of critical density in baryonic matter.

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def Omega_b_observed : ℝ := 0.0493

/-- Ω_b > 0 -/
theorem Omega_b_observed_pos : Omega_b_observed > 0 := by
  unfold Omega_b_observed; norm_num

/-- Ω_b < 1 -/
theorem Omega_b_observed_lt_one : Omega_b_observed < 1 := by
  unfold Omega_b_observed; norm_num

/-- Observed dark matter density fraction: Ω_DM = 0.266 (Planck 2018).

    **Physical meaning:**
    Fraction of critical density in dark matter.

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def Omega_DM_observed : ℝ := 0.266

/-- Ω_DM > 0 -/
theorem Omega_DM_observed_pos : Omega_DM_observed > 0 := by
  unfold Omega_DM_observed; norm_num

/-- Ω_DM < 1 -/
theorem Omega_DM_observed_lt_one : Omega_DM_observed < 1 := by
  unfold Omega_DM_observed; norm_num

/-- Observed total matter density fraction: Ω_m = 0.315 (Planck 2018).

    **Physical meaning:**
    Fraction of critical density in all matter (baryonic + dark).

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def Omega_m_observed : ℝ := 0.315

/-- Ω_m > 0 -/
theorem Omega_m_observed_pos : Omega_m_observed > 0 := by
  unfold Omega_m_observed; norm_num

/-- Ω_m < 1 -/
theorem Omega_m_observed_lt_one : Omega_m_observed < 1 := by
  unfold Omega_m_observed; norm_num

/-- Observed dark energy density fraction: Ω_Λ = 0.685 (Planck 2018).

    **Physical meaning:**
    Fraction of critical density in dark energy (cosmological constant).

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def Omega_Lambda_observed : ℝ := 0.685

/-- Ω_Λ > 0 -/
theorem Omega_Lambda_observed_pos : Omega_Lambda_observed > 0 := by
  unfold Omega_Lambda_observed; norm_num

/-- Ω_Λ < 1 -/
theorem Omega_Lambda_observed_lt_one : Omega_Lambda_observed < 1 := by
  unfold Omega_Lambda_observed; norm_num

/-- Radiation density fraction: Ω_r ≈ 9.4 × 10⁻⁵.

    **Physical meaning:**
    Negligible compared to matter and dark energy at present epoch.

    **Citation:** Derived from T_CMB = 2.7255 K -/
noncomputable def Omega_r : ℝ := 9.4e-5

/-- Ω_r > 0 -/
theorem Omega_r_pos : Omega_r > 0 := by unfold Omega_r; norm_num

/-- Ω_r is small (negligible contribution) -/
theorem Omega_r_small : Omega_r < 0.001 := by unfold Omega_r; norm_num

/-- W-soliton mass: M_W = 1700 GeV (CG prediction).

    **Physical meaning:**
    Mass of W-condensate dark matter candidate.

    **Citation:** Prediction 8.3.1 §12 -/
noncomputable def M_W_soliton_GeV : ℝ := 1700

/-- M_W > 0 -/
theorem M_W_soliton_pos : M_W_soliton_GeV > 0 := by
  unfold M_W_soliton_GeV; norm_num

/-- W-to-baryon geometric suppression factor: κ_W^geom = 4.71 × 10⁻⁴.

    **Physical meaning:**
    Ratio of W-asymmetry to baryon asymmetry from stella geometry.
    κ_W^geom = f_singlet × f_VEV × f_solid × f_overlap × |f_chiral|

    **Geometric factors:**
    - f_singlet = 1/N_c = 1/3 (singlet vs triplet)
    - f_VEV = (v_W/v_H)² = 1/3
    - f_solid = √(Ω_W/4π) = 1/2 (domain solid angle)
    - f_overlap = e^{-d/R} ≈ 4.89 × 10⁻³ (vertex separation)
    - |f_chiral| = √3 (chirality transfer)

    **Citation:** Prediction 8.3.1 §6.4.6 -/
noncomputable def kappa_W_geom : ℝ := 4.71e-4

/-- κ_W^geom > 0 -/
theorem kappa_W_geom_pos : kappa_W_geom > 0 := by
  unfold kappa_W_geom; norm_num

/-- κ_W^geom < 1 (suppression factor) -/
theorem kappa_W_geom_lt_one : kappa_W_geom < 1 := by
  unfold kappa_W_geom; norm_num

/-- CG predicted baryon density fraction: Ω_b = 0.049 ± 0.020.

    **Physical meaning:**
    Derived from η_B via standard cosmology conversion.

    **Citation:** Theorem 4.2.1 §18 -/
noncomputable def Omega_b_predicted : ℝ := 0.049

/-- Ω_b predicted > 0 -/
theorem Omega_b_predicted_pos : Omega_b_predicted > 0 := by
  unfold Omega_b_predicted; norm_num

/-- CG predicted dark matter density fraction: Ω_DM = 0.30 ± 0.15.

    **Physical meaning:**
    Derived from W-asymmetry via ADM mechanism.

    **Citation:** Proposition 5.1.2a §4 -/
noncomputable def Omega_DM_predicted : ℝ := 0.30

/-- Ω_DM predicted > 0 -/
theorem Omega_DM_predicted_pos : Omega_DM_predicted > 0 := by
  unfold Omega_DM_predicted; norm_num

/-- CG predicted total matter density: Ω_m = Ω_b + Ω_DM ≈ 0.349.

    **Physical meaning:**
    Sum of baryonic and dark matter fractions.
    Defined as exact sum for internal consistency.
    Display approximation: 0.34 ± 0.15

    **Citation:** Proposition 5.1.2a §5 -/
noncomputable def Omega_m_predicted : ℝ := Omega_b_predicted + Omega_DM_predicted

/-- Ω_m predicted > 0 -/
theorem Omega_m_predicted_pos : Omega_m_predicted > 0 := by
  unfold Omega_m_predicted
  linarith [Omega_b_predicted_pos, Omega_DM_predicted_pos]

/-- Ω_m = Ω_b + Ω_DM by definition -/
theorem Omega_m_is_sum : Omega_m_predicted = Omega_b_predicted + Omega_DM_predicted := rfl

/-- CG predicted dark energy density: Ω_Λ = 1 - Ω_m - Ω_r ≈ 0.651.

    **Physical meaning:**
    Derived from flatness condition: Ω_Λ = 1 - Ω_m - Ω_r.
    Defined as exact difference for internal consistency.
    Display approximation: 0.66 ± 0.15

    **Citation:** Proposition 5.1.2a §6 -/
noncomputable def Omega_Lambda_predicted : ℝ := 1 - Omega_m_predicted - Omega_r

/-- Ω_Λ predicted > 0 -/
theorem Omega_Lambda_predicted_pos : Omega_Lambda_predicted > 0 := by
  unfold Omega_Lambda_predicted Omega_m_predicted Omega_b_predicted Omega_DM_predicted Omega_r
  norm_num

/-- Ω_Λ = 1 - Ω_m - Ω_r by definition (flatness condition) -/
theorem Omega_Lambda_from_flatness : Omega_Lambda_predicted = 1 - Omega_m_predicted - Omega_r := rfl

/-- Flatness: Ω_m + Ω_Λ + Ω_r = 1 (exact by construction) -/
theorem flatness_exact : Omega_m_predicted + Omega_Lambda_predicted + Omega_r = 1 := by
  unfold Omega_Lambda_predicted
  ring

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 17: PRECISION COSMOLOGICAL DENSITY CONSTANTS (PROPOSITION 5.1.2b)
    ═══════════════════════════════════════════════════════════════════════════

    Updated constants with reduced theoretical uncertainties from
    Proposition 5.1.2b: Precision Cosmological Density Predictions.

    Key improvements:
    - η_B uncertainty reduced from factor ~5 to factor ~1.6 (±40%)
    - f_overlap uses power-law scaling (reduced sensitivity)
    - λ_W derived from first principles (no longer unknown)
    - v_W derived self-consistently from soliton + potential

    Reference: docs/proofs/Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md
-/

/-- Updated baryon asymmetry: η_B = 6.1 × 10⁻¹⁰ (Prop 5.1.2b §2.4).

    **Physical meaning:**
    Baryon-to-photon ratio derived from CG sphaleron dynamics.
    Improved uncertainty from factor ~5 to factor ~1.6.

    **Citation:** Proposition 5.1.2b §2.4 -/
noncomputable def eta_B_precision : ℝ := 6.1e-10

/-- η_B precision = η_B (same central value) -/
theorem eta_B_precision_eq : eta_B_precision = eta_B := rfl

/-- Sphaleron efficiency factor: κ_sph = 3.5 × 10⁻² (Prop 5.1.2b §2.3).

    **Physical meaning:**
    Fraction of CP asymmetry that survives sphaleron processing.
    κ_sph = f_transport × f_wall × f_wash

    **Citation:** Proposition 5.1.2b §2.3 -/
noncomputable def kappa_sph : ℝ := 3.5e-2

/-- κ_sph > 0 -/
theorem kappa_sph_pos : kappa_sph > 0 := by unfold kappa_sph; norm_num

/-- κ_sph < 1 (efficiency factor) -/
theorem kappa_sph_lt_one : kappa_sph < 1 := by unfold kappa_sph; norm_num

/-- Updated overlap factor: f_overlap = 7.1 × 10⁻³ (Prop 5.1.2b §3.4).

    **Physical meaning:**
    Geometric overlap factor using power-law (not exponential) scaling.
    Uncertainty reduced from ±50% to ±15%.

    **Key insight:**
    Power-law falloff |ψ|² ~ r⁻⁴ gives reduced sensitivity:
    10% change in d/r₀ → 15% change in f_overlap (vs 50% for exponential)

    **Citation:** Proposition 5.1.2b §3.4 -/
noncomputable def f_overlap_precision : ℝ := 7.1e-3

/-- f_overlap > 0 -/
theorem f_overlap_precision_pos : f_overlap_precision > 0 := by
  unfold f_overlap_precision; norm_num

/-- f_overlap < 1 (suppression factor) -/
theorem f_overlap_precision_lt_one : f_overlap_precision < 1 := by
  unfold f_overlap_precision; norm_num

/-- W-sector quartic coupling: λ_W = 0.101 (Prop 5.1.2b §4.5).

    **Physical meaning:**
    Derived from self-consistency between soliton mass formula
    and potential minimization. Key breakthrough - previously unknown.

    **Derivation:**
    λ_W = (μ_W² - λ_HW v_H²) / (2 v_W²)
        = (5230 - 2181) / 30258 = 0.101

    **Citation:** Proposition 5.1.2b §4.5 -/
noncomputable def lambda_W : ℝ := 0.101

/-- λ_W > 0 -/
theorem lambda_W_pos : lambda_W > 0 := by unfold lambda_W; norm_num

-- NOTE: lambda_H, lambda_H_pos relocated to Electroweak.lean

/-- Ratio λ_W/λ_H = 0.78 (Prop 5.1.2b §4.5).

    **Physical meaning:**
    W-sector coupling is ~78% of Higgs coupling.

    **Citation:** Proposition 5.1.2b §4.5.3 -/
noncomputable def lambda_ratio : ℝ := lambda_W / lambda_H

/-- λ_W/λ_H ≈ 0.78 -/
theorem lambda_ratio_approx : lambda_ratio > 0.77 ∧ lambda_ratio < 0.79 := by
  unfold lambda_ratio lambda_W lambda_H
  constructor <;> norm_num

/-- Higgs portal coupling: λ_HW = 0.036 (Prop 5.1.2b §4.2.2).

    **Physical meaning:**
    Portal coupling from domain boundary overlap.

    **Citation:** Prediction 8.3.1 §13, Proposition 5.1.2b §4.2.2 -/
noncomputable def lambda_HW : ℝ := 0.036

/-- λ_HW > 0 -/
theorem lambda_HW_pos : lambda_HW > 0 := by unfold lambda_HW; norm_num

/-- Updated W-sector VEV: v_W = 123 GeV (Prop 5.1.2b §4.6).

    **Physical meaning:**
    Self-consistent solution from soliton + potential minimization.
    Intermediate between geometric estimate (142 GeV) and
    λ_W = λ_H assumption (108 GeV).

    **Citation:** Proposition 5.1.2b §4.6 -/
noncomputable def v_W_precision_GeV : ℝ := 123

/-- v_W > 0 -/
theorem v_W_precision_pos : v_W_precision_GeV > 0 := by
  unfold v_W_precision_GeV; norm_num

/-- v_W/v_H ratio = 0.50 (Prop 5.1.2b §4.6).

    **Physical meaning:**
    Uncertainty reduced from ±20% to ±12%.

    **Citation:** Proposition 5.1.2b §4.6 -/
noncomputable def v_W_v_H_ratio : ℝ := v_W_precision_GeV / v_H_GeV

/-- v_W/v_H ≈ 0.50 (approximation, exact value depends on v_H precision) -/
theorem v_W_v_H_ratio_approx : 0.49 < v_W_v_H_ratio ∧ v_W_v_H_ratio < 0.51 := by
  unfold v_W_v_H_ratio v_W_precision_GeV v_H_GeV
  constructor <;> norm_num

/-- Skyrme parameter for W-sector: e_W = 4.5 (Prop 5.1.2b §5.2).

    **Physical meaning:**
    Derived from stella geometry curvature.
    Consistent with QCD value e_π ≈ 4.25-5.45.

    **Citation:** Proposition 5.1.2b §5.2 -/
noncomputable def skyrme_e_W : ℝ := 4.5

/-- e_W > 0 -/
theorem skyrme_e_W_pos : skyrme_e_W > 0 := by unfold skyrme_e_W; norm_num

/-- Updated W-soliton mass: M_W = 1620 GeV (Prop 5.1.2b §5.3).

    **Physical meaning:**
    M_W = 6π² v_W / e_W with improved values.
    Uncertainty reduced from ±20% to ±10%.

    **Citation:** Proposition 5.1.2b §5.3 -/
noncomputable def M_W_precision_GeV : ℝ := 1620

/-- M_W precision > 0 -/
theorem M_W_precision_pos : M_W_precision_GeV > 0 := by
  unfold M_W_precision_GeV; norm_num

/-- Updated geometric suppression factor: κ_W^geom = 5.1 × 10⁻⁴ (Prop 5.1.2b §6.1).

    **Physical meaning:**
    κ_W^geom = f_singlet × f_VEV × f_solid × f_overlap × |f_chiral|
    Updated with precision f_overlap and v_W values.

    **Citation:** Proposition 5.1.2b §6.1 -/
noncomputable def kappa_W_geom_precision : ℝ := 5.1e-4

/-- κ_W^geom precision > 0 -/
theorem kappa_W_geom_precision_pos : kappa_W_geom_precision > 0 := by
  unfold kappa_W_geom_precision; norm_num

/-- κ_W^geom precision < 1 -/
theorem kappa_W_geom_precision_lt_one : kappa_W_geom_precision < 1 := by
  unfold kappa_W_geom_precision; norm_num

/-! ─────────────────────────────────────────────────────────────────────────────
    SECTION 17a: FIVE GEOMETRIC SUPPRESSION FACTORS (PROPOSITION 4.3.3)
    ─────────────────────────────────────────────────────────────────────────────

    The five individual geometric factors whose product gives κ_W^geom.
    These are the first-principles derivation of why Ω_DM/Ω_b ≈ 5.

    Reference: docs/proofs/Phase4/Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md §5
-/

/-- Factor 1: Chemical equilibrium transfer fraction: f_singlet^eff = 1/N_c = 1/3.

    **Physical meaning:**
    The W vertex is a color singlet, so its anomaly coupling vanishes.
    Asymmetry is transferred indirectly via Higgs portal chemical equilibrium.
    Since η_B ∝ 3μ_c and ε_W ∝ μ_W = μ_c, the transfer fraction is 1/3.

    **Citation:** Proposition 4.3.3 §5.1 -/
noncomputable def f_singlet_eff : ℝ := 1 / 3

/-- f_singlet_eff > 0 -/
theorem f_singlet_eff_pos : f_singlet_eff > 0 := by unfold f_singlet_eff; norm_num

/-- f_singlet_eff < 1 -/
theorem f_singlet_eff_lt_one : f_singlet_eff < 1 := by unfold f_singlet_eff; norm_num

/-- f_singlet_eff = 1/N_c (exact) -/
theorem f_singlet_from_Nc : f_singlet_eff = 1 / (N_c : ℝ) := by
  unfold f_singlet_eff N_c; norm_num

/-- Factor 2: VEV ratio squared: f_VEV = (v_W/v_H)² ≈ 0.25.

    **Physical meaning:**
    Asymmetry production rate scales with VEV². v_W = 123 GeV, v_H = 246.22 GeV.

    **Citation:** Proposition 4.3.3 §5.2, Proposition 5.1.2b §4.5 -/
noncomputable def f_VEV_4_3_3 : ℝ := (v_W_precision_GeV / v_H_GeV) ^ 2

/-- f_VEV > 0 -/
theorem f_VEV_4_3_3_pos : f_VEV_4_3_3 > 0 := by
  unfold f_VEV_4_3_3
  apply sq_pos_of_pos
  exact div_pos v_W_precision_pos v_H_GeV_pos

/-- f_VEV < 1 -/
theorem f_VEV_4_3_3_lt_one : f_VEV_4_3_3 < 1 := by
  unfold f_VEV_4_3_3 v_W_precision_GeV v_H_GeV
  norm_num

/-- f_VEV ≈ 0.25 (within 1%) -/
theorem f_VEV_4_3_3_approx : 0.24 < f_VEV_4_3_3 ∧ f_VEV_4_3_3 < 0.26 := by
  unfold f_VEV_4_3_3 v_W_precision_GeV v_H_GeV
  constructor <;> norm_num

/-- Factor 3: Domain solid angle (RMS amplitude projection): f_solid = 1/2.

    **Physical meaning:**
    The W domain covers solid angle Ω_W = π steradians (25% of sphere).
    Since asymmetry transfer is linear in chirality gradient amplitude (not intensity),
    f_solid = √(Ω_W/4π) = √(1/4) = 1/2.

    **Citation:** Proposition 4.3.3 §5.3 -/
noncomputable def f_solid : ℝ := 1 / 2

/-- f_solid > 0 -/
theorem f_solid_pos : f_solid > 0 := by unfold f_solid; norm_num

/-- f_solid < 1 -/
theorem f_solid_lt_one : f_solid < 1 := by unfold f_solid; norm_num

/-- Factor 5: Chirality transfer efficiency: |f_chiral| = √3.

    **Physical meaning:**
    Three color pairs (R–G, G–B, B–R) each contribute chirality gradient
    proportional to sin(2π/3) = √3/2. The three gradient contributions are
    mutually orthogonal (tetrahedral edge directions), so they add in quadrature:
    |G_total| = √3 × |G_single|. The factor is √N_c.

    **Citation:** Proposition 4.3.3 §5.5 -/
noncomputable def f_chiral_abs : ℝ := Real.sqrt 3

/-- |f_chiral| > 0 -/
theorem f_chiral_abs_pos : f_chiral_abs > 0 := by
  unfold f_chiral_abs
  exact Real.sqrt_pos_of_pos (by norm_num : (3 : ℝ) > 0)

/-- |f_chiral| > 1 (enhancement factor, not suppression) -/
theorem f_chiral_abs_gt_one : f_chiral_abs > 1 := by
  unfold f_chiral_abs
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- |f_chiral|² = N_c = 3 -/
theorem f_chiral_abs_sq : f_chiral_abs ^ 2 = 3 := by
  unfold f_chiral_abs
  exact Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- W-sector fine-structure constant: α_W^sector = e_W²/(4π) ≈ 1.61.

    **Physical meaning:**
    The W-sector SU(2)_W gauge coupling strength. This is the SECTOR coupling
    (strongly coupled, α ≫ 1), NOT the SM weak coupling α_W ≈ 0.034.
    Controls W-soliton self-interactions and symmetric component depletion.

    **Citation:** Proposition 4.3.3 §4.2, Theorem 4.3.2 -/
noncomputable def alpha_W_sector : ℝ := skyrme_e_W ^ 2 / (4 * Real.pi)

/-- α_W^sector > 0 -/
theorem alpha_W_sector_pos : alpha_W_sector > 0 := by
  unfold alpha_W_sector
  exact div_pos (sq_pos_of_pos skyrme_e_W_pos) (mul_pos (by norm_num) Real.pi_pos)

/-- α_W^sector > 1 (strongly coupled) -/
theorem alpha_W_sector_gt_one : alpha_W_sector > 1 := by
  unfold alpha_W_sector skyrme_e_W
  show 1 < 4.5 ^ 2 / (4 * Real.pi)
  rw [one_lt_div (mul_pos (by norm_num : (4 : ℝ) > 0) Real.pi_pos)]
  nlinarith [Real.pi_lt_four]

/-- Precise Planck baryon density: Ω_b h² = 0.0224 (Planck 2018).

    **Physical meaning:**
    More precise value than 0.022, used in Prop 4.3.3 ADM formula.

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def Omega_b_h2_Planck : ℝ := 0.0224

/-- Ω_b h² Planck > 0 -/
theorem Omega_b_h2_Planck_pos : Omega_b_h2_Planck > 0 := by
  unfold Omega_b_h2_Planck; norm_num

/-- Precise Planck DM density: Ω_DM h² = 0.1200 (Planck 2018).

    **Physical meaning:**
    The Planck 2018 observed dark matter density parameter.

    **Citation:** Planck 2018, Ω_DM h² = 0.1200 ± 0.0012 -/
noncomputable def Omega_DM_h2_Planck : ℝ := 0.1200

/-- Ω_DM h² Planck > 0 -/
theorem Omega_DM_h2_Planck_pos : Omega_DM_h2_Planck > 0 := by
  unfold Omega_DM_h2_Planck; norm_num

/-- DM/baryon ratio from Planck: Ω_DM/Ω_b = 0.1200/0.0224 ≈ 5.36 -/
noncomputable def DM_baryon_ratio_Planck : ℝ := Omega_DM_h2_Planck / Omega_b_h2_Planck

/-- Precision Ω_b = 0.049 ± 0.017 (±35%) (Prop 5.1.2b §6.2).

    **Citation:** Proposition 5.1.2b §6.2 -/
noncomputable def Omega_b_precision : ℝ := 0.049

/-- Ω_b precision > 0 -/
theorem Omega_b_precision_pos : Omega_b_precision > 0 := by
  unfold Omega_b_precision; norm_num

/-- Precision Ω_DM = 0.27 ± 0.11 (±41%) (Prop 5.1.2b §6.3).

    **Citation:** Proposition 5.1.2b §6.3 -/
noncomputable def Omega_DM_precision : ℝ := 0.27

/-- Ω_DM precision > 0 -/
theorem Omega_DM_precision_pos : Omega_DM_precision > 0 := by
  unfold Omega_DM_precision; norm_num

/-- Precision Ω_m = 0.32 ± 0.12 (±38%) (Prop 5.1.2b §6.4).

    **Citation:** Proposition 5.1.2b §6.4 -/
noncomputable def Omega_m_precision : ℝ := Omega_b_precision + Omega_DM_precision

/-- Ω_m precision > 0 -/
theorem Omega_m_precision_pos : Omega_m_precision > 0 := by
  unfold Omega_m_precision
  linarith [Omega_b_precision_pos, Omega_DM_precision_pos]

/-- Ω_m precision is sum -/
theorem Omega_m_precision_is_sum :
    Omega_m_precision = Omega_b_precision + Omega_DM_precision := rfl

/-- Precision Ω_Λ = 0.68 ± 0.14 (±20%) (Prop 5.1.2b §6.4).

    **Citation:** Proposition 5.1.2b §6.4 -/
noncomputable def Omega_Lambda_precision : ℝ := 1 - Omega_m_precision - Omega_r

/-- Ω_Λ precision > 0 -/
theorem Omega_Lambda_precision_pos : Omega_Lambda_precision > 0 := by
  unfold Omega_Lambda_precision Omega_m_precision Omega_b_precision Omega_DM_precision Omega_r
  norm_num

/-- Precision flatness: Ω_m + Ω_Λ + Ω_r = 1 (exact by construction) -/
theorem flatness_precision_exact :
    Omega_m_precision + Omega_Lambda_precision + Omega_r = 1 := by
  unfold Omega_Lambda_precision
  ring

/-- Overlap integral coefficient: I = 16r₀³/(9d⁴) (Prop 5.1.2b §3.2.3).

    **Physical meaning:**
    The radial integral evaluates to π/(4r₀), giving the final coefficient.

    **Citation:** Proposition 5.1.2b §3.2.3 -/
noncomputable def overlap_integral_coefficient : ℝ := 16 / 9

/-- Overlap coefficient > 0 -/
theorem overlap_integral_coefficient_pos : overlap_integral_coefficient > 0 := by
  unfold overlap_integral_coefficient; norm_num

/-- W-sector mass parameter squared: μ_W² = μ_H²/3 = 5230 GeV² (Prop 5.1.2b §4.5.2).

    **Physical meaning:**
    Geometric constraint from stella vertex counting.

    **Citation:** Proposition 5.1.2b §4.5.2 -/
noncomputable def mu_W_squared_GeV2 : ℝ := 5230

/-- μ_W² > 0 -/
theorem mu_W_squared_pos : mu_W_squared_GeV2 > 0 := by
  unfold mu_W_squared_GeV2; norm_num

/-- Electroweak sphaleron energy: E_sph = 9.1 TeV (Prop 5.1.2b §2.2.3).

    **Physical meaning:**
    Refined from earlier ~10 TeV estimates.

    **Citation:** Matchev & Verner (2025), arXiv:2505.05607 -/
noncomputable def E_sph_TeV : ℝ := 9.1

/-- E_sph > 0 -/
theorem E_sph_pos : E_sph_TeV > 0 := by unfold E_sph_TeV; norm_num

/-- Freeze-out temperature: T_* = 132 GeV (Prop 5.1.2b §2.2.2).

    **Physical meaning:**
    Temperature at which sphalerons freeze out.

    **Citation:** D'Onofrio et al. (2014) -/
noncomputable def T_freezeout_GeV : ℝ := 132

/-- T_* > 0 -/
theorem T_freezeout_pos : T_freezeout_GeV > 0 := by
  unfold T_freezeout_GeV; norm_num

/-- Critical temperature: T_c = 159.5 GeV (Prop 5.1.2b §2.2.2).

    **Physical meaning:**
    Electroweak phase transition temperature.

    **Citation:** D'Onofrio et al. (2014) -/
noncomputable def T_critical_GeV : ℝ := 159.5

/-- T_c > 0 -/
theorem T_critical_pos : T_critical_GeV > 0 := by
  unfold T_critical_GeV; norm_num

/-- Jarlskog invariant: J = 3.00 × 10⁻⁵ (Prop 5.1.2b §2.1).

    **Physical meaning:**
    CP violation parameter from CKM matrix.

    **Citation:** PDG 2024 -/
noncomputable def jarlskog_invariant : ℝ := 3.00e-5

/-- J > 0 -/
theorem jarlskog_pos : jarlskog_invariant > 0 := by
  unfold jarlskog_invariant; norm_num

/-- Effective CP violation parameter: ε_CP = 1.5 × 10⁻⁵ (Prop 5.1.2b §2.1).

    **Physical meaning:**
    ε_CP = J × (m_t² - m_c²)/v_H² × f_thermal

    **Citation:** Proposition 5.1.2b §2.1 -/
noncomputable def epsilon_CP : ℝ := 1.5e-5

/-- ε_CP > 0 -/
theorem epsilon_CP_pos : epsilon_CP > 0 := by unfold epsilon_CP; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 15: ANTHROPIC BOUNDS ON R_STELLA
    ═══════════════════════════════════════════════════════════════════════════

    Proposition 0.0.36 derives the range of R_stella values compatible with
    observer existence (complex observers capable of carbon-based chemistry
    sustained by stellar nucleosynthesis).

    Reference: docs/proofs/foundations/Proposition-0.0.36-Anthropic-Bounds-On-R-Stella.md
-/

/-- Lower bound on R_stella from anthropic constraints: R_min ≈ 0.42 fm.

    **Physical origin:**
    Primarily from di-proton stability and Hoyle state (¹²C resonance).
    If R_stella < R_min, the strong force becomes too strong, potentially
    binding the di-proton and/or disrupting the Hoyle state for carbon production.

    **Literature:**
    - Barrow & Tipler (1986): Di-proton binds at +4% QCD increase
    - MacDonald & Mullan (2009): H survival threshold at +50%
    - Epelbaum et al. (2013): Hoyle state sensitivity ±4%

    **Citation:** Proposition 0.0.36 §4, §5 -/
noncomputable def R_stella_min_fm : ℝ := 0.42

/-- R_stella_min > 0 -/
theorem R_stella_min_pos : R_stella_min_fm > 0 := by
  unfold R_stella_min_fm; norm_num

/-- Upper bound on R_stella from anthropic constraints: R_max ≈ 0.48 fm.

    **Physical origin:**
    Primarily from deuteron binding. The deuteron (²H) is essential for
    stellar nucleosynthesis (p + n → d + γ). If R_stella > R_max, the
    strong force becomes too weak and the deuteron unbinds.

    **Literature:**
    - Barnes & Lewis (2017): "The most definitive boundary... is between
      a bound and unbound deuteron."
    - Damour & Donoghue (2008): Deuteron unbinds at -6% QCD decrease

    **Citation:** Proposition 0.0.36 §3 -/
noncomputable def R_stella_max_fm : ℝ := 0.48

/-- R_stella_max > 0 -/
theorem R_stella_max_pos : R_stella_max_fm > 0 := by
  unfold R_stella_max_fm; norm_num

/-- The anthropic window width: ΔR ≈ 0.06 fm.

    **Citation:** Proposition 0.0.36 §6.2 -/
noncomputable def anthropic_window_width_fm : ℝ := R_stella_max_fm - R_stella_min_fm

/-- Anthropic window width is positive -/
theorem anthropic_window_width_pos : anthropic_window_width_fm > 0 := by
  unfold anthropic_window_width_fm R_stella_max_fm R_stella_min_fm
  norm_num

/-- Anthropic window width ≈ 0.06 fm -/
theorem anthropic_window_width_value : anthropic_window_width_fm = 0.06 := by
  unfold anthropic_window_width_fm R_stella_max_fm R_stella_min_fm
  norm_num

/-- Lower bound on √σ from anthropic constraints: √σ_min ≈ 411 MeV.

    **Derivation:** √σ_min = ℏc/R_max = 197.327/0.48 ≈ 411 MeV

    **Citation:** Proposition 0.0.36 §6.1 -/
noncomputable def sqrt_sigma_min_MeV : ℝ := hbar_c_MeV_fm / R_stella_max_fm

/-- √σ_min > 0 -/
theorem sqrt_sigma_min_pos : sqrt_sigma_min_MeV > 0 := by
  unfold sqrt_sigma_min_MeV
  exact div_pos hbar_c_pos R_stella_max_pos

/-- √σ_min ≈ 411 MeV (numerical check) -/
theorem sqrt_sigma_min_approx : sqrt_sigma_min_MeV > 410 ∧ sqrt_sigma_min_MeV < 412 := by
  unfold sqrt_sigma_min_MeV hbar_c_MeV_fm R_stella_max_fm
  constructor <;> norm_num

/-- Upper bound on √σ from anthropic constraints: √σ_max ≈ 470 MeV.

    **Derivation:** √σ_max = ℏc/R_min = 197.327/0.42 ≈ 470 MeV

    **Citation:** Proposition 0.0.36 §6.1 -/
noncomputable def sqrt_sigma_max_MeV : ℝ := hbar_c_MeV_fm / R_stella_min_fm

/-- √σ_max > 0 -/
theorem sqrt_sigma_max_pos : sqrt_sigma_max_MeV > 0 := by
  unfold sqrt_sigma_max_MeV
  exact div_pos hbar_c_pos R_stella_min_pos

/-- √σ_max ≈ 470 MeV (numerical check) -/
theorem sqrt_sigma_max_approx : sqrt_sigma_max_MeV > 469 ∧ sqrt_sigma_max_MeV < 471 := by
  unfold sqrt_sigma_max_MeV hbar_c_MeV_fm R_stella_min_fm
  constructor <;> norm_num

/-- The string tension anthropic window width: Δ√σ ≈ 59 MeV.

    **Citation:** Proposition 0.0.36 §6.1 -/
noncomputable def sqrt_sigma_window_MeV : ℝ := sqrt_sigma_max_MeV - sqrt_sigma_min_MeV

/-- √σ window is positive -/
theorem sqrt_sigma_window_pos : sqrt_sigma_window_MeV > 0 := by
  unfold sqrt_sigma_window_MeV sqrt_sigma_max_MeV sqrt_sigma_min_MeV
    hbar_c_MeV_fm R_stella_min_fm R_stella_max_fm
  norm_num

/-- Fractional width of anthropic window: ΔR/R_center ≈ 13%.

    **Citation:** Proposition 0.0.36 §6.2 -/
noncomputable def anthropic_fractional_width : ℝ :=
  anthropic_window_width_fm / ((R_stella_min_fm + R_stella_max_fm) / 2)

/-- Fractional width ≈ 13% -/
theorem anthropic_fractional_width_approx :
    anthropic_fractional_width > 0.13 ∧ anthropic_fractional_width < 0.14 := by
  unfold anthropic_fractional_width anthropic_window_width_fm
    R_stella_min_fm R_stella_max_fm
  constructor <;> norm_num

/-- Position of observed R_stella in the anthropic window (as fraction from R_min).

    Position = (R_obs - R_min) / (R_max - R_min) ≈ 47.4%

    **Interpretation:**
    The observed value sits approximately at the CENTER of the anthropic window,
    neither at an edge nor requiring explanation for its particular position.
    This is NOT fine-tuning.

    **Citation:** Proposition 0.0.36 §6.3, Corollary 0.0.36.2 -/
noncomputable def observed_position_in_window : ℝ :=
  (R_stella_fm - R_stella_min_fm) / anthropic_window_width_fm

/-- Position ≈ 47% (near center) -/
theorem observed_position_approx :
    observed_position_in_window > 0.47 ∧ observed_position_in_window < 0.48 := by
  unfold observed_position_in_window anthropic_window_width_fm
    R_stella_fm R_stella_min_fm R_stella_max_fm
  constructor <;> norm_num

/-- The observed R_stella lies within the anthropic window.

    **Citation:** Proposition 0.0.36 §6.3 -/
theorem R_stella_in_anthropic_window :
    R_stella_min_fm < R_stella_fm ∧ R_stella_fm < R_stella_max_fm := by
  unfold R_stella_min_fm R_stella_fm R_stella_max_fm
  constructor <;> norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 28: STRUCTURE FORMATION OBSERVATIONAL BOUNDS (PROPOSITION 4.3.4)
    ═══════════════════════════════════════════════════════════════════════════

    Observational bounds on dark matter properties from structure formation,
    CMB, and spectral distortion measurements. Used primarily in
    Proposition 4.3.4 (W-Soliton Structure Formation Compatibility).

    Reference: docs/proofs/Phase4/Proposition-4.3.4-W-Soliton-Structure-Formation.md
-/

/-- Temperature at matter-radiation equality: T_eq ≈ 0.75 eV.

    **Physical meaning:**
    The temperature at which the energy density of matter equals
    that of radiation. Sets the scale for CDM classification.

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def T_eq_eV : ℝ := 0.75

/-- T_eq > 0 -/
theorem T_eq_eV_pos : T_eq_eV > 0 := by unfold T_eq_eV; norm_num

/-- Redshift at matter-radiation equality: z_eq ≈ 3400.

    **Citation:** Planck 2018 -/
noncomputable def z_eq : ℝ := 3400

/-- z_eq > 0 -/
theorem z_eq_pos : z_eq > 0 := by unfold z_eq; norm_num

/-- Bullet Cluster self-interaction bound (classic): σ/m < 1 cm²/g.

    **Physical meaning:**
    The original order-of-magnitude constraint from the merging galaxy
    cluster 1E 0657-56 (the "Bullet Cluster").

    **Citation:** Markevitch et al. (2004), ApJ 606, 819. arXiv:astro-ph/0309303 -/
noncomputable def bullet_cluster_sigma_m_bound : ℝ := 1.0

/-- Bullet Cluster bound > 0 -/
theorem bullet_cluster_sigma_m_bound_pos : bullet_cluster_sigma_m_bound > 0 := by
  unfold bullet_cluster_sigma_m_bound; norm_num

/-- Planck CMB annihilation bound: f_eff ⟨σv⟩ / M_DM < 3.2 × 10⁻²⁸ cm³/s/GeV.

    **Physical meaning:**
    Upper limit on energy injection from DM annihilation at late times,
    constrained by CMB anisotropy measurements.

    **Citation:** Planck 2018, arXiv:1807.06209 -/
noncomputable def planck_cmb_annihilation_bound : ℝ := 3.2e-28

/-- Planck CMB bound > 0 -/
theorem planck_cmb_annihilation_bound_pos : planck_cmb_annihilation_bound > 0 := by
  unfold planck_cmb_annihilation_bound; norm_num

/-- FIRAS μ-distortion limit: |μ| < 9 × 10⁻⁵.

    **Citation:** Fixsen et al. (1996), ApJ 473, 576. arXiv:astro-ph/9605054 -/
noncomputable def FIRAS_mu_limit : ℝ := 9e-5

/-- FIRAS μ limit > 0 -/
theorem FIRAS_mu_limit_pos : FIRAS_mu_limit > 0 := by unfold FIRAS_mu_limit; norm_num

/-- FIRAS y-distortion limit: |y| < 1.5 × 10⁻⁵.

    **Citation:** Fixsen et al. (1996) -/
noncomputable def FIRAS_y_limit : ℝ := 1.5e-5

/-- FIRAS y limit > 0 -/
theorem FIRAS_y_limit_pos : FIRAS_y_limit > 0 := by unfold FIRAS_y_limit; norm_num

/-- Lyman-α warm DM mass limit: m_WDM > 5.3 keV.

    **Physical meaning:**
    Lower bound on warm dark matter particle mass from Lyman-α forest
    power spectrum measurements at small scales.

    **Citation:** Irsic et al. (2017), Phys. Rev. D 96, 023522. arXiv:1702.01764 -/
noncomputable def WDM_mass_limit_keV : ℝ := 5.3

/-- WDM mass limit > 0 -/
theorem WDM_mass_limit_keV_pos : WDM_mass_limit_keV > 0 := by
  unfold WDM_mass_limit_keV; norm_num

/-- Planck scalar spectral index: n_s = 0.9649 ± 0.0042.

    **Citation:** Planck 2018 -/
noncomputable def n_s_Planck : ℝ := 0.9649

/-- n_s > 0 -/
theorem n_s_Planck_pos : n_s_Planck > 0 := by unfold n_s_Planck; norm_num

/-- Planck optical depth: τ = 0.054 ± 0.007.

    **Citation:** Planck 2018 -/
noncomputable def tau_Planck : ℝ := 0.054

/-- τ > 0 -/
theorem tau_Planck_pos : tau_Planck > 0 := by unfold tau_Planck; norm_num

/-- Planck Hubble constant: H_0 = 67.4 ± 0.5 km/s/Mpc.

    **Citation:** Planck 2018 -/
noncomputable def H_0_Planck : ℝ := 67.4

/-- H_0 > 0 -/
theorem H_0_Planck_pos : H_0_Planck > 0 := by unfold H_0_Planck; norm_num

end ChiralGeometrogenesis.Constants
