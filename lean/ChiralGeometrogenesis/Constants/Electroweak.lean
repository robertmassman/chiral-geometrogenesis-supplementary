/-
  Constants/Electroweak.lean — Electroweak constants, gauge boson masses,
  LHC cross-sections, oblique parameters, and electromagnetic constants.

  Sections 10, 23, 21, 22-EW, 22a, 24, 26-EM, 30 from the original Constants.lean,
  plus relocated Higgs/EW definitions from Sections 15a, 17, and 20.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import ChiralGeometrogenesis.Constants.Core
import ChiralGeometrogenesis.Constants.Geometry

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Constants

open Real

/-! ### Relocated Electroweak Definitions
    These were originally in Sections 15a, 17, and 20 but belong here
    because they are fundamental SM electroweak parameters.
-/

/-- Higgs VEV: v_H = 246.22 GeV (Standard Model).

    **Physical meaning:**
    The electroweak symmetry breaking scale derived from the Fermi constant:
    v_H = (√2 G_F)^{-1/2} = 246.22 GeV

    **Citation:** PDG 2024 -/
noncomputable def v_H_GeV : ℝ := 246.22

/-- v_H > 0 -/
theorem v_H_GeV_pos : v_H_GeV > 0 := by unfold v_H_GeV; norm_num

/-- Higgs mass: m_h = 125.11 GeV.

    **Citation:** PDG 2024, m_h = 125.11 ± 0.11 GeV -/
noncomputable def m_h_GeV : ℝ := 125.11

/-- m_h > 0 -/
theorem m_h_GeV_pos : m_h_GeV > 0 := by unfold m_h_GeV; norm_num

/-- Higgs self-coupling: λ_H = m_H²/(2v_H²) = 0.129.

    **Physical meaning:**
    Standard Model Higgs quartic coupling.

    **Citation:** PDG 2024 -/
noncomputable def lambda_H : ℝ := 0.129

/-- λ_H > 0 -/
theorem lambda_H_pos : lambda_H > 0 := by unfold lambda_H; norm_num

/-- Observed weak mixing angle at M_Z: sin²θ_W = 0.23122 (PDG 2024) -/
noncomputable def sin_sq_theta_W_PDG : ℝ := 0.23122

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 10: ELECTROWEAK CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Standard Model electroweak parameters.
-/

/-- Weak mixing angle: sin²θ_W = 0.2232 (ON-SHELL scheme).

    **Physical meaning:**
    The Weinberg angle relates the electromagnetic and weak couplings:
    e = g sin θ_W = g' cos θ_W

    **On-shell definition:**
    sin²θ_W = 1 - M_W²/M_Z² = 1 - (80.3692/91.1876)² ≈ 0.2232

    **Scheme distinction:**
    - On-shell (this value): sin²θ_W = 0.2232 (from mass ratio)
    - MS-bar (PDG): sin²θ_W = 0.23122 ± 0.00003 (running parameter)

    Use on-shell for tree-level amplitude calculations where gauge boson
    masses appear explicitly. Use MS-bar for precision EW fits and RG running.

    **Citation:** PDG 2024 -/
noncomputable def sinSqThetaW : ℝ := 0.2232

/-- sin²θ_W > 0 -/
theorem sinSqThetaW_pos : sinSqThetaW > 0 := by
  unfold sinSqThetaW; norm_num

/-- sin²θ_W < 1 (physical constraint) -/
theorem sinSqThetaW_lt_one : sinSqThetaW < 1 := by
  unfold sinSqThetaW; norm_num

/-- **sinSqThetaW matches the on-shell definition from mass ratios.**

    This theorem verifies that sinSqThetaW = 0.2232 is consistent with
    the on-shell definition sin²θ_W = 1 - (M_W/M_Z)².

    **Calculation:**
    1 - (80.3692/91.1876)² = 1 - 0.7768 ≈ 0.2232

    The small discrepancy (< 0.001) is due to rounding in the mass values.

    Note: Uses inline values since M_W_GeV/M_Z_GeV are defined later in file. -/
theorem sinSqThetaW_matches_onshell :
    |sinSqThetaW - (1 - (80.3692 / 91.1876)^2)| < 0.001 := by
  unfold sinSqThetaW
  -- sinSqThetaW = 0.2232
  -- 1 - (80.3692/91.1876)² ≈ 0.22319
  norm_num

/-- Difference between on-shell and MS-bar schemes.

    **Physical meaning:**
    The ~0.009 difference arises from radiative corrections absorbed
    differently in the two schemes. MS-bar: 0.23122, On-shell: 0.2232

    **Citation:** PDG 2024, Electroweak review

    Note: Uses inline MS-bar value since sin_sq_theta_W_MSbar defined later. -/
theorem scheme_difference :
    |(0.23122 : ℝ) - sinSqThetaW| < 0.01 := by
  unfold sinSqThetaW
  norm_num

/-- cot²θ_W = (1 - sin²θ_W)/sin²θ_W ≈ 3.48 -/
noncomputable def cotSqThetaW : ℝ := (1 - sinSqThetaW) / sinSqThetaW

/-- cot²θ_W > 0 -/
theorem cotSqThetaW_pos : cotSqThetaW > 0 := by
  unfold cotSqThetaW sinSqThetaW
  apply div_pos
  · norm_num
  · norm_num

/-- Dimension of the electroweak adjoint representation: dim(adj_EW) = 4.

    **Derivation:**
    dim(adj_EW) = dim(su(2)) + dim(u(1)) = 3 + 1 = 4

    **Physical meaning:**
    Counts the electroweak gauge generators:
    - SU(2)_L: 3 generators (W₁, W₂, W₃)
    - U(1)_Y: 1 generator (B)

    **Citation:** Proposition 0.0.19 §5.1 -/
def dim_adj_EW : ℕ := 4

/-- dim(adj_EW) = 4 (value check) -/
theorem dim_adj_EW_value : dim_adj_EW = 4 := rfl

/-- dim(adj_EW) > 0 -/
theorem dim_adj_EW_pos : dim_adj_EW > 0 := by decide

/-- Electroweak β-function index: index_EW ≈ 5.63.

    **Derivation (from Proposition 0.0.19 §5.3):**
    index_EW = |b₂| + |b₁| × (3/5)
             = 19/6 + 41/10 × 3/5
             = 19/6 + 123/50
             = 1688/300 ≈ 5.63

    where:
    - b₂ = -19/6 is the one-loop SU(2)_L β-function coefficient
    - b₁ = +41/10 is the one-loop U(1)_Y β-function coefficient
    - 3/5 is the GUT hypercharge normalization (from SU(5) embedding)

    **Physical meaning:**
    This is the combined electroweak β-function index that appears
    in the topological hierarchy formula, analogous to the QCD index.

    **Citation:** Proposition 0.0.19 §5.3, Costello-Bittleston (2025) -/
noncomputable def index_EW : ℝ := 1688 / 300

/-- index_EW > 0 -/
theorem index_EW_pos : index_EW > 0 := by
  unfold index_EW; norm_num

/-- index_EW ≈ 5.63 (numerical bounds) -/
theorem index_EW_approx : 5.62 < index_EW ∧ index_EW < 5.64 := by
  unfold index_EW
  constructor <;> norm_num

/-- SU(2)_L β-function coefficient: b₂ = -19/6.

    **Derivation:**
    b₂ = -(11/3)C₂(G) + (4/3)T(R)N_f + (1/3)T(R)N_H
       = -(11/3)×2 + (4/3)×(1/2)×3 + (1/3)×(1/2)×1
       = -22/3 + 2 + 1/6 = -19/6

    **Citation:** PDG 2024, SM running coupling review -/
noncomputable def b2_SU2 : ℝ := -19 / 6

/-- U(1)_Y β-function coefficient: b₁ = +41/10.

    **Derivation:**
    With GUT normalization g₁² = (5/3)g'²:
    b₁ = (4/3)×(3/5)×∑Y² = 41/10

    **Citation:** PDG 2024, SM running coupling review -/
noncomputable def b1_U1Y : ℝ := 41 / 10

/-- GUT hypercharge normalization factor: 3/5.

    **Physical meaning:**
    In SU(5) GUT, the hypercharge coupling is normalized as g₁² = (5/3)g'².
    The factor 3/5 appears when combining β-functions.

    **Citation:** Georgi & Glashow, PRL 32, 438 (1974) -/
noncomputable def GUT_hypercharge_normalization : ℝ := 3 / 5

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 23: ELECTROWEAK GAUGE BOSON CONSTANTS (Proposition 0.0.24)
    ═══════════════════════════════════════════════════════════════════════════

    Physical constants for electroweak sector consistency with GUT unification.
    Reference: docs/proofs/foundations/Proposition-0.0.24-SU2-Gauge-Coupling-From-Unification.md
-/

/-- SU(2) gauge coupling at M_Z (on-shell scheme): g₂ = 2M_W/v_H = 0.6528.

    **Physical meaning:**
    The weak isospin coupling constant in the on-shell renormalization scheme,
    defined as g₂ ≡ 2M_W/v_H.

    **Value:** g₂(M_Z) = 0.6528 ± 0.0010 (on-shell)

    **Citation:** PDG 2024, from M_W = 80.3692 GeV and v_H = 246.22 GeV -/
noncomputable def g2_MZ_onshell : ℝ := 0.6528

/-- g₂(M_Z) > 0 -/
theorem g2_MZ_onshell_pos : g2_MZ_onshell > 0 := by
  unfold g2_MZ_onshell; norm_num

/-- g₂(M_Z) < 1 (perturbativity constraint) -/
theorem g2_MZ_onshell_lt_one : g2_MZ_onshell < 1 := by
  unfold g2_MZ_onshell; norm_num

/-- W boson mass: M_W = 80.3692 GeV (PDG 2024).

    **Physical meaning:**
    The mass of the charged weak gauge boson W⁺.

    **Citation:** PDG 2024, M_W = 80.3692 ± 0.0133 GeV -/
noncomputable def M_W_GeV : ℝ := 80.3692

/-- M_W > 0 -/
theorem M_W_GeV_pos : M_W_GeV > 0 := by unfold M_W_GeV; norm_num

/-- Z boson mass: M_Z = 91.1876 GeV (PDG 2024).

    **Physical meaning:**
    The mass of the neutral weak gauge boson Z⁰.

    **Citation:** PDG 2024, M_Z = 91.1876 ± 0.0021 GeV -/
noncomputable def M_Z_GeV : ℝ := 91.1876

/-- M_Z > 0 -/
theorem M_Z_GeV_pos : M_Z_GeV > 0 := by unfold M_Z_GeV; norm_num

/-- Higgs VEV precise value: v_H = 246.22 GeV.

    **Physical meaning:**
    The electroweak symmetry breaking scale from Fermi constant:
    v_H = (√2 G_F)^{-1/2}

    **Citation:** PDG 2024 -/
noncomputable def v_H_precise_GeV : ℝ := 246.22

/-- v_H precise > 0 -/
theorem v_H_precise_GeV_pos : v_H_precise_GeV > 0 := by unfold v_H_precise_GeV; norm_num

/-- sin²θ_W at GUT scale: 3/8 = 0.375.

    **Physical meaning:**
    The Weinberg angle at the grand unification scale M_GUT ~ 10¹⁶ GeV,
    derived from SU(5) embedding: sin²θ_W = Tr(T₃²)/Tr(Q²) = (1/2)/(4/3) = 3/8.

    **Citation:** Theorem 0.0.4 §7, Georgi-Glashow (1974) -/
noncomputable def sin_sq_theta_W_GUT : ℝ := 3 / 8

/-- sin²θ_W(GUT) = 0.375 -/
theorem sin_sq_theta_W_GUT_value : sin_sq_theta_W_GUT = 0.375 := by
  unfold sin_sq_theta_W_GUT; norm_num

/-- sin²θ_W(GUT) > 0 -/
theorem sin_sq_theta_W_GUT_pos : sin_sq_theta_W_GUT > 0 := by
  unfold sin_sq_theta_W_GUT; norm_num

/-- sin²θ_W(GUT) < 1 -/
theorem sin_sq_theta_W_GUT_lt_one : sin_sq_theta_W_GUT < 1 := by
  unfold sin_sq_theta_W_GUT; norm_num

/-- sin²θ_W at M_Z (on-shell scheme): 1 - M_W²/M_Z² = 0.2232.

    **Physical meaning:**
    The Weinberg angle in the on-shell scheme, defined via gauge boson masses.

    **Citation:** PDG 2024 -/
noncomputable def sin_sq_theta_W_onshell : ℝ := 1 - (M_W_GeV / M_Z_GeV)^2

/-- sin²θ_W at M_Z (MS-bar scheme): 0.23122 ± 0.00003.

    **Physical meaning:**
    The Weinberg angle after RG running from GUT scale to M_Z.

    **Citation:** PDG 2024 -/
noncomputable def sin_sq_theta_W_MSbar : ℝ := 0.23122

/-- SU(3) β-function coefficient: b₃ = -7.

    **Physical meaning:**
    The one-loop β-function coefficient for SU(3)_C.
    Determines the running of the strong coupling α_s.

    **Derivation:**
    b₃ = -(11/3)C₂(G) + (4/3)T(R)N_f = -(11/3)×3 + (4/3)×(1/2)×6 = -11 + 4 = -7

    **Citation:** PDG 2024, QCD running review -/
noncomputable def b3_SU3 : ℝ := -7

/-- ρ parameter tree-level value: ρ = M_W²/(M_Z² cos²θ_W) = 1.

    **Physical meaning:**
    The custodial SU(2) symmetry parameter. Equals 1 at tree level.
    Deviations indicate new physics or radiative corrections.

    **Citation:** PDG 2024, ρ = 1.00038 ± 0.00020 (includes loop corrections) -/
noncomputable def rho_tree_level : ℝ := 1

/-- ρ tree-level = 1 -/
theorem rho_tree_level_value : rho_tree_level = 1 := rfl

/-- Logarithm of GUT to Z scale ratio: ln(M_GUT/M_Z) ≈ 33.

    **Physical meaning:**
    The number of e-foldings from M_Z to M_GUT, determines RG running magnitude.

    **Derivation:** ln(2×10¹⁶/91.2) ≈ 33.0 -/
noncomputable def ln_GUT_Z_ratio : ℝ := 33

/-- Verification: g₂ = 2M_W/v_H relationship.

    In the on-shell scheme, this is the definition of g₂. -/
theorem g2_from_MW_vH :
    |2 * M_W_GeV / v_H_precise_GeV - g2_MZ_onshell| < 0.001 := by
  unfold M_W_GeV v_H_precise_GeV g2_MZ_onshell
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 21: LHC CROSS-SECTION CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Constants for LHC cross-section predictions (Proposition 6.5.1).
    Reference: docs/proofs/Phase6/Proposition-6.5.1-LHC-Cross-Section-Predictions.md
-/

/-- Top quark mass: m_t = 172.5 GeV (PDG 2024).

    **Physical meaning:**
    The pole mass of the top quark. In CG, this corresponds to
    phase-gradient mass generation with η_t ≈ 1.

    **Citation:** PDG 2024, m_t = 172.57 ± 0.29 GeV -/
noncomputable def m_top_GeV : ℝ := 172.5

/-- m_t > 0 -/
theorem m_top_GeV_pos : m_top_GeV > 0 := by unfold m_top_GeV; norm_num

/-- Top mass uncertainty: ±0.5 GeV (combined) -/
noncomputable def m_top_uncertainty_GeV : ℝ := 0.5

/-- Strong coupling at top mass scale: α_s(m_t) = 0.108.

    **Physical meaning:**
    The running strong coupling evaluated at the top quark mass scale.
    In CG, this follows from geometric running (Prop 0.0.17s).

    **Citation:** PDG 2024, derived from α_s(M_Z) = 0.1180 -/
noncomputable def alpha_s_mt : ℝ := 0.108

/-- α_s(m_t) > 0 -/
theorem alpha_s_mt_pos : alpha_s_mt > 0 := by unfold alpha_s_mt; norm_num

/-- Electroweak EFT scale: Λ_EW = 10 TeV.

    **Physical meaning:**
    The scale at which CG form factor corrections become significant.
    Current LHC constraints: Λ_EW > 8 TeV.

    **Citation:** Proposition 6.5.1 §4.1 -/
noncomputable def Lambda_EW_TeV : ℝ := 10

/-- Λ_EW > 0 -/
theorem Lambda_EW_TeV_pos : Lambda_EW_TeV > 0 := by unfold Lambda_EW_TeV; norm_num

/-- Lower bound on Λ_EW from current data: 8 TeV -/
noncomputable def Lambda_EW_lower_bound_TeV : ℝ := 8

/-- Top quark pair production cross-section at 13 TeV: σ(tt̄) ≈ 834 pb (CG/SM prediction).

    **Physical meaning:**
    The inclusive tt̄ production cross-section at the LHC (13 TeV).
    CG prediction is identical to SM NNLO+NNLL.

    **Citation:** Top++v2.0, ATLAS/CMS 2024: 829 ± 19 pb -/
noncomputable def sigma_ttbar_13TeV_pb : ℝ := 834

/-- Experimental σ(tt̄) value: 829 pb -/
noncomputable def sigma_ttbar_exp_pb : ℝ := 829

/-- Experimental uncertainty on σ(tt̄): ±19 pb -/
noncomputable def sigma_ttbar_uncertainty_pb : ℝ := 19

/-- σ(tt̄) > 0 -/
theorem sigma_ttbar_pos : sigma_ttbar_13TeV_pb > 0 := by
  unfold sigma_ttbar_13TeV_pb; norm_num

/-- W boson production cross-section at 13 TeV: σ(W) ≈ 20.7 nb.

    **Physical meaning:**
    The inclusive W production cross-section (W+ + W-).
    CG with SM electroweak couplings matches SM prediction.

    **Citation:** ATLAS 2017: σ(W) = 20.6 ± 0.6 nb -/
noncomputable def sigma_W_13TeV_nb : ℝ := 20.7

/-- Experimental σ(W) value: 20.6 nb -/
noncomputable def sigma_W_exp_nb : ℝ := 20.6

/-- Experimental uncertainty on σ(W): ±0.6 nb -/
noncomputable def sigma_W_uncertainty_nb : ℝ := 0.6

/-- σ(W) > 0 -/
theorem sigma_W_pos : sigma_W_13TeV_nb > 0 := by
  unfold sigma_W_13TeV_nb; norm_num

/-- Z boson to dilepton cross-section at 13 TeV: σ(Z→ℓℓ) ≈ 1.98 nb.

    **Physical meaning:**
    The Z → ℓ⁺ℓ⁻ production cross-section.
    CG with SM electroweak couplings matches SM prediction.

    **Citation:** ATLAS 2017: σ(Z→ℓℓ) = 1.98 ± 0.04 nb -/
noncomputable def sigma_Z_ll_13TeV_nb : ℝ := 1.98

/-- Experimental σ(Z→ℓℓ) value: 1.98 nb -/
noncomputable def sigma_Z_ll_exp_nb : ℝ := 1.98

/-- Experimental uncertainty on σ(Z→ℓℓ): ±0.04 nb -/
noncomputable def sigma_Z_ll_uncertainty_nb : ℝ := 0.04

/-- σ(Z→ℓℓ) > 0 -/
theorem sigma_Z_ll_pos : sigma_Z_ll_13TeV_nb > 0 := by
  unfold sigma_Z_ll_13TeV_nb; norm_num

/-- Higgs production via gluon fusion at 13 TeV: σ(H, ggF) ≈ 48.5 pb.

    **Physical meaning:**
    The dominant Higgs production mode at LHC.
    CG predicts SM value (χ corrections suppressed by (v/Λ_EW)² ~ 10⁻⁴).

    **Citation:** CERN Yellow Report N³LO: 48.52 pb, ATLAS/CMS: 49.6 ± 5.2 pb -/
noncomputable def sigma_H_ggF_13TeV_pb : ℝ := 48.5

/-- Experimental σ(H, ggF) value: 49.6 pb -/
noncomputable def sigma_H_ggF_exp_pb : ℝ := 49.6

/-- Experimental uncertainty on σ(H, ggF): ±5.2 pb -/
noncomputable def sigma_H_ggF_uncertainty_pb : ℝ := 5.2

/-- σ(H, ggF) > 0 -/
theorem sigma_H_ggF_pos : sigma_H_ggF_13TeV_pb > 0 := by
  unfold sigma_H_ggF_13TeV_pb; norm_num

/-- Form factor correction coefficient: c_eff ≈ 1.

    **Physical meaning:**
    The effective coefficient in σ_CG/σ_SM = 1 + c_eff(p_T/Λ)².
    Incorporates QCD color factors and higher-order corrections.

    **Citation:** Proposition 6.5.1 §4.1 -/
noncomputable def form_factor_coeff : ℝ := 1

/-- Hexadecapole anisotropy coefficient ε₄ at TeV scale: ~10⁻³³.

    **Physical meaning:**
    The ℓ=4 Lorentz violation parameter from O_h stella symmetry.
    CG predicts ε₄ ~ (E/M_P)² with no ℓ=2 component.

    **Citation:** Theorem 0.0.14, Proposition 6.5.1 §4.2 -/
noncomputable def epsilon_4_TeV : ℝ := 1e-33

/-- Higgs trilinear deviation: δλ₃ ~ 1-10%.

    **Physical meaning:**
    The fractional deviation of the Higgs self-coupling from SM value
    due to χ-Higgs portal mixing.

    **Citation:** Proposition 6.5.1 §4.4 -/
noncomputable def delta_lambda3_min : ℝ := 0.01
noncomputable def delta_lambda3_max : ℝ := 0.10

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 22: ELECTROWEAK COUPLING CONSTANTS (PROPOSITION 0.0.26)
    ═══════════════════════════════════════════════════════════════════════════

    Fine structure constants and couplings for electroweak unitarity derivation.
    Reference: docs/proofs/foundations/Proposition-0.0.26-Electroweak-Cutoff-Derivation.md
-/

/-- SU(2)_L weak coupling constant: g₂ ≈ 0.653.

    **Physical meaning:**
    The gauge coupling for the weak isospin SU(2)_L group.

    **Relation:** α_W = g₂²/(4π) ≈ 0.0338

    **Citation:** PDG 2024, Electroweak review -/
noncomputable def g2_weak_coupling : ℝ := 0.653

/-- g₂ > 0 -/
theorem g2_weak_coupling_pos : g2_weak_coupling > 0 := by
  unfold g2_weak_coupling; norm_num

/-- SU(2)_L fine structure constant: α_W = g₂²/(4π) ≈ 0.0338.

    **Physical meaning:**
    The dimensionless coupling that controls weak interaction strength.
    At the Z-pole: α_W(M_Z) ≈ 0.0338

    **Citation:** PDG 2024, α₂⁻¹(M_Z) ≈ 29.6 → α₂ ≈ 0.0338 -/
noncomputable def alpha_W : ℝ := 0.0338

/-- α_W > 0 -/
theorem alpha_W_pos : alpha_W > 0 := by unfold alpha_W; norm_num

/-- α_W < 1 (perturbative) -/
theorem alpha_W_lt_one : alpha_W < 1 := by unfold alpha_W; norm_num

/-- α_W ≈ g₂²/(4π) consistency check.

    **Calculation:**
    g₂²/(4π) = 0.653²/(4×3.14159) = 0.426409/12.566 ≈ 0.0339
    |0.0338 - 0.0339| ≈ 0.0001 < 0.001 ✓ -/
theorem alpha_W_from_g2_approx :
    |alpha_W - g2_weak_coupling^2 / (4 * Real.pi)| < 0.001 := by
  unfold alpha_W g2_weak_coupling
  -- Numerical consistency check - defer detailed proof
  -- g₂²/(4π) = 0.653²/(4π) ≈ 0.0339, diff from 0.0338 is < 0.001
  sorry

/-- U(1)_Y hypercharge coupling: g' = g₁/√(5/3) ≈ 0.357.

    **Physical meaning:**
    The gauge coupling for the hypercharge U(1)_Y group.

    **Citation:** PDG 2024 -/
noncomputable def g1_hypercharge : ℝ := 0.357

/-- g' > 0 -/
theorem g1_hypercharge_pos : g1_hypercharge > 0 := by
  unfold g1_hypercharge; norm_num

/-- U(1)_Y fine structure constant: α_Y = g'²/(4π) ≈ 0.0102.

    **Physical meaning:**
    The dimensionless hypercharge coupling.
    At the Z-pole: α_Y(M_Z) ≈ 0.0102

    **Citation:** PDG 2024, α₁⁻¹(M_Z) ≈ 98 → α₁ ≈ 0.0102 -/
noncomputable def alpha_Y : ℝ := 0.0102

/-- α_Y > 0 -/
theorem alpha_Y_pos : alpha_Y > 0 := by unfold alpha_Y; norm_num

/-- α_Y < 1 (perturbative) -/
theorem alpha_Y_lt_one : alpha_Y < 1 := by unfold alpha_Y; norm_num

/-- α_Y < α_W (hypercharge is weaker than weak isospin) -/
theorem alpha_Y_lt_alpha_W : alpha_Y < alpha_W := by
  unfold alpha_Y alpha_W; norm_num

/-- cos²θ_W = 1 - sin²θ_W ≈ 0.7768.

    **Citation:** PDG 2024, on-shell scheme -/
noncomputable def cosSqThetaW : ℝ := 1 - sinSqThetaW

/-- cos²θ_W > 0 -/
theorem cosSqThetaW_pos : cosSqThetaW > 0 := by
  unfold cosSqThetaW sinSqThetaW; norm_num

/-- cos²θ_W < 1 -/
theorem cosSqThetaW_lt_one : cosSqThetaW < 1 := by
  unfold cosSqThetaW sinSqThetaW; norm_num

/-- sin²θ_W + cos²θ_W = 1 -/
theorem sin_cos_theta_W_sum : sinSqThetaW + cosSqThetaW = 1 := by
  unfold cosSqThetaW; ring

/-- cosθ_W (MS-bar at M_Z): cos(θ_W) = √(1 - sin²θ_W) ≈ 0.8768.

    **Physical meaning:**
    The cosine of the weak mixing angle in the MS-bar scheme.
    Used in h → Zγ loop calculations where the Z coupling involves
    factors of 1/cos(θ_W).

    **Value:** √(1 - 0.23122) = √0.76878 ≈ 0.8768

    **Citation:** PDG 2024, derived from sin²θ_W(MS-bar) = 0.23122 -/
noncomputable def cos_theta_W_MSbar : ℝ := 0.8768

/-- cos_theta_W > 0 -/
theorem cos_theta_W_MSbar_pos : cos_theta_W_MSbar > 0 := by
  unfold cos_theta_W_MSbar; norm_num

/-- cos_theta_W < 1 -/
theorem cos_theta_W_MSbar_lt_one : cos_theta_W_MSbar < 1 := by
  unfold cos_theta_W_MSbar; norm_num

/-- cos²θ_W(MS-bar) + sin²θ_W(MS-bar) ≈ 1 (consistency check).

    cos_theta_W_MSbar² + sin_sq_theta_W_PDG
    = 0.8768² + 0.23122 ≈ 0.76878 + 0.23122 ≈ 1.0000
    (Small residual from rounding cos_theta_W to 4 decimal places) -/
theorem cos_sin_MSbar_sum :
    |cos_theta_W_MSbar^2 + sin_sq_theta_W_PDG - 1| < 0.0001 := by
  unfold cos_theta_W_MSbar sin_sq_theta_W_PDG; norm_num

/-- Number of stella octangula vertices: n = 8.

    **Physical meaning:**
    The stella octangula (compound of two tetrahedra) has 8 vertices.
    This sets the tree-level vertex count in the unitarity formula.

    **Citation:** Proposition 0.0.27, Definition 0.1.1 -/
def n_stella_vertices : ℕ := 8

/-- n = 8 (value check) -/
theorem n_stella_vertices_value : n_stella_vertices = 8 := rfl

/-- n_stella_vertices = stella_boundary_vertices -/
theorem n_stella_eq_boundary : n_stella_vertices = stella_boundary_vertices := rfl

/-- n_stella_vertices > 0 -/
theorem n_stella_vertices_pos : n_stella_vertices > 0 := by decide

/-- Higgs quartic coupling (CG geometric prediction): λ_geo = 1/8 = 0.125.

    **Physical meaning:**
    The Higgs self-coupling λ in V(H) = μ²|H|² + λ|H|⁴.
    Derived from the 8 vertices of the stella octangula: λ = 1/n = 1/8.

    **Comparison:**
    - CG prediction: λ_geo = 1/8 = 0.125
    - SM measured: λ_H = 0.129 ± 0.004 (PDG 2024)
    - Agreement: 3% (within experimental uncertainty)

    **Citation:** Proposition 0.0.27 -/
noncomputable def lambda_H_geometric : ℝ := 1 / 8

/-- λ_geo > 0 -/
theorem lambda_H_geometric_pos : lambda_H_geometric > 0 := by
  unfold lambda_H_geometric; norm_num

/-- λ_geo = 1/8 -/
theorem lambda_H_geometric_value : lambda_H_geometric = 1 / 8 := rfl

/-- λ_geo = 0.125 -/
theorem lambda_H_geometric_decimal : lambda_H_geometric = 0.125 := by
  unfold lambda_H_geometric; norm_num

/-- λ_geo < 1 -/
theorem lambda_H_geometric_lt_one : lambda_H_geometric < 1 := by
  unfold lambda_H_geometric; norm_num

/-- CG prediction agrees with SM measurement to ~3%.

    λ_geo = 0.125, λ_H(SM) = 0.129
    |0.125 - 0.129| / 0.129 = 3.1% -/
theorem lambda_H_geometric_agrees_with_SM :
    |lambda_H_geometric - lambda_H| / lambda_H < 0.04 := by
  unfold lambda_H_geometric lambda_H
  norm_num

/-- Lee-Quigg-Thacker unitarity bound: Λ_LQT ≈ 1502 GeV.

    **Physical meaning:**
    The scale where W_L W_L → W_L W_L would violate unitarity without
    new physics. Derived from √(8π²/(3G_F)).

    **Citation:** Lee, Quigg, Thacker, Phys. Rev. D 16, 1519 (1977) -/
noncomputable def Lambda_LQT_GeV : ℝ := 1502

/-- Λ_LQT > 0 -/
theorem Lambda_LQT_pos : Lambda_LQT_GeV > 0 := by unfold Lambda_LQT_GeV; norm_num

/-- Λ_LQT > 1 TeV -/
theorem Lambda_LQT_gt_TeV : Lambda_LQT_GeV > 1000 := by unfold Lambda_LQT_GeV; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 22a: SPHALERON CONSTANTS (PROPOSITION 4.2.4)
    ═══════════════════════════════════════════════════════════════════════════

    Constants for sphaleron rate and energy calculations.
    Reference: docs/proofs/Phase4/Proposition-4.2.4-Sphaleron-Rate-From-CG-Topology.md
-/

/-- Sphaleron lattice prefactor: κ = 18 ± 3.

    **Physical meaning:**
    Non-perturbative prefactor in the sphaleron rate formula
    Γ_sph = κ α_W⁵ T⁴ in the symmetric phase.

    **Citation:** D'Onofrio, Rummukainen & Tranberg (2014),
    Phys. Rev. Lett. 113:141602 [arXiv:1404.3565] -/
noncomputable def sphaleron_kappa : ℝ := 18

/-- κ > 0 -/
theorem sphaleron_kappa_pos : sphaleron_kappa > 0 := by
  unfold sphaleron_kappa; norm_num

/-- Sphaleron shape function: B(λ_H/g₂²) ≈ 1.87.

    **Physical meaning:**
    Dimensionless shape function from the numerical sphaleron
    profile solution. Depends on the ratio λ_H/g₂².

    For λ_H/g₂² ≈ 0.30: B ≈ 1.87

    Asymptotic limits:
    - B(0) = 1.52 (pure gauge)
    - B(∞) → 2.72 (heavy Higgs)

    **Citation:** Klinkhamer & Manton (1984), Phys. Rev. D 30:2212;
    Arnold & McLerran (1987), Phys. Rev. D 36:581 -/
noncomputable def sphaleron_shape_B : ℝ := 1.87

/-- B > 0 -/
theorem sphaleron_shape_B_pos : sphaleron_shape_B > 0 := by
  unfold sphaleron_shape_B; norm_num

/-- B > 1 (shape function exceeds pure gauge limit) -/
theorem sphaleron_shape_B_gt_one : sphaleron_shape_B > 1 := by
  unfold sphaleron_shape_B; norm_num

/-- SU(2) on-shell coupling: g₂ = 0.6528 (defined as 2M_W/v_H).

    **Physical meaning:**
    On-shell weak coupling used in sphaleron energy calculation.
    g₂ = 2 × 80.37 / 246.22 = 0.6528

    Note: This is slightly different from the Z-pole value g₂ = 0.653
    used in g2_weak_coupling. The on-shell value is appropriate for
    sphaleron calculations at T ~ 100 GeV.

    **Citation:** Proposition 0.0.24, PDG 2024 -/
noncomputable def g2_onshell : ℝ := 0.6528

/-- g₂_onshell > 0 -/
theorem g2_onshell_pos : g2_onshell > 0 := by
  unfold g2_onshell; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 24: OBLIQUE PARAMETER CONSTANTS (Proposition 0.0.24a)
    ═══════════════════════════════════════════════════════════════════════════

    Peskin-Takeuchi oblique parameters (S, T, U) experimental values
    and CG framework constants.
    Reference: docs/proofs/foundations/Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md
-/

/-- S parameter experimental central value (PDG 2024): S = -0.01.

    **Citation:** PDG 2024, Electroweak Model and Constraints on New Physics -/
noncomputable def S_PDG_central : ℝ := -0.01

/-- S parameter experimental uncertainty (PDG 2024): ±0.07 -/
noncomputable def S_PDG_uncertainty : ℝ := 0.07

/-- S uncertainty > 0 -/
theorem S_PDG_uncertainty_pos : S_PDG_uncertainty > 0 := by
  unfold S_PDG_uncertainty; norm_num

/-- T parameter experimental central value (PDG 2024): T = +0.05.

    **Citation:** PDG 2024, Electroweak Model and Constraints on New Physics -/
noncomputable def T_PDG_central : ℝ := 0.05

/-- T parameter experimental uncertainty (PDG 2024): ±0.06 -/
noncomputable def T_PDG_uncertainty : ℝ := 0.06

/-- T uncertainty > 0 -/
theorem T_PDG_uncertainty_pos : T_PDG_uncertainty > 0 := by
  unfold T_PDG_uncertainty; norm_num

/-- U parameter experimental central value (PDG 2024): U = +0.02.

    **Citation:** PDG 2024, Electroweak Model and Constraints on New Physics -/
noncomputable def U_PDG_central : ℝ := 0.02

/-- U parameter experimental uncertainty (PDG 2024): ±0.09 -/
noncomputable def U_PDG_uncertainty : ℝ := 0.09

/-- U uncertainty > 0 -/
theorem U_PDG_uncertainty_pos : U_PDG_uncertainty > 0 := by
  unfold U_PDG_uncertainty; norm_num

/-- Electroweak EFT scale in GeV: Λ_EW = 10000 GeV (= 10 TeV).

    **Physical meaning:**
    The cutoff scale for CG form factor corrections.
    Equivalent to Lambda_EW_TeV × 1000.

    **Citation:** Proposition 0.0.24a §4, Proposition 6.5.1 §4.1 -/
noncomputable def Lambda_EW_GeV : ℝ := 10000

/-- Λ_EW (GeV) > 0 -/
theorem Lambda_EW_GeV_pos : Lambda_EW_GeV > 0 := by unfold Lambda_EW_GeV; norm_num

/-- Λ_EW consistency: GeV value = 1000 × TeV value -/
theorem Lambda_EW_consistency : Lambda_EW_GeV = 1000 * Lambda_EW_TeV := by
  unfold Lambda_EW_GeV Lambda_EW_TeV; norm_num

/-- Mass ratio squared: (m_H/Λ)² = (125.11/10000)² ≈ 1.57 × 10⁻⁴.

    **Physical meaning:**
    This is the suppression factor for oblique parameter loop corrections.
    The heavy suppression ensures CG predictions are SM-like.

    **Citation:** Proposition 0.0.24a §4.4 -/
noncomputable def mH_over_Lambda_sq : ℝ := (m_h_GeV / Lambda_EW_GeV) ^ 2

/-- (m_H/Λ)² > 0 -/
theorem mH_over_Lambda_sq_pos : mH_over_Lambda_sq > 0 := by
  unfold mH_over_Lambda_sq
  exact sq_pos_of_pos (div_pos m_h_GeV_pos Lambda_EW_GeV_pos)

/-- (m_H/Λ)² < 1 (hierarchy exists) -/
theorem mH_over_Lambda_sq_lt_one : mH_over_Lambda_sq < 1 := by
  unfold mH_over_Lambda_sq m_h_GeV Lambda_EW_GeV
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 26: ELECTROMAGNETIC AND FERMI CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    QED fine structure constant and Fermi constant.
    Used in loop-level calculations (e.g., h → γγ, Proposition 6.3.3).
-/

/-- Fine structure constant: α = e²/(4π) = 1/137.036.

    **Physical meaning:**
    The dimensionless coupling strength of quantum electrodynamics.

    **Citation:** PDG 2024, α⁻¹ = 137.035999177 ± 0.000000021 -/
noncomputable def alpha_em : ℝ := 1 / 137.036

/-- α > 0 -/
theorem alpha_em_pos : alpha_em > 0 := by unfold alpha_em; norm_num

/-- α < 1 (perturbative) -/
theorem alpha_em_lt_one : alpha_em < 1 := by unfold alpha_em; norm_num

/-- Inverse fine structure constant: α⁻¹ = 137.036 -/
noncomputable def alpha_em_inv : ℝ := 137.036

/-- α × α⁻¹ = 1 -/
theorem alpha_em_inv_relation : alpha_em * alpha_em_inv = 1 := by
  unfold alpha_em alpha_em_inv; field_simp

/-- Fermi constant: G_F = 1.1664 × 10⁻⁵ GeV⁻².

    **Physical meaning:**
    Effective strength of weak interactions at low energies.
    G_F/√2 = g₂²/(8M_W²) = 1/(2v_H²)

    **Citation:** PDG 2024, G_F = 1.1663787(6) × 10⁻⁵ GeV⁻² -/
noncomputable def G_F_GeV : ℝ := 1.1664e-5

/-- G_F > 0 -/
theorem G_F_GeV_pos : G_F_GeV > 0 := by unfold G_F_GeV; norm_num

/-- Top quark mass: m_t = 172.5 GeV.

    **Physical meaning:**
    Pole mass of the top quark. In CG, determined by phase-gradient
    mechanism with η_t ~ 1.

    **Citation:** PDG 2024, m_t = 172.52 ± 0.33 GeV -/
noncomputable def m_t_GeV : ℝ := 172.5

/-- m_t > 0 -/
theorem m_t_GeV_pos : m_t_GeV > 0 := by unfold m_t_GeV; norm_num

/-- Bottom quark mass: m_b = 4.18 GeV (MS-bar at m_b).

    **Citation:** PDG 2024 -/
noncomputable def m_b_GeV : ℝ := 4.18

/-- m_b > 0 -/
theorem m_b_GeV_pos : m_b_GeV > 0 := by unfold m_b_GeV; norm_num

/-- Tau lepton mass: m_τ = 1.777 GeV.

    **Citation:** PDG 2024, m_τ = 1776.86 ± 0.12 MeV -/
noncomputable def m_tau_GeV : ℝ := 1.777

/-- m_τ > 0 -/
theorem m_tau_GeV_pos : m_tau_GeV > 0 := by unfold m_tau_GeV; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 30: HIGGS TRILINEAR COUPLING CONSTANTS (PROPOSITION 0.0.37)
    ═══════════════════════════════════════════════════════════════════════════

    Constants for the Higgs trilinear self-coupling ratio κ_λ.
    Reference: docs/proofs/foundations/Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md
-/

/-- Higgs pole mass (PDG 2024 updated): m_H = 125.20 GeV.

    **Physical meaning:**
    The physical (pole) mass of the Higgs boson measured at the LHC.

    **Citation:** PDG 2024, m_H = 125.20 ± 0.11 GeV -/
noncomputable def m_H_pole_GeV : ℝ := 125.20

/-- m_H_pole > 0 -/
theorem m_H_pole_GeV_pos : m_H_pole_GeV > 0 := by unfold m_H_pole_GeV; norm_num

/-- SM Higgs quartic coupling: λ_SM = m_H²/(2v²) ≈ 0.1293.

    **Physical meaning:**
    The effective Higgs self-coupling extracted from experiment,
    absorbing all radiative corrections into a single measured parameter.

    **Citation:** PDG 2024, from m_H = 125.20 GeV, v = 246.22 GeV -/
noncomputable def lambda_SM : ℝ := m_H_pole_GeV ^ 2 / (2 * v_H_GeV ^ 2)

/-- λ_SM > 0 -/
theorem lambda_SM_pos : lambda_SM > 0 := by
  unfold lambda_SM m_H_pole_GeV v_H_GeV
  positivity

/-- Top Yukawa coupling (CG prediction): y_t = 1.0.

    **Physical meaning:**
    The top quark Yukawa coupling in the CG framework.
    Quasi-fixed point value from Extension 3.1.2c.
    SM value: y_t^SM = √2 m_t/v ≈ 0.991.

    **Citation:** Extension 3.1.2c -/
noncomputable def y_t_CG : ℝ := 1.0

/-- y_t_CG > 0 -/
theorem y_t_CG_pos : y_t_CG > 0 := by unfold y_t_CG; norm_num

/-- Higgs trilinear coupling ratio: κ_λ = 0.97 (central value).

    **Physical meaning:**
    The ratio of the CG-predicted Higgs trilinear self-coupling
    to the SM value: κ_λ ≡ λ₃^CG / λ₃^SM.

    **Citation:** Proposition 0.0.37 -/
noncomputable def kappa_lambda_central : ℝ := 0.97

/-- κ_λ > 0 -/
theorem kappa_lambda_central_pos : kappa_lambda_central > 0 := by
  unfold kappa_lambda_central; norm_num

/-- κ_λ uncertainty: ±0.03 (1σ from Monte Carlo).

    **Citation:** Proposition 0.0.37 §8 -/
noncomputable def kappa_lambda_uncertainty : ℝ := 0.03

/-- One-loop Coleman-Weinberg correction to κ_λ: δ_loop = -0.002.

    **Physical meaning:**
    The shift in the trilinear ratio from one-loop effects.
    Small because gauge boson loops cancel in the CG/SM ratio.

    **Citation:** Proposition 0.0.37 §7 -/
noncomputable def delta_loop_kappa : ℝ := -0.002

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION: CKM / WOLFENSTEIN PARAMETERS
    ═══════════════════════════════════════════════════════════════════════════

    Complete Wolfenstein parameters from PDG 2024 CKM global fit and
    geometric predictions from Extension 3.1.2b.

    Reference: PDG 2024, Navas et al., Phys. Rev. D 110, 030001
    Reference: docs/proofs/Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md
-/

-- Note: wolfenstein_lambda_geometric, wolfenstein_lambda_PDG, and related
-- theorems are defined in Constants/Neutrino.lean.

/-- Wolfenstein A parameter (PDG 2024 global CKM fit): A = 0.826 ± 0.015.

    **Physical meaning:**
    Controls 2nd↔3rd generation mixing: |V_cb| = Aλ².

    **Citation:** PDG 2024, CKM global fit -/
noncomputable def wolfenstein_A_PDG : ℝ := 0.826

/-- Uncertainty on A (1σ) -/
noncomputable def wolfenstein_A_PDG_uncertainty : ℝ := 0.015

/-- A_PDG > 0 -/
theorem wolfenstein_A_PDG_pos : wolfenstein_A_PDG > 0 := by
  unfold wolfenstein_A_PDG; norm_num

/-- Wolfenstein A parameter (GEOMETRIC PREDICTION): A = sin(36°)/sin(45°) ≈ 0.8313.

    **Derivation (Extension 3.1.2b §5.2):**
    A = sin(π/5) / sin(π/4) = √((5−√5)/4)

    Ratio of pentagonal (5-fold) to octahedral (4-fold) symmetry.

    **Agreement:** 0.35σ from PDG -/
noncomputable def wolfenstein_A_geometric : ℝ :=
  Real.sin (π / 5) / Real.sin (π / 4)

/-- Wolfenstein ρ̄ (PDG 2024 global CKM fit): ρ̄ = 0.1581 ± 0.0092.

    **Physical meaning:**
    Rephasing-invariant CP-violation parameter, real part of unitarity triangle apex.

    **Citation:** PDG 2024, CKM global fit -/
noncomputable def wolfenstein_rhobar_PDG : ℝ := 0.1581

/-- Uncertainty on ρ̄ (1σ) -/
noncomputable def wolfenstein_rhobar_PDG_uncertainty : ℝ := 0.0092

/-- ρ̄_PDG > 0 -/
theorem wolfenstein_rhobar_PDG_pos : wolfenstein_rhobar_PDG > 0 := by
  unfold wolfenstein_rhobar_PDG; norm_num

/-- Wolfenstein η̄ (PDG 2024 global CKM fit): η̄ = 0.3548 ± 0.0072.

    **Physical meaning:**
    Rephasing-invariant CP-violation parameter, imaginary part of unitarity triangle apex.

    **Citation:** PDG 2024, CKM global fit -/
noncomputable def wolfenstein_etabar_PDG : ℝ := 0.3548

/-- Uncertainty on η̄ (1σ) -/
noncomputable def wolfenstein_etabar_PDG_uncertainty : ℝ := 0.0072

/-- η̄_PDG > 0 (CP violation exists) -/
theorem wolfenstein_etabar_PDG_pos : wolfenstein_etabar_PDG > 0 := by
  unfold wolfenstein_etabar_PDG; norm_num

/-- CKM unitarity triangle angle β (PDG 2024): β = 22.9° ± 0.7°.

    **Physical meaning:**
    Measured via B⁰ → J/ψ K_S (sin 2β).

    **Citation:** PDG 2024, CKM global fit -/
noncomputable def CKM_beta_PDG_deg : ℝ := 22.9

/-- Uncertainty on β (1σ, degrees) -/
noncomputable def CKM_beta_PDG_uncertainty_deg : ℝ := 0.7

/-- CKM unitarity triangle angle γ (PDG 2024): γ = 66.0° ± 3.4°.

    **Physical meaning:**
    Measured via B → DK.

    **Citation:** PDG 2024, CKM global fit -/
noncomputable def CKM_gamma_PDG_deg : ℝ := 66.0

/-- Uncertainty on γ (1σ, degrees) -/
noncomputable def CKM_gamma_PDG_uncertainty_deg : ℝ := 3.4

/-- Jarlskog invariant (PDG 2024): J = (3.08 ± 0.15) × 10⁻⁵.

    **Physical meaning:**
    Unique rephasing-invariant measure of CP violation:
    J = Im(V_us V_cb V_ub* V_cs*)

    **Citation:** PDG 2024, CKM global fit -/
noncomputable def jarlskog_PDG : ℝ := 3.08e-5

/-- Uncertainty on J (1σ) -/
noncomputable def jarlskog_PDG_uncertainty : ℝ := 0.15e-5

/-- J_PDG > 0 (CP violation exists) -/
theorem jarlskog_PDG_pos : jarlskog_PDG > 0 := by
  unfold jarlskog_PDG; norm_num

end ChiralGeometrogenesis.Constants
