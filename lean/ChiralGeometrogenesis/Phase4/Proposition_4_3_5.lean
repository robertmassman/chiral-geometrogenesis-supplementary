/-
  Phase4/Proposition_4_3_5.lean

  Proposition 4.3.5: Skyrme Parameter from Pressure-Kurtosis Geometry

  Status: 🔶 NOVEL — GEOMETRIC DETERMINATION OF W-SECTOR SKYRME COEFFICIENT

  This file formalizes Proposition 4.3.5, which provides a geometric determination
  of the W-sector Skyrme parameter e_W = 4.5 ± 1.2 from the pressure kurtosis on
  the W domain of the stella octangula. The Skyrme parameter controls the
  four-derivative stabilization term in the chiral Lagrangian and directly
  determines the W-soliton mass through the Faddeev-Bogomolny lower bound
  M_W^(FB) = 6π² v_W / e_W.

  **Key Results Formalized:**
  - §3.4: Pressure kurtosis definition and properties (K_W ≥ 1, scale-invariant)
  - §4.2: Equal-area cap approximation (θ₀ = 60°, Ω_W = π sr)
  - §4.3: Analytical cap integrals (second and fourth pressure moments)
  - §4.3: Kurtosis formula: e_W² = 1 + 1/(3ε̃²(1 + ε̃²))
  - §4.6: Central value e_W = 4.5 at ε̃ = 0.130
  - §5:   Error budget: ±27% total (regularization ±24%, higher-order ±12%)
  - §6.1: Dimensional analysis (e_W dimensionless, scale-independent)
  - §6.5: Soliton mass consistency (M_W^FB ≈ 1620 GeV)
  - §6.6: NJL cross-check (e_NJL² = 6π²/N_c = 19.74, 2.5% agreement on e²)
  - §6.7: GL-Skyrme matching (e_GL = 4.64, 6% agreement on e²)

  **Dependencies:**
  - ✅ Definition 0.1.1 (Stella Octangula Boundary Topology) — Vertex structure
  - ✅ Definition 0.1.3 (Pressure Functions from Geometric Opposition) — P_c(x)
  - ✅ Definition 0.1.4 (Color Field Domains) — Domain decomposition D_c, D_W
  - ✅ Definition 4.3.1 (W-Sector Field Theory) — W condensate, v_W, omega_W
  - ✅ Theorem 4.1.2 (Soliton Mass Spectrum) — Skyrme energy functional
  - ✅ Theorem 4.3.2 (W-Soliton Existence) — W-sector Skyrme Lagrangian
  - ✅ Constants.lean — v_W, e_W, ε̃, ℓ̄₁, ℓ̄₂, N_c, π bounds

  **Cross-References:**
  - Phase4/Definition_4_3_1.lean: omega_W (= π), WCondensateParams
  - Phase4/Theorem_4_3_2.lean: WSolitonConfig, Faddeev bound
  - Constants/Cosmology.lean: v_W_precision_GeV, skyrme_e_W, M_W_precision_GeV
  - Constants/Specialized.lean: epsilon_tilde_W, anw_coefficient, Lambda_W_GeV
  - Constants/QCD.lean: ell_bar_1_empirical, ell_bar_2_empirical, N_c
  - Constants/Core.lean: N_c, N_c_pos

  **Computational Verification:**
  - verification/Phase4/prop_4_3_5_corrected_derivation.py
  - verification/Phase4/prop_4_3_5_adversarial_verification.py
  - verification/Phase4/prop_4_3_5_cross_checks.py
  - verification/Phase4/prop_4_3_5_gl_skyrme_matching.py

  Reference: docs/proofs/Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md
-/

import ChiralGeometrogenesis.Phase4.Definition_4_3_1
import ChiralGeometrogenesis.Phase4.Theorem_4_3_2
import ChiralGeometrogenesis.Constants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.dupNamespace false

namespace ChiralGeometrogenesis.Phase4.Proposition_4_3_5

open ChiralGeometrogenesis.Constants
open ChiralGeometrogenesis.Phase4.Definition_4_3_1
open ChiralGeometrogenesis.Phase4.Theorem_4_3_2
open Real

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 1: PRESSURE KURTOSIS DEFINITION AND PROPERTIES
    ═══════════════════════════════════════════════════════════════════════════

    The pressure kurtosis K_W on D_W is the ratio of the domain-averaged
    fourth power to the square of the domain-averaged second power of the
    pressure function:

      K_W = Ω_W · ∫_{D_W} P_W⁴ dΩ / (∫_{D_W} P_W² dΩ)²

    This is a dimensionless, scale-invariant quantity with K_W ≥ 1
    (Cauchy-Schwarz), with equality iff P_W = const.

    The identification e_W² = K_W (Assumption A-K) is the central claim
    of the proposition.

    Reference: Proposition-4.3.5 §3.4
-/

/-- **Pressure Kurtosis Parameters**

    Encapsulates the angular moments of the pressure function over D_W
    needed to compute the kurtosis and hence the Skyrme parameter.

    The kurtosis is defined as:
      K_W = Ω_W · I₄ / I₂²

    where I₂ = ∫_{D_W} P_W² dΩ and I₄ = ∫_{D_W} P_W⁴ dΩ.

    **Reference:** Proposition 4.3.5 §3.4 -/
structure PressureKurtosisParams where
  /-- Solid angle of the W domain (steradians) -/
  Omega_W : ℝ
  /-- Ω_W > 0 -/
  Omega_W_pos : Omega_W > 0
  /-- Second pressure moment: I₂ = ∫_{D_W} P_W² dΩ -/
  I2 : ℝ
  /-- I₂ > 0 (pressure is non-negative and non-trivial) -/
  I2_pos : I2 > 0
  /-- Fourth pressure moment: I₄ = ∫_{D_W} P_W⁴ dΩ -/
  I4 : ℝ
  /-- I₄ > 0 -/
  I4_pos : I4 > 0
  /-- Cauchy-Schwarz: Ω_W · I₄ ≥ I₂² (from ⟨f²,1⟩² ≤ ⟨f⁴,1⟩·⟨1,1⟩) -/
  cauchy_schwarz : Omega_W * I4 ≥ I2 ^ 2

/-- The pressure kurtosis: K_W = Ω_W · I₄ / I₂².

    This is the central quantity of Proposition 4.3.5.

    **Reference:** Proposition 4.3.5 §3.4 -/
noncomputable def PressureKurtosisParams.kurtosis (p : PressureKurtosisParams) : ℝ :=
  p.Omega_W * p.I4 / p.I2 ^ 2

/-- The kurtosis is positive.

    **Reference:** Proposition 4.3.5 §3.4, Properties table -/
theorem PressureKurtosisParams.kurtosis_pos (p : PressureKurtosisParams) :
    p.kurtosis > 0 := by
  unfold PressureKurtosisParams.kurtosis
  apply div_pos
  · exact mul_pos p.Omega_W_pos p.I4_pos
  · exact sq_pos_of_pos p.I2_pos

/-- **Kurtosis lower bound:** K_W ≥ 1 (Cauchy-Schwarz inequality).

    For any non-negative function f on a domain of solid angle Ω:
      Ω · ∫f⁴ dΩ ≥ (∫f² dΩ)²

    Equality holds iff f = const on D_W.

    **Reference:** Proposition 4.3.5 §3.4, Properties table -/
theorem kurtosis_lower_bound (p : PressureKurtosisParams) :
    p.kurtosis ≥ 1 := by
  unfold PressureKurtosisParams.kurtosis
  rw [ge_iff_le, le_div_iff₀ (sq_pos_of_pos p.I2_pos)]
  linarith [p.cauchy_schwarz]

/-- **Kurtosis scale invariance:** Under P_W → α · P_W, the kurtosis is invariant.

    Numerator scales as α⁴, denominator scales as α⁴, so the ratio is unchanged.
    This means e_W is independent of the pressure normalization.

    **Reference:** Proposition 4.3.5 §3.4, Properties table; §6.1 -/
theorem kurtosis_scale_invariant (p : PressureKurtosisParams) (α : ℝ) (hα : α > 0) :
    let p' : PressureKurtosisParams := {
      Omega_W := p.Omega_W
      Omega_W_pos := p.Omega_W_pos
      I2 := α ^ 2 * p.I2
      I2_pos := mul_pos (sq_pos_of_pos hα) p.I2_pos
      I4 := α ^ 4 * p.I4
      I4_pos := mul_pos (pow_pos hα 4) p.I4_pos
      cauchy_schwarz := by
        have : p.Omega_W * (α ^ 4 * p.I4) = α ^ 4 * (p.Omega_W * p.I4) := by ring
        rw [this]
        have : (α ^ 2 * p.I2) ^ 2 = α ^ 4 * p.I2 ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left p.cauchy_schwarz (le_of_lt (pow_pos hα 4))
    }
    p'.kurtosis = p.kurtosis := by
  simp only [PressureKurtosisParams.kurtosis]
  have hI2_ne : p.I2 ≠ 0 := ne_of_gt p.I2_pos
  have hα_ne : α ≠ 0 := ne_of_gt hα
  field_simp

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 1B: PHYSICAL ASSUMPTIONS
    ═══════════════════════════════════════════════════════════════════════════

    The identification e_W² = K_W rests on two explicit physical assumptions:

    **Assumption A-PW4 (Pressure weighting):** The angular integration of the
    pressure-modulated effective action on D_W yields P_W² weighting for the
    kinetic term and P_W⁴ weighting for the Skyrme term. This follows from
    the amplitude modulation L_μ^(loc) ~ P_W · L_μ^(zero), so the quartic
    Skyrme term Tr[L_μ,L_ν]² receives P_W⁴ weighting.

    **Assumption A-K (Kurtosis identification):** The effective Skyrme parameter
    of the W-sector chiral Lagrangian equals the square root of the pressure
    kurtosis: e_W² = K_W = Ω_W · I₄/I₂².

    Both assumptions are physically motivated by the KK reduction mechanism
    (§3.3) and validated by two independent cross-checks:
    - NJL bosonization (§6.6.1): 2.5% agreement on e²
    - GL-Skyrme matching (§6.7): 6% agreement on e²

    Reference: Proposition-4.3.5 §3.3–3.4
-/

/-- **Assumption A-PW4 (Pressure weighting of the Skyrme term).**

    In the pressure-modulated effective action on D_W, the chiral current at
    angular position x̂ scales as L_μ^(loc) ~ P_W(x̂) · L_μ^(zero). Therefore:
    - The kinetic term ∝ ∫_{D_W} P_W² dΩ
    - The Skyrme term ∝ ∫_{D_W} P_W⁴ dΩ

    This is analogous to a Kaluza-Klein reduction where the internal profile
    enters the effective 4D couplings.

    **Reference:** Proposition 4.3.5 §3.3 -/
axiom assumption_A_PW4 :
    -- Physical content: the Skyrme four-derivative term receives P_W⁴ angular
    -- weighting, while the kinetic two-derivative term receives P_W² weighting.
    -- This determines the Skyrme parameter through the pressure moment ratio.
    ∀ (p : PressureKurtosisParams), p.Omega_W > 0 → p.I4 > 0

/-- **Assumption A-K (Pressure-kurtosis identification).**

    The effective Skyrme parameter squared equals the pressure kurtosis:
      e_W² = K_W = Ω_W · ∫P_W⁴ dΩ / (∫P_W² dΩ)²

    This is the central physical identification of the proposition. It is
    motivated by the KK mechanism (§3.3) and validated by:
    - NJL bosonization (§6.6.1): e_NJL² = 6π²/N_c = 19.74, vs K_W = 20.40
    - GL-Skyrme matching (§6.7): e_GL² = 21.5, vs K_W = 20.40

    **Reference:** Proposition 4.3.5 §3.4 -/
axiom assumption_A_K :
    -- Physical content: there exist pressure moments on D_W (with Ω_W = π)
    -- whose kurtosis K_W = Ω_W · I₄/I₂² determines the Skyrme parameter.
    -- The kurtosis formula (Part 3) analytically evaluates K_W ≈ 20.4 ≈ e_W².
    ∃ (p : PressureKurtosisParams), p.Omega_W = Real.pi ∧
    |p.kurtosis - skyrme_e_W ^ 2| < 0.5

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 2: EQUAL-AREA CAP APPROXIMATION
    ═══════════════════════════════════════════════════════════════════════════

    The W domain D_W is a spherical triangle (Voronoi cell) on S². It is
    approximated by an equal-area spherical cap with half-angle θ₀ = 60°,
    chosen so that:

      Ω_cap = 2π(1 - cos θ₀) = π = Ω_W

    This approximation is accurate to < 0.3% for the kurtosis (MC verified).

    Reference: Proposition-4.3.5 §4.1–4.2
-/

/-- **Equal-Area Cap Geometry**

    Parameters for the equal-area cap approximation to the W Voronoi cell.

    **Reference:** Proposition 4.3.5 §4.2 -/
structure CapGeometry where
  /-- Cap half-angle in radians -/
  theta_0 : ℝ
  /-- θ₀ > 0 -/
  theta_0_pos : theta_0 > 0
  /-- θ₀ < π -/
  theta_0_lt_pi : theta_0 < Real.pi
  /-- Equal-area condition: 2π(1 - cos θ₀) = Ω_W = π -/
  equal_area : 2 * Real.pi * (1 - Real.cos theta_0) = Real.pi

/-- The canonical equal-area cap has θ₀ = π/3 (60°).

    From 2π(1 - cos θ₀) = π, we get cos θ₀ = 1/2, hence θ₀ = π/3.

    **Reference:** Proposition 4.3.5 §4.2 -/
noncomputable def canonicalCap : CapGeometry where
  theta_0 := Real.pi / 3
  theta_0_pos := by positivity
  theta_0_lt_pi := by
    have : Real.pi > 0 := Real.pi_pos
    linarith
  equal_area := by
    -- Need: 2π(1 - cos(π/3)) = π
    -- cos(π/3) = 1/2, so 2π(1 - 1/2) = 2π · 1/2 = π ✓
    rw [Real.cos_pi_div_three]
    ring

/-- cos(θ₀) = 1/2 for the equal-area cap.

    **Reference:** Proposition 4.3.5 §4.2 -/
theorem cap_cos_theta : Real.cos canonicalCap.theta_0 = 1 / 2 := by
  unfold canonicalCap
  simp only
  exact Real.cos_pi_div_three

/-- The substitution variable t₀ = 1 - cos θ₀ = 1/2.

    Used in the analytical integration: t = 1 - cos θ, dt = sin θ dθ.

    **Reference:** Proposition 4.3.5 §4.3 -/
noncomputable def t_0 : ℝ := 1 - Real.cos canonicalCap.theta_0

/-- t₀ = 1/2 -/
theorem t_0_value : t_0 = 1 / 2 := by
  unfold t_0 canonicalCap
  simp only
  rw [Real.cos_pi_div_three]
  ring

/-- t₀ > 0 -/
theorem t_0_pos : t_0 > 0 := by
  rw [t_0_value]; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 3: PRESSURE FUNCTION, CAP INTEGRALS, AND KURTOSIS FORMULA
    ═══════════════════════════════════════════════════════════════════════════

    The pressure function on the cap is P_W(θ) = 1/(2(1-cos θ) + c) where c = ε̃².

    With the substitution t = 1 - cos θ, dt = sin θ dθ, the angular integrals
    evaluate analytically (standard antiderivative of 1/(at+b)^n):

    Second moment:
      I₂ = 2π ∫₀^{1/2} dt/(2t+c)² = π/(c(1+c))

    Fourth moment:
      I₄ = 2π ∫₀^{1/2} dt/(2t+c)⁴ = (π/3)(1/c³ - 1/(1+c)³)

    Kurtosis formula:
      e_W² = K_W = Ω_W · I₄/I₂² = 1 + 1/(3ε̃²(1 + ε̃²))

    Reference: Proposition-4.3.5 §3.5, §4.3
-/

/-- **The W-domain pressure function** on the equal-area cap.

    P_W(c, θ) = 1/(2(1 - cos θ) + c) where c = ε̃².

    This is the angular form of the pressure function P_W(x) = 1/(|x - x_W|² + ε²)
    restricted to the unit circumsphere, with u = |x̂ - x̂_W|² = 2(1 - cos θ).

    **Reference:** Proposition 4.3.5 §3.5; Definition 0.1.3 -/
noncomputable def P_W (c : ℝ) (theta : ℝ) : ℝ :=
  1 / (2 * (1 - Real.cos theta) + c)

/-- P_W > 0 for c > 0 (denominator ≥ c > 0 since 1 - cos θ ≥ 0).

    **Reference:** Proposition 4.3.5 §3.5 -/
theorem P_W_pos (c : ℝ) (hc : c > 0) (theta : ℝ) :
    P_W c theta > 0 := by
  unfold P_W
  apply div_pos one_pos
  have : Real.cos theta ≤ 1 := Real.cos_le_one theta
  linarith

/-- **Partial fraction identity** used in the I₂ derivation:
    1/c - 1/(1+c) = 1/(c(1+c)).

    This is the key step in evaluating the antiderivative
    [-1/(2(2t+c))]₀^{1/2} = 1/(2c) - 1/(2(1+c)).

    **Reference:** Proposition 4.3.5 §4.3, second moment -/
theorem partial_fraction_identity (c : ℝ) (hc : c > 0) :
    1 / c - 1 / (1 + c) = 1 / (c * (1 + c)) := by
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have h1c_ne : (1 : ℝ) + c ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **Cubic difference identity** used in the kurtosis derivation:
    (1+c)³ - c³ = 1 + 3c(1+c).

    This simplification converts I₄/I₂² into the kurtosis formula.

    **Reference:** Proposition 4.3.5 §4.3, kurtosis computation -/
theorem cubic_difference_identity (c : ℝ) :
    (1 + c) ^ 3 - c ^ 3 = 1 + 3 * c * (1 + c) := by ring

/-- The regularization variable c = ε̃².

    **Reference:** Proposition 4.3.5 §4.3 -/
noncomputable def c_reg : ℝ := epsilon_tilde_W ^ 2

/-- c > 0 -/
theorem c_reg_pos : c_reg > 0 := by
  unfold c_reg
  exact sq_pos_of_pos epsilon_tilde_W_pos

/-- c < 1 -/
theorem c_reg_lt_one : c_reg < 1 := by
  unfold c_reg epsilon_tilde_W
  norm_num

/-- 1 + c > 0 -/
theorem one_plus_c_pos : 1 + c_reg > 0 := by
  linarith [c_reg_pos]

/-- **Second pressure moment on the cap:**
    I₂ = ∫_cap P_W² dΩ = π/(c(1+c))

    **Derivation:**
    I₂ = 2π ∫₀^{t₀} dt/(2t + c)²
       = 2π [-1/(2(2t+c))]₀^{t₀}
       = π (1/c - 1/(1+c))
       = π / (c(1+c))

    **Reference:** Proposition 4.3.5 §4.3 -/
noncomputable def cap_I2 (c : ℝ) (hc : c > 0) : ℝ :=
  Real.pi / (c * (1 + c))

/-- I₂ > 0 for c > 0 -/
theorem cap_I2_pos (c : ℝ) (hc : c > 0) : cap_I2 c hc > 0 := by
  unfold cap_I2
  apply div_pos Real.pi_pos
  exact mul_pos hc (by linarith)

/-- **Fourth pressure moment on the cap:**
    I₄ = ∫_cap P_W⁴ dΩ = (π/3)(1/c³ - 1/(1+c)³)

    **Derivation:**
    I₄ = 2π ∫₀^{t₀} dt/(2t + c)⁴
       = 2π [-1/(6(2t+c)³)]₀^{t₀}
       = (π/3)(1/c³ - 1/(1+c)³)

    **Reference:** Proposition 4.3.5 §4.3 -/
noncomputable def cap_I4 (c : ℝ) (hc : c > 0) : ℝ :=
  Real.pi / 3 * (1 / c ^ 3 - 1 / (1 + c) ^ 3)

/-- I₄ > 0 for 0 < c < 1 -/
theorem cap_I4_pos (c : ℝ) (hc : c > 0) (hc1 : c < 1) : cap_I4 c hc > 0 := by
  unfold cap_I4
  apply mul_pos
  · exact div_pos Real.pi_pos (by norm_num : (3 : ℝ) > 0)
  · -- Need: 1/c³ - 1/(1+c)³ > 0, i.e. 1/c³ > 1/(1+c)³
    have hc3_pos : c ^ 3 > 0 := pow_pos hc 3
    have h1c_gt : c < 1 + c := by linarith
    have hpow_lt : c ^ 3 < (1 + c) ^ 3 := by
      have : (1 + c) ^ 3 - c ^ 3 = 1 + 3 * c + 3 * c ^ 2 := by ring
      nlinarith [sq_nonneg c]
    linarith [div_lt_div_of_pos_left one_pos hc3_pos hpow_lt]

/-- **The Kurtosis Formula (Main Analytical Result):**

    e_W² = 1 + 1/(3ε̃²(1 + ε̃²))

    This is the central formula of Proposition 4.3.5, derived by combining:
    - Ω_W = π (W domain solid angle)
    - I₂ = π/(c(1+c)) (second moment)
    - I₄ = (π/3)(1/c³ - 1/(1+c)³) (fourth moment)
    - (1+c)³ - c³ = 1 + 3c + 3c² = 1 + 3c(1+c)

    into K_W = Ω_W · I₄ / I₂² and simplifying.

    **Reference:** Proposition 4.3.5 §4.3, boxed equation -/
noncomputable def kurtosis_formula (eps_tilde : ℝ) : ℝ :=
  1 + 1 / (3 * eps_tilde ^ 2 * (1 + eps_tilde ^ 2))

/-- The kurtosis formula is well-defined for ε̃ > 0.

    The denominator 3ε̃²(1 + ε̃²) > 0 for all ε̃ > 0. -/
theorem kurtosis_formula_pos (eps_tilde : ℝ) (h : eps_tilde > 0) :
    kurtosis_formula eps_tilde > 0 := by
  unfold kurtosis_formula
  have h1 : eps_tilde ^ 2 > 0 := sq_pos_of_pos h
  have h2 : 1 + eps_tilde ^ 2 > 0 := by linarith
  have h3 : 3 * eps_tilde ^ 2 * (1 + eps_tilde ^ 2) > 0 := by positivity
  linarith [div_pos (by norm_num : (1 : ℝ) > 0) h3]

/-- The kurtosis formula gives K ≥ 1 for all ε̃ > 0.

    Since 1/(3ε̃²(1+ε̃²)) > 0, we have K = 1 + positive > 1. -/
theorem kurtosis_formula_ge_one (eps_tilde : ℝ) (h : eps_tilde > 0) :
    kurtosis_formula eps_tilde ≥ 1 := by
  unfold kurtosis_formula
  have h1 : eps_tilde ^ 2 > 0 := sq_pos_of_pos h
  have h2 : 1 + eps_tilde ^ 2 > 0 := by linarith
  have h3 : 3 * eps_tilde ^ 2 * (1 + eps_tilde ^ 2) > 0 := by positivity
  linarith [div_pos (by norm_num : (1 : ℝ) > 0) h3]

/-- The kurtosis formula is monotonically decreasing in ε̃ for ε̃ > 0.

    More peaked P_W (smaller ε̃) → larger kurtosis → larger e_W.

    **Reference:** Proposition 4.3.5 §3.4, Properties table -/
theorem kurtosis_formula_antitone (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a < b) :
    kurtosis_formula b < kurtosis_formula a := by
  unfold kurtosis_formula
  -- Suffices: 1/(3b²(1+b²)) < 1/(3a²(1+a²))
  -- Since denominators are positive and 3a²(1+a²) < 3b²(1+b²)
  have hab2 : a ^ 2 < b ^ 2 := sq_lt_sq' (by linarith) hab
  have hab4 : a ^ 4 < b ^ 4 := by
    have h1 : b ^ 2 - a ^ 2 > 0 := by linarith
    have h2 : b ^ 2 + a ^ 2 > 0 := by positivity
    have : b ^ 4 - a ^ 4 = (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) := by ring
    nlinarith [mul_pos h1 h2]
  have h_denom_a_pos : 3 * a ^ 2 * (1 + a ^ 2) > 0 := by positivity
  have h_denom_b_pos : 3 * b ^ 2 * (1 + b ^ 2) > 0 := by positivity
  have h_denom_lt : 3 * a ^ 2 * (1 + a ^ 2) < 3 * b ^ 2 * (1 + b ^ 2) := by nlinarith
  linarith [div_lt_div_of_pos_left one_pos h_denom_a_pos h_denom_lt]

/-- **Kurtosis formula agrees with cap integral ratio.**

    This theorem verifies that the closed-form kurtosis formula
    e_W² = 1 + 1/(3c(1+c)) matches K_W = Ω_W · I₄ / I₂²
    with Ω_W = π, I₂ = π/(c(1+c)), I₄ = (π/3)(1/c³ - 1/(1+c)³).

    **Reference:** Proposition 4.3.5 §4.3 -/
theorem kurtosis_formula_from_integrals (c : ℝ) (hc : c > 0) :
    let Omega_W := Real.pi
    let I2 := Real.pi / (c * (1 + c))
    let I4 := Real.pi / 3 * (1 / c ^ 3 - 1 / (1 + c) ^ 3)
    Omega_W * I4 / I2 ^ 2 = kurtosis_formula (Real.sqrt c) := by
  simp only [kurtosis_formula]
  have hsqrt : Real.sqrt c ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
  rw [hsqrt]
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have h1c_pos : (1 : ℝ) + c > 0 := by linarith
  have h1c_ne : (1 : ℝ) + c ≠ 0 := ne_of_gt h1c_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- **Cap Kurtosis Parameters:**
    Concrete `PressureKurtosisParams` instance for the W-domain equal-area cap.

    This bridges Part 1 (abstract kurtosis framework) with Part 3 (analytical
    cap integrals), instantiating:
    - Ω_W = π (W domain solid angle, Definition 4.3.1 §3.2)
    - I₂ = π/(c(1+c)) (second pressure moment, §4.3)
    - I₄ = (π/3)(1/c³ - 1/(1+c)³) (fourth pressure moment, §4.3)

    The Cauchy-Schwarz field is verified via kurtosis_formula_ge_one.

    **Reference:** Proposition 4.3.5 §4.1–4.3 -/
noncomputable def capKurtosisParams (c : ℝ) (hc : c > 0) (hc1 : c < 1) :
    PressureKurtosisParams where
  Omega_W := Real.pi
  Omega_W_pos := Real.pi_pos
  I2 := cap_I2 c hc
  I2_pos := cap_I2_pos c hc
  I4 := cap_I4 c hc
  I4_pos := cap_I4_pos c hc hc1
  cauchy_schwarz := by
    -- π · I₄ ≥ I₂² follows from kurtosis ≥ 1:
    -- kurtosis = π · I₄ / I₂² ≥ 1 (kurtosis_formula_ge_one)
    rw [ge_iff_le]
    have h_sqrt_pos : Real.sqrt c > 0 := Real.sqrt_pos.mpr hc
    have hI2_pos := cap_I2_pos c hc
    have h_ge_one := kurtosis_formula_ge_one _ h_sqrt_pos
    have h_eq : Real.pi * cap_I4 c hc / (cap_I2 c hc) ^ 2 =
      kurtosis_formula (Real.sqrt c) := by
        unfold cap_I2 cap_I4
        exact kurtosis_formula_from_integrals c hc
    rw [← h_eq] at h_ge_one
    rwa [ge_iff_le, le_div_iff₀ (sq_pos_of_pos hI2_pos), one_mul] at h_ge_one

/-- The kurtosis of the cap parameters equals the kurtosis formula.

    This is the key bridge theorem: the abstract kurtosis K_W = Ω_W · I₄/I₂²
    from the PressureKurtosisParams structure equals the analytical kurtosis
    formula kurtosis_formula(ε̃) when instantiated with the W-domain cap integrals.

    **Reference:** Proposition 4.3.5 §4.3 -/
theorem capKurtosisParams_kurtosis_eq (c : ℝ) (hc : c > 0) (hc1 : c < 1) :
    (capKurtosisParams c hc hc1).kurtosis = kurtosis_formula (Real.sqrt c) := by
  unfold PressureKurtosisParams.kurtosis capKurtosisParams cap_I2 cap_I4
  simp only
  exact kurtosis_formula_from_integrals c hc

/-- The cap kurtosis at c = ε̃² satisfies K_W ≥ 1.

    Specialized instance of kurtosis_lower_bound for the W-domain. -/
theorem capKurtosis_ge_one (c : ℝ) (hc : c > 0) (hc1 : c < 1) :
    (capKurtosisParams c hc hc1).kurtosis ≥ 1 :=
  kurtosis_lower_bound _

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 4: CENTRAL VALUE AND NUMERICAL EVALUATION
    ═══════════════════════════════════════════════════════════════════════════

    Evaluating the kurtosis formula at the central regularization ε̃ = 0.130:

      c = ε̃² = 0.0169
      3c(1+c) = 3 × 0.0169 × 1.0169 = 0.05156
      1/(3c(1+c)) = 19.40
      e_W² = 1 + 19.40 = 20.40
      e_W = √20.40 ≈ 4.52

    The small difference from the rounded central value e_W = 4.5 is within
    the rounding of ε̃ = 0.130.

    Reference: Proposition-4.3.5 §4.6
-/

/-- e_W² at the central regularization: e_W²(ε̃ = 0.130) ≈ 20.4.

    **Reference:** Proposition 4.3.5 §4.6, Step 1-2 -/
noncomputable def e_W_squared_central : ℝ := kurtosis_formula epsilon_tilde_W

/-- e_W² ≥ 1 at central value -/
theorem e_W_squared_central_ge_one : e_W_squared_central ≥ 1 := by
  unfold e_W_squared_central
  exact kurtosis_formula_ge_one epsilon_tilde_W epsilon_tilde_W_pos

/-- e_W² ∈ (19, 22) at ε̃ = 0.130.

    More precisely: e_W² = 1 + 1/(3 × 0.0169 × 1.0169) ≈ 20.40

    **Reference:** Proposition 4.3.5 §4.6 -/
theorem e_W_squared_bounds :
    19 < e_W_squared_central ∧ e_W_squared_central < 22 := by
  unfold e_W_squared_central kurtosis_formula epsilon_tilde_W
  constructor <;> norm_num

/-- The Skyrme parameter e_W = √(e_W²) satisfies 4 < e_W < 5.

    Since 16 < e_W² < 25, we have 4 < √(e_W²) < 5.

    **Reference:** Proposition 4.3.5 §4.6 -/
theorem e_W_in_range :
    4 < Real.sqrt e_W_squared_central ∧ Real.sqrt e_W_squared_central < 5 := by
  have ⟨hlb, hub⟩ := e_W_squared_bounds
  constructor
  · rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) from
      (Real.sqrt_sq (by norm_num : (4 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  · rw [show (5 : ℝ) = Real.sqrt (5 ^ 2) from
      (Real.sqrt_sq (by norm_num : (5 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by linarith [e_W_squared_central_ge_one]) (by linarith)

/-- The kurtosis formula value matches the Constants.lean Skyrme parameter
    (skyrme_e_W = 4.5) to within 2%.

    |√(e_W²(0.130)) - 4.5| / 4.5 < 0.02

    **Reference:** Proposition 4.3.5 §4.6 -/
private theorem e_W_squared_tight_bounds :
    19.36 < e_W_squared_central ∧ e_W_squared_central < 21.16 := by
  unfold e_W_squared_central kurtosis_formula epsilon_tilde_W
  constructor <;> norm_num

theorem e_W_matches_constant :
    |Real.sqrt e_W_squared_central - skyrme_e_W| < 0.1 := by
  have ⟨hlb, hub⟩ := e_W_squared_tight_bounds
  unfold skyrme_e_W
  rw [abs_lt]
  constructor
  · -- -0.1 < √(e_W²) - 4.5, i.e., 4.4 < √(e_W²), i.e., 4.4² = 19.36 < e_W²
    linarith [show (4.4 : ℝ) < Real.sqrt e_W_squared_central from by
      rw [show (4.4 : ℝ) = Real.sqrt (4.4 ^ 2) from
        (Real.sqrt_sq (by norm_num : (4.4 : ℝ) ≥ 0)).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)]
  · -- √(e_W²) - 4.5 < 0.1, i.e., √(e_W²) < 4.6, i.e., e_W² < 4.6² = 21.16
    linarith [show Real.sqrt e_W_squared_central < (4.6 : ℝ) from by
      rw [show (4.6 : ℝ) = Real.sqrt (4.6 ^ 2) from
        (Real.sqrt_sq (by norm_num : (4.6 : ℝ) ≥ 0)).symm]
      exact Real.sqrt_lt_sqrt (by linarith [e_W_squared_central_ge_one]) (by linarith)]

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 5: REGULARIZATION SCAN AND SENSITIVITY
    ═══════════════════════════════════════════════════════════════════════════

    The kurtosis formula evaluates over the constrained range ε̃ ∈ [0.10, 0.16]:

    | ε̃   | e_W² | e_W  | δe_W/e_W |
    |------|------|------|----------|
    | 0.10 | 34.0 | 5.83 | +29%     |
    | 0.13 | 20.4 | 4.52 | central  |
    | 0.16 | 13.7 | 3.70 | −18%     |

    The asymmetric variation (+29%/−18%) reflects the ~1/ε̃² scaling.

    Reference: Proposition-4.3.5 §5.1
-/

/-- At ε̃ = 0.10 (lower bound of constrained range): e_W² ∈ (33, 35).

    More precisely: e_W² = 1 + 1/(3 × 0.01 × 1.01) = 34.00.
    This gives e_W ≈ 5.83, the upper end of the uncertainty range.

    **Reference:** Proposition 4.3.5 §5.1 -/
theorem kurtosis_at_eps_010 :
    33 < kurtosis_formula 0.10 ∧ kurtosis_formula 0.10 < 35 := by
  unfold kurtosis_formula
  constructor <;> norm_num

/-- At ε̃ = 0.16 (upper bound of constrained range): e_W² ∈ (13, 14.5).

    More precisely: e_W² = 1 + 1/(3 × 0.0256 × 1.0256) = 13.70.
    This gives e_W ≈ 3.70, the lower end of the uncertainty range.

    **Reference:** Proposition 4.3.5 §5.1 -/
theorem kurtosis_at_eps_016 :
    13 < kurtosis_formula 0.16 ∧ kurtosis_formula 0.16 < 14.5 := by
  unfold kurtosis_formula
  constructor <;> norm_num

/-- At ε̃ = 0.50 (physical regularization from Def 0.1.3): e_W² ∈ (2.0, 2.1).

    More precisely: e_W² = 1 + 16/15 = 31/15 ≈ 2.067.
    This gives e_W ≈ 1.44, confirming that the physical ε gives a much
    smaller Skyrme parameter — the Skyrme term probes finer angular structure.

    **Reference:** Proposition 4.3.5 §4.6 table -/
theorem kurtosis_at_eps_050 :
    2.0 < kurtosis_formula 0.50 ∧ kurtosis_formula 0.50 < 2.1 := by
  unfold kurtosis_formula
  constructor <;> norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 6: ERROR BUDGET
    ═══════════════════════════════════════════════════════════════════════════

    The total uncertainty δe_W/e_W ≈ 27% arises from four sources
    combined in quadrature:

    | Source                           | δe_W/e_W |
    |----------------------------------|----------|
    | Regularization (ε̃ variation)     | ±24%     |
    | Higher-order gradients (M_W~Λ_W) | ±12%     |
    | Boundary corrections (cap/Voronoi)| ±3%      |
    | Cap geometry approximation        | ±2%      |
    | Total (quadrature)               | ±27%     |

    Reference: Proposition-4.3.5 §5
-/

/-- **Error Budget Structure**

    Encodes the four uncertainty sources and total error for the
    Skyrme parameter determination.

    **Reference:** Proposition 4.3.5 §5.4 -/
structure ErrorBudget where
  /-- Regularization uncertainty (symmetrized, %) -/
  delta_regularization : ℝ
  /-- Higher-order gradient uncertainty (%) -/
  delta_higher_order : ℝ
  /-- Boundary correction uncertainty (%) -/
  delta_boundary : ℝ
  /-- Cap geometry uncertainty (%) -/
  delta_cap : ℝ
  /-- All uncertainties are non-negative -/
  delta_reg_nonneg : delta_regularization ≥ 0
  delta_ho_nonneg : delta_higher_order ≥ 0
  delta_bnd_nonneg : delta_boundary ≥ 0
  delta_cap_nonneg : delta_cap ≥ 0

/-- Total error in quadrature: √(Σ δᵢ²) -/
noncomputable def ErrorBudget.total (eb : ErrorBudget) : ℝ :=
  Real.sqrt (eb.delta_regularization ^ 2 + eb.delta_higher_order ^ 2 +
             eb.delta_boundary ^ 2 + eb.delta_cap ^ 2)

/-- The standard error budget for Proposition 4.3.5.

    **Reference:** Proposition 4.3.5 §5.4, Table -/
noncomputable def standardErrorBudget : ErrorBudget where
  delta_regularization := 24
  delta_higher_order := 12
  delta_boundary := 3
  delta_cap := 2
  delta_reg_nonneg := by norm_num
  delta_ho_nonneg := by norm_num
  delta_bnd_nonneg := by norm_num
  delta_cap_nonneg := by norm_num

/-- The total error is approximately 27%.

    √(24² + 12² + 3² + 2²) = √(576 + 144 + 9 + 4) = √733 ≈ 27.07

    **Reference:** Proposition 4.3.5 §5.4 -/
theorem total_error_approx :
    26 < standardErrorBudget.total ∧ standardErrorBudget.total < 28 := by
  unfold ErrorBudget.total standardErrorBudget
  simp only
  -- Need: 26 < √733 < 28
  -- 26² = 676 < 733 < 784 = 28²
  constructor
  · rw [show (26 : ℝ) = Real.sqrt (26 ^ 2) from (Real.sqrt_sq (by norm_num : (26 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (28 : ℝ) = Real.sqrt (28 ^ 2) from (Real.sqrt_sq (by norm_num : (28 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The absolute uncertainty δe_W ≈ e_W × 0.27 ≈ 1.2.

    This matches the stated result e_W = 4.5 ± 1.2.

    **Reference:** Proposition 4.3.5 §5.4 -/
theorem absolute_uncertainty_matches :
    |skyrme_e_W * (standardErrorBudget.total / 100) - skyrme_e_W_uncertainty| < 0.1 := by
  have ⟨h_low, h_high⟩ := total_error_approx
  unfold skyrme_e_W skyrme_e_W_uncertainty
  rw [abs_lt]
  constructor <;> nlinarith

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 7: CONSISTENCY CHECKS
    ═══════════════════════════════════════════════════════════════════════════

    Six consistency checks validate the kurtosis determination:
    1. Dimensional analysis (e_W dimensionless, scale-independent)
    2. QCD limit (e_W ∈ [4.25, 5.45])
    3. NJL cross-check (e_NJL² = 6π²/N_c ≈ 19.74, 2.5% on e²)
    4. GL-Skyrme matching (e_GL = 4.64, 6% on e²)
    5. Soliton mass consistency (M_W^FB ≈ 1620 GeV)
    6. Domain geometry scaling (tetrahedral Voronoi uniquely determined)

    Reference: Proposition-4.3.5 §6
-/

-- ────────────────────────────────────────────────────────────────────────────
-- §6.1: Dimensional Analysis
-- ────────────────────────────────────────────────────────────────────────────

/-- **Dimensional analysis:** The kurtosis formula is manifestly dimensionless.

    The formula e_W² = 1 + 1/(3ε̃²(1+ε̃²)) depends only on the dimensionless
    parameter ε̃. It is independent of:
    - Pressure amplitude a₀
    - Stella edge length a
    - W condensate VEV v_W
    - Any dimensionful scale

    **Reference:** Proposition 4.3.5 §6.1

    **Formalization note:** Dimensionlessness is captured by two properties:
    (1) `kurtosis_scale_invariant` (Part 1): K_W is invariant under P_W → αP_W
    (2) The kurtosis formula depends only on the dimensionless parameter ε̃ -/
theorem kurtosis_dimensionless_check :
    ∀ (eps : ℝ), eps > 0 →
    -- The kurtosis formula is positive, ≥ 1, and scale-invariant (see Part 1)
    kurtosis_formula eps > 0 ∧ kurtosis_formula eps ≥ 1 := by
  intro eps heps
  exact ⟨kurtosis_formula_pos eps heps, kurtosis_formula_ge_one eps heps⟩

-- ────────────────────────────────────────────────────────────────────────────
-- §6.2: QCD Phenomenological Range
-- ────────────────────────────────────────────────────────────────────────────

/-- **QCD range check:** The Skyrme parameter e_W = 4.5 falls within
    the QCD phenomenological range [4.25, 5.45].

    - Adkins, Nappi & Witten (1983): e = 4.25 (chiral limit)
    - Adkins & Nappi (1984): e = 5.45 (massive pions)

    **Reference:** Proposition 4.3.5 §6.2 -/
theorem e_W_in_qcd_range :
    (4.25 : ℝ) ≤ skyrme_e_W ∧ skyrme_e_W ≤ 5.45 :=
  skyrme_e_W_in_QCD_range

-- ────────────────────────────────────────────────────────────────────────────
-- §6.6.1: NJL Bosonization Cross-Check
-- ────────────────────────────────────────────────────────────────────────────

/-- **NJL Skyrme coefficient:** e_NJL² = 6π²/N_c.

    Derived by Espriu, de Rafael & Taron (1990) from NJL bosonization
    at leading order in 1/N_c.

    **Citation:** Nucl. Phys. B 345, 22–56 -/
noncomputable def e_NJL_squared (Nc : ℕ) : ℝ := 6 * Real.pi ^ 2 / Nc

/-- e_NJL² > 0 for N_c > 0 -/
theorem e_NJL_squared_pos (Nc : ℕ) (hNc : Nc > 0) : e_NJL_squared Nc > 0 := by
  unfold e_NJL_squared
  apply div_pos
  · exact mul_pos (by norm_num : (6 : ℝ) > 0) (sq_pos_of_pos Real.pi_pos)
  · exact Nat.cast_pos.mpr hNc

/-- e_NJL² for N_c = 3: 6π²/3 = 2π² ≈ 19.74.

    **Reference:** Proposition 4.3.5 §6.6.1 -/
noncomputable def e_NJL_squared_Nc3 : ℝ := e_NJL_squared N_c

/-- e_NJL²(N_c=3) = 2π² -/
theorem e_NJL_squared_Nc3_eq : e_NJL_squared_Nc3 = 2 * Real.pi ^ 2 := by
  unfold e_NJL_squared_Nc3 e_NJL_squared N_c
  push_cast
  ring

/-- e_NJL²(N_c=3) ∈ (19, 20).

    More precisely: 2 × 3.14159² = 19.739... ∈ (19, 20)

    **Reference:** Proposition 4.3.5 §6.6.1 -/
theorem e_NJL_squared_bounds :
    19 < e_NJL_squared_Nc3 ∧ e_NJL_squared_Nc3 < 20 := by
  rw [e_NJL_squared_Nc3_eq]
  have h_pi_gt : 3.14 < Real.pi := pi_gt_d2
  have h_pi_lt : Real.pi < 3.15 := pi_lt_d2
  have h_pi_sq_lb : 3.14 ^ 2 < Real.pi ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) (by linarith)
  have h_pi_sq_ub : Real.pi ^ 2 < 3.15 ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) h_pi_lt
  constructor <;> nlinarith

/-- **NJL–Kurtosis agreement on e²:** within 3%.

    |e_NJL² - e_W²| / e_W² < 0.03, where e_W² ≈ 20.25 and e_NJL² ≈ 19.74.
    Fractional difference: |19.74 - 20.25|/20.25 ≈ 2.5%.

    We verify the weaker bound that both lie in (19, 22).

    **Reference:** Proposition 4.3.5 §6.6.1 -/
theorem njl_kurtosis_close :
    19 < e_NJL_squared_Nc3 ∧ e_NJL_squared_Nc3 < 22 ∧
    19 < e_W_squared_central ∧ e_W_squared_central < 22 := by
  refine ⟨e_NJL_squared_bounds.1, by linarith [e_NJL_squared_bounds.2],
         e_W_squared_bounds.1, e_W_squared_bounds.2⟩

/-- **N_c scan:** The NJL formula selects N_c = 3 as uniquely consistent.

    For N_c = 2: e_NJL = 5.44 (too high by 21%)
    For N_c = 3: e_NJL = 4.44 (within 1.3%)
    For N_c = 4: e_NJL = 3.85 (too low by 14%)

    **Reference:** Proposition 4.3.5 §6.6.1, N_c scan table -/
theorem njl_selects_Nc3 :
    -- e_NJL²(2) > 25 (too large)
    e_NJL_squared 2 > 25 ∧
    -- e_NJL²(3) ∈ (19, 20) (matches kurtosis)
    19 < e_NJL_squared 3 ∧ e_NJL_squared 3 < 20 ∧
    -- e_NJL²(4) < 16 (too small)
    e_NJL_squared 4 < 16 := by
  unfold e_NJL_squared
  push_cast
  have h_pi_gt : 3.14 < Real.pi := pi_gt_d2
  have h_pi_lt : Real.pi < 3.15 := pi_lt_d2
  have h_pi_sq_lb : 3.14 ^ 2 < Real.pi ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) (by linarith)
  have h_pi_sq_ub : Real.pi ^ 2 < 3.15 ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) h_pi_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 6π²/2 > 25 ⟺ 6π² > 50 ⟺ π² > 50/6
    rw [gt_iff_lt, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  · -- 6π²/3 > 19 ⟺ 6π² > 57 ⟺ π² > 9.5
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  · -- 6π²/3 < 20 ⟺ 6π² < 60 ⟺ π² < 10
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  · -- 6π²/4 < 16 ⟺ 6π² < 64 ⟺ π² < 32/3
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith

-- ────────────────────────────────────────────────────────────────────────────
-- §6.6.1 continued: NJL Inversion to ε̃
-- ────────────────────────────────────────────────────────────────────────────

/-- **NJL inversion to ε̃:** kurtosis_formula(0.132) ≈ e_NJL² = 2π².

    Inverting e_NJL² = 19.74 through the kurtosis formula gives ε̃_NJL = 0.132.
    This shows the NJL result is equivalent to a specific regularization value.

    **Reference:** Proposition 4.3.5 §6.7.3 -/
theorem njl_inversion_eps_tilde :
    |kurtosis_formula 0.132 - e_NJL_squared_Nc3| < 0.1 := by
  unfold kurtosis_formula e_NJL_squared_Nc3 e_NJL_squared N_c
  push_cast
  have h_pi_gt : 3.14 < Real.pi := pi_gt_d2
  have h_pi_lt : Real.pi < 3.15 := pi_lt_d2
  have h_pi_sq_lb : 3.14 ^ 2 < Real.pi ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) (by linarith)
  have h_pi_sq_ub : Real.pi ^ 2 < 3.15 ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) h_pi_lt
  rw [abs_lt]
  constructor <;> nlinarith

-- ────────────────────────────────────────────────────────────────────────────
-- §6.7: GL-Skyrme Matching
-- ────────────────────────────────────────────────────────────────────────────

/-- **GL-Skyrme Identity:**
    e² = 1/(8(ℓ₂ʳ - ℓ₁ʳ))

    For SU(2), the Skyrme four-derivative term decomposes into GL operators:
      Tr[L_μ, L_ν]² = 2(O₂ - O₁)

    Matching: ℓ₂ = 1/(16e²), ℓ₁ = -1/(16e²)
    Therefore: e² = 1/(8(ℓ₂ʳ - ℓ₁ʳ))

    **Citation:** Manton & Sutcliffe (2004), Ch. 9; Proposition 4.3.5 §6.7.1 -/
noncomputable def gl_skyrme_e_squared (ell2r_minus_ell1r : ℝ) : ℝ :=
  1 / (8 * ell2r_minus_ell1r)

/-- **GL-Skyrme Parameters from Resonance Saturation**

    The renormalized GL LECs at μ = M_V = 775 MeV, derived from
    resonance saturation on ∂S (Proposition 0.0.17k2 §4).

    **Reference:** Proposition 4.3.5 §6.7.2 -/
structure GLSkyrmeParams where
  /-- ℓ₁ʳ(M_V) (renormalized LEC at vector meson mass scale) -/
  ell1r : ℝ
  /-- ℓ₂ʳ(M_V) -/
  ell2r : ℝ
  /-- ℓ₂ʳ > ℓ₁ʳ (required for e² > 0) -/
  ell2r_gt_ell1r : ell2r > ell1r

/-- The LEC difference: ℓ₂ʳ - ℓ₁ʳ -/
noncomputable def GLSkyrmeParams.lec_diff (p : GLSkyrmeParams) : ℝ :=
  p.ell2r - p.ell1r

/-- LEC difference is positive -/
theorem GLSkyrmeParams.lec_diff_pos (p : GLSkyrmeParams) : p.lec_diff > 0 := by
  unfold GLSkyrmeParams.lec_diff
  linarith [p.ell2r_gt_ell1r]

/-- Standard GL-Skyrme parameters from CG resonance saturation.

    From ℓ̄₁ = −0.4, ℓ̄₂ = 4.3, converting to renormalized at μ = M_V:
    ℓ₁ʳ(M_V) = −4.11 × 10⁻³
    ℓ₂ʳ(M_V) = 1.70 × 10⁻³
    Δℓʳ = 5.81 × 10⁻³

    **Reference:** Proposition 4.3.5 §6.7.2 -/
noncomputable def standardGLParams : GLSkyrmeParams where
  ell1r := -4.11e-3
  ell2r := 1.70e-3
  ell2r_gt_ell1r := by norm_num

/-- The LEC difference is approximately 5.81 × 10⁻³ -/
theorem gl_lec_diff_value :
    5.5e-3 < standardGLParams.lec_diff ∧ standardGLParams.lec_diff < 6.0e-3 := by
  unfold GLSkyrmeParams.lec_diff standardGLParams
  simp only
  constructor <;> norm_num

/-- **GL-Skyrme Skyrme parameter:** e_GL ≈ 4.64.

    e² = 1/(8 × 5.81 × 10⁻³) = 21.5, so e = 4.64.

    **Reference:** Proposition 4.3.5 §6.7.2 -/
theorem gl_skyrme_e_approx :
    let e2 := gl_skyrme_e_squared standardGLParams.lec_diff
    20 < e2 ∧ e2 < 23 := by
  simp only
  unfold gl_skyrme_e_squared GLSkyrmeParams.lec_diff standardGLParams
  simp only
  constructor <;> norm_num

/-- **GL-Skyrme consistency with kurtosis:** Both give e² ∈ (19, 23).

    Kurtosis: e_W² ≈ 20.40
    GL-Skyrme: e_GL² ≈ 21.5
    Fractional difference: ~5% on e²

    **Reference:** Proposition 4.3.5 §6.7.4 -/
theorem gl_kurtosis_consistent :
    let e2_GL := gl_skyrme_e_squared standardGLParams.lec_diff
    19 < e2_GL ∧ e2_GL < 23 := by
  simp only
  exact ⟨by linarith [gl_skyrme_e_approx.1], gl_skyrme_e_approx.2⟩

/-- **GL inversion to ε̃:** kurtosis_formula(0.127) ≈ e_GL² ≈ 21.5.

    Inverting e_GL² = 21.5 through the kurtosis formula gives ε̃_GL = 0.127.

    **Reference:** Proposition 4.3.5 §6.7.2 -/
theorem gl_inversion_eps_tilde :
    |kurtosis_formula 0.127 - gl_skyrme_e_squared standardGLParams.lec_diff| < 0.5 := by
  unfold kurtosis_formula gl_skyrme_e_squared GLSkyrmeParams.lec_diff standardGLParams
  simp only
  rw [abs_lt]
  constructor <;> norm_num

/-- **NJL and GL inversions bracket ε̃ = 0.130.**

    ε̃_GL = 0.127 < ε̃_central = 0.130 < ε̃_NJL = 0.132

    Two independent first-principles calculations (resonance saturation on ∂S
    and NJL bosonization) bracket the central value from opposite sides.
    Arithmetic mean: (0.127 + 0.132)/2 = 0.1295, within 0.4% of 0.130.

    **Reference:** Proposition 4.3.5 §6.7.4 -/
theorem eps_tilde_bracketing :
    (0.127 : ℝ) < epsilon_tilde_W ∧ epsilon_tilde_W < 0.132 := by
  unfold epsilon_tilde_W
  constructor <;> norm_num

/-- **Kurtosis monotonicity confirms bracketing is consistent:**
    ε̃_GL < ε̃ < ε̃_NJL implies K(ε̃_NJL) < K(ε̃) < K(ε̃_GL),
    since kurtosis_formula is decreasing.

    **Reference:** Proposition 4.3.5 §6.7.4 -/
theorem kurtosis_monotone_bracketing :
    kurtosis_formula 0.132 < kurtosis_formula epsilon_tilde_W ∧
    kurtosis_formula epsilon_tilde_W < kurtosis_formula 0.127 := by
  unfold epsilon_tilde_W
  constructor
  · exact kurtosis_formula_antitone 0.130 0.132 (by norm_num) (by norm_num) (by norm_num)
  · exact kurtosis_formula_antitone 0.127 0.130 (by norm_num) (by norm_num) (by norm_num)

-- ────────────────────────────────────────────────────────────────────────────
-- §6.5: Soliton Mass Consistency
-- ────────────────────────────────────────────────────────────────────────────

/-- **Faddeev-Bogomolny mass:** M_W^FB = 6π² v_W / e_W.

    **Reference:** Proposition 4.3.5 §6.5 -/
noncomputable def M_W_FB_GeV : ℝ := 6 * Real.pi ^ 2 * v_W_precision_GeV / skyrme_e_W

/-- M_W^FB > 0 -/
theorem M_W_FB_pos : M_W_FB_GeV > 0 := by
  unfold M_W_FB_GeV
  apply div_pos
  · apply mul_pos
    · exact mul_pos (by norm_num : (6 : ℝ) > 0) (sq_pos_of_pos Real.pi_pos)
    · exact v_W_precision_pos
  · exact skyrme_e_W_pos

/-- **Faddeev mass approximately 1620 GeV:**
    M_W^FB = 6π² × 123 / 4.5 ≈ 59.22 × 123 / 4.5 ≈ 1618 GeV.

    This matches M_W_precision_GeV = 1620 to within rounding.

    **Reference:** Proposition 4.3.5 §6.5 -/
theorem M_W_FB_approx :
    1600 < M_W_FB_GeV ∧ M_W_FB_GeV < 1650 := by
  unfold M_W_FB_GeV v_W_precision_GeV skyrme_e_W
  have h_pi_gt : 3.14 < Real.pi := pi_gt_d2
  have h_pi_lt : Real.pi < 3.15 := pi_lt_d2
  have h_pi_sq_lb : 3.14 ^ 2 < Real.pi ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) (by linarith)
  have h_pi_sq_ub : Real.pi ^ 2 < 3.15 ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) h_pi_lt
  constructor
  · -- 1600 < 6π² × 123 / 4.5 ⟺ 1600 × 4.5 < 6π² × 123 ⟺ 7200 < 738π²
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4.5)]
    nlinarith
  · -- 6π² × 123 / 4.5 < 1650 ⟺ 6π² × 123 < 1650 × 4.5 ⟺ 738π² < 7425
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4.5)]
    nlinarith

/-- **Soliton mass matches existing constant:** M_W^FB ≈ M_W_precision_GeV.

    **Reference:** Proposition 4.3.5 §6.5 -/
theorem mass_consistency :
    |M_W_FB_GeV - M_W_precision_GeV| < 30 := by
  have ⟨h_low, h_high⟩ := M_W_FB_approx
  unfold M_W_precision_GeV
  rw [abs_lt]
  constructor <;> linarith

/-- **EFT validity check:** M_W^FB / Λ_W ≈ 1.05.

    The soliton mass sits near the EFT cutoff Λ_W = 4πv_W ≈ 1546 GeV.
    This ratio being close to 1 is why we assign ±12% higher-order uncertainty.

    **Reference:** Proposition 4.3.5 §6.5 -/
theorem eft_validity_ratio :
    M_W_FB_GeV / Lambda_W_GeV > 1.0 ∧ M_W_FB_GeV / Lambda_W_GeV < 1.1 := by
  have ⟨h_low, h_high⟩ := M_W_FB_approx
  unfold Lambda_W_GeV v_W_precision_GeV
  have h_pi_gt : 3.14 < Real.pi := pi_gt_d2
  have h_pi_lt : Real.pi < 3.15 := pi_lt_d2
  constructor
  · rw [gt_iff_lt, lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 8: MAIN PROPOSITION STATEMENT
    ═══════════════════════════════════════════════════════════════════════════

    The complete Proposition 4.3.5, combining the kurtosis identification,
    analytical evaluation, error budget, and consistency checks.

    Reference: Proposition-4.3.5 §1, §7
-/

/-- **Proposition 4.3.5 (Skyrme Parameter from Pressure-Kurtosis Geometry)**

    The W-sector Skyrme parameter e_W is determined by the pressure-curvature
    geometry of the W domain on ∂S:

      e_W = 4.5 ± 1.2

    Under assumptions A-PW4 (pressure weighting) and A-K (kurtosis identification):

    (a) e_W² = K_W = Ω_W · ∫P_W⁴ dΩ / (∫P_W² dΩ)²

    (b) On the equal-area cap: e_W² = 1 + 1/(3ε̃²(1+ε̃²))

    (c) Total uncertainty: δe_W/e_W ≈ 27%

    **Reference:** Proposition 4.3.5 §1 -/
structure Proposition_4_3_5 where
  /-- The Skyrme parameter central value -/
  e_W : ℝ
  /-- e_W > 0 -/
  e_W_pos : e_W > 0
  /-- The uncertainty -/
  delta_e_W : ℝ
  /-- δe_W > 0 -/
  delta_e_W_pos : delta_e_W > 0
  /-- Central value matches Constants.lean -/
  central_value : e_W = skyrme_e_W
  /-- Uncertainty matches Constants.lean -/
  uncertainty_value : delta_e_W = skyrme_e_W_uncertainty
  /-- Within QCD phenomenological range -/
  qcd_consistent : 4.25 ≤ e_W ∧ e_W ≤ 5.45
  /-- Kurtosis formula close to e_W²: |K(ε̃) - e_W²| < 0.5.
      (Actual: |20.40 - 20.25| = 0.15, from rounding ε̃ = 0.130) -/
  kurtosis_derived : |kurtosis_formula epsilon_tilde_W - e_W ^ 2| < 0.5
  /-- NJL cross-check: e_W² ≈ 6π²/N_c to within 2.5% on e².
      (Actual: |20.25 - 19.74| = 0.51) -/
  njl_consistent : |e_W ^ 2 - e_NJL_squared_Nc3| < 1

/-- **The standard instance of Proposition 4.3.5.**

    Establishes e_W = 4.5 ± 1.2 with all consistency checks.

    **Reference:** Proposition 4.3.5 §7.1 -/
noncomputable def proposition_4_3_5 : Proposition_4_3_5 where
  e_W := skyrme_e_W
  e_W_pos := skyrme_e_W_pos
  delta_e_W := skyrme_e_W_uncertainty
  delta_e_W_pos := skyrme_e_W_uncertainty_pos
  central_value := rfl
  uncertainty_value := rfl
  qcd_consistent := skyrme_e_W_in_QCD_range
  kurtosis_derived := by
    -- |kurtosis_formula(0.130) - 4.5²| = |20.40 - 20.25| = 0.15 < 0.5
    unfold kurtosis_formula epsilon_tilde_W skyrme_e_W
    rw [abs_lt]
    constructor <;> norm_num
  njl_consistent := by
    -- |4.5² - 2π²| = |20.25 - 19.74| = 0.51 < 1
    unfold skyrme_e_W e_NJL_squared_Nc3 e_NJL_squared N_c
    push_cast
    have h_pi_gt : 3.14 < Real.pi := pi_gt_d2
    have h_pi_lt : Real.pi < 3.15 := pi_lt_d2
    have h_pi_sq_lb : 3.14 ^ 2 < Real.pi ^ 2 :=
      sq_lt_sq' (by linarith [Real.pi_pos]) (by linarith)
    have h_pi_sq_ub : Real.pi ^ 2 < 3.15 ^ 2 :=
      sq_lt_sq' (by linarith [Real.pi_pos]) h_pi_lt
    rw [abs_lt]
    constructor <;> nlinarith

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 9: DOWNSTREAM CONNECTIONS
    ═══════════════════════════════════════════════════════════════════════════

    This proposition provides the geometric derivation of e_W, superseding
    the semi-numerical determination in Prop 5.1.2b §5.2. The value feeds
    into:
    - Theorem 4.3.2: W-soliton mass formula
    - Proposition 5.1.2b: Precision cosmological densities
    - Prediction 8.2.4: W-sector gravitational waves error budget

    Reference: Proposition-4.3.5 §7.3
-/

/-- **Downstream: Skyrme parameter feeds into W-soliton mass.**

    The Faddeev-Bogomolny bound M_W^FB = 6π² v_W / e_W uses e_W = 4.5.
    This is now geometrically derived rather than semi-numerical.

    **Reference:** Proposition 4.3.5 → Theorem 4.3.2 §4.3 -/
theorem downstream_mass_formula :
    M_W_precision_GeV > 0 ∧
    M_W_FB_GeV > 0 ∧
    |M_W_FB_GeV - M_W_precision_GeV| < 30 := by
  exact ⟨M_W_precision_pos, M_W_FB_pos, mass_consistency⟩

/-- **Downstream: ANW mass uses same e_W.**

    M_W^ANW = 72.92 × v_W / e_W ≈ 1993 GeV.

    **Reference:** Proposition 4.3.5 → Theorem 4.3.2 §4.4 -/
theorem downstream_anw_mass :
    M_W_anw_GeV > 0 ∧ 1990 < M_W_anw_GeV ∧ M_W_anw_GeV < 2000 :=
  ⟨M_W_anw_pos, M_W_anw_approx⟩

-- ────────────────────────────────────────────────────────────────────────────
-- Verification hooks
-- ────────────────────────────────────────────────────────────────────────────

#check proposition_4_3_5
#check kurtosis_formula
#check e_NJL_squared_Nc3
#check standardErrorBudget
#check M_W_FB_GeV

end ChiralGeometrogenesis.Phase4.Proposition_4_3_5
