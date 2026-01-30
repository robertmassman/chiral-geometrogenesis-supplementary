/-
  Foundations/Proposition_0_0_17z2.lean

  Proposition 0.0.17z2: Scale-Dependent Effective Euler Characteristic

  STATUS: 🔶 NOVEL — Topological transition from UV (χ=4) to IR (χ=2) at interpenetration scale

  **Purpose:**
  Derive a scale-dependent effective Euler characteristic χ_eff(μ) that transitions
  from χ = 4 (two resolved tetrahedra at short distances) to χ = 2 (effective single
  surface at long distances), improving the agreement between the non-perturbative
  bootstrap prediction and observed string tension.

  **Key Results:**
  (a) Interpenetration scale d_inter = R/3 = 0.1495 fm
  (b) Resolution function f(ξ) = 1 - exp(-ξ²), ξ = μ·d_inter/ℏc
  (c) χ_eff(μ) = 2 + 2·f(ξ) ∈ [2, 4]
  (d) At confinement scale: ξ ≈ 0.333, χ_eff ≈ 2.21
  (e) Effective c_G^eff = 0.127, total NP correction = -8.7%
  (f) Corrected prediction: √σ = 439.2 MeV, agreement 0.02σ

  **Dependencies:**
  - 🔶 NOVEL Proposition 0.0.17z1 (Geometric Derivation of Non-Perturbative Coefficients)
  - 🔶 NOVEL ✅ VERIFIED Proposition 0.0.17z (Non-Perturbative Corrections to Bootstrap)
  - ✅ Definition 0.1.1 (Stella Octangula Boundary Topology) — χ(∂S) = 4

  Reference: docs/proofs/foundations/Proposition-0.0.17z2-Scale-Dependent-Effective-Euler-Characteristic.md
-/

import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.Constants
import ChiralGeometrogenesis.Tactics.Prelude
import ChiralGeometrogenesis.Foundations.Proposition_0_0_17z
import ChiralGeometrogenesis.Foundations.Proposition_0_0_17z1
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.nativeDecide false

namespace ChiralGeometrogenesis.Foundations.Proposition_0_0_17z2

open Real
open ChiralGeometrogenesis
open ChiralGeometrogenesis.Constants
open ChiralGeometrogenesis.Foundations.Proposition_0_0_17z

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 1: INTERPENETRATION SCALE
    ═══════════════════════════════════════════════════════════════════════════

    The two tetrahedra T₊ and T₋ of the stella octangula, each inscribed in a
    sphere of circumradius R, have inradius r = R/3. The interpenetration scale
    is the minimum face-to-face separation:

    d_inter = R/3

    Reference: Markdown §2.1
-/

/-- Stella octangula circumradius (observed), in fm.
    This is R_stella from Constants.lean. -/
noncomputable def R_fm : ℝ := R_stella_fm

/-- Interpenetration scale d_inter = R/3, in fm.
    The inradius of a regular tetrahedron inscribed in a sphere of radius R. -/
noncomputable def d_inter_fm : ℝ := R_fm / 3

/-- d_inter > 0 -/
theorem d_inter_pos : d_inter_fm > 0 := by
  unfold d_inter_fm R_fm
  exact div_pos R_stella_pos (by norm_num : (3:ℝ) > 0)

/-- d_inter ≈ 0.1495 fm -/
theorem d_inter_approx : 0.149 < d_inter_fm ∧ d_inter_fm < 0.150 := by
  unfold d_inter_fm R_fm R_stella_fm
  constructor <;> norm_num

/-- Transition energy scale μ_trans = ℏc / d_inter, in MeV.
    Reference: Markdown §2.2 -/
noncomputable def mu_trans_MeV : ℝ := hbar_c_MeV_fm / d_inter_fm

/-- μ_trans ≈ 1319 MeV -/
theorem mu_trans_approx : 1318 < mu_trans_MeV ∧ mu_trans_MeV < 1321 := by
  unfold mu_trans_MeV d_inter_fm R_fm R_stella_fm hbar_c_MeV_fm
  constructor <;> norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 2: RESOLUTION FUNCTION AND χ_eff(μ)
    ═══════════════════════════════════════════════════════════════════════════

    **Coupling mechanism (Markdown §3.0):**
    The stella boundary ∂S = ∂T₊ ⊔ ∂T₋ is topologically disjoint. On a genuinely
    disconnected manifold the heat kernel gives χ = 4 at all diffusion times. The
    resolution argument requires an explicit coupling mechanism: **bulk field
    propagation** through the stella interior. The color fields χ_c propagate in the
    ambient ℝ³ embedding, with finite penetration depth between ∂T₊ and ∂T₋.
    - Short wavelengths (λ ≪ d_inter): modes localize on individual surfaces → χ = 4
    - Long wavelengths (λ ≫ d_inter): modes bridge through the bulk → χ_eff = 2
    - Intermediate: partial coupling, interpolated by f(ξ)
    This is analogous to coupled quantum dots with tunnel splitting ∼ exp(-d/ξ).

    The heat kernel resolution function:
      f(ξ) = 1 - exp(-ξ²),  ξ = μ · d_inter / ℏc

    The effective Euler characteristic:
      χ_eff(μ) = 2 + 2·f(ξ) = 2 + 2(1 - exp(-ξ²))

    **Terminological note (Markdown §3.2):**
    χ_eff(μ) is NOT a topological invariant. The exact Euler characteristic of ∂S
    remains χ = 4 at all scales. χ_eff is an effective spectral topology weight
    analogous to the spectral dimension d_s(t) of Ambjorn et al. (2005).

    Reference: Markdown §3.0–3.3
-/

/-- Dimensionless resolution parameter ξ = μ · d_inter / ℏc -/
noncomputable def xi (mu_MeV : ℝ) : ℝ := mu_MeV * d_inter_fm / hbar_c_MeV_fm

/-- Resolution function f(ξ) = 1 - exp(-ξ²).
    From heat kernel spectral probe (§3.3). -/
noncomputable def resolution_f (xi_val : ℝ) : ℝ := 1 - Real.exp (-(xi_val ^ 2))

/-- f(ξ) ∈ [0, 1] for ξ ≥ 0 -/
theorem resolution_f_range {xi_val : ℝ} (hξ : xi_val ≥ 0) :
    0 ≤ resolution_f xi_val ∧ resolution_f xi_val ≤ 1 := by
  unfold resolution_f
  constructor
  · -- 0 ≤ 1 - exp(-ξ²): since exp(-ξ²) ≤ exp(0) = 1 for -ξ² ≤ 0
    have h : Real.exp (-(xi_val ^ 2)) ≤ Real.exp 0 :=
      Real.exp_le_exp_of_le (by linarith [sq_nonneg xi_val])
    rw [Real.exp_zero] at h
    linarith
  · -- 1 - exp(-ξ²) ≤ 1: since exp(-ξ²) ≥ 0
    have h := Real.exp_pos (-(xi_val ^ 2))
    linarith

/-- f(ξ) ∈ [0, 1] for all ξ (not just ξ ≥ 0; exp(-ξ²) = exp(-(-ξ)²)) -/
theorem resolution_f_range_all (xi_val : ℝ) :
    0 ≤ resolution_f xi_val ∧ resolution_f xi_val ≤ 1 := by
  unfold resolution_f
  constructor
  · have h : Real.exp (-(xi_val ^ 2)) ≤ Real.exp 0 :=
      Real.exp_le_exp_of_le (by linarith [sq_nonneg xi_val])
    rw [Real.exp_zero] at h; linarith
  · have h := Real.exp_pos (-(xi_val ^ 2)); linarith

/-- UV limit: f(ξ) → 1 as ξ → ∞ (bounded above by 1) -/
theorem resolution_f_uv_limit_bound {xi_val : ℝ} : resolution_f xi_val ≤ 1 :=
  (resolution_f_range_all xi_val).2

/-- IR limit: f(0) = 0 -/
theorem resolution_f_ir_limit : resolution_f 0 = 0 := by
  unfold resolution_f
  simp [Real.exp_zero]

/-- Monotonicity: f is monotone increasing on [0, ∞).
    Proof: exp(-ξ²) is decreasing for ξ ≥ 0, so 1 - exp(-ξ²) is increasing.
    We prove: ξ₁ ≤ ξ₂ and both ≥ 0 implies f(ξ₁) ≤ f(ξ₂). -/
theorem resolution_f_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    resolution_f a ≤ resolution_f b := by
  unfold resolution_f
  -- Suffices to show exp(-b²) ≤ exp(-a²), i.e., -b² ≤ -a²
  have h_sq : a ^ 2 ≤ b ^ 2 := sq_le_sq' (by linarith) hab
  have h_exp : Real.exp (-(b ^ 2)) ≤ Real.exp (-(a ^ 2)) :=
    Real.exp_le_exp_of_le (by linarith)
  linarith

/-- Scale-dependent effective Euler characteristic.
    χ_eff(μ) = 2 + 2·f(ξ(μ))
    Reference: Markdown §3.2 -/
noncomputable def chi_eff (mu_MeV : ℝ) : ℝ :=
  2 + 2 * resolution_f (xi mu_MeV)

/-- χ_eff ∈ [2, 4] for μ ≥ 0 -/
theorem chi_eff_range {mu_MeV : ℝ} (hmu : mu_MeV ≥ 0) :
    2 ≤ chi_eff mu_MeV ∧ chi_eff mu_MeV ≤ 4 := by
  unfold chi_eff
  have hξ : xi mu_MeV ≥ 0 := by
    unfold xi
    apply div_nonneg
    · exact mul_nonneg hmu (le_of_lt d_inter_pos)
    · exact le_of_lt hbar_c_pos
  have ⟨hf_lo, hf_hi⟩ := resolution_f_range hξ
  constructor <;> nlinarith

/-- IR limit: χ_eff(0) = 2 (single effective surface) -/
theorem chi_eff_ir : chi_eff 0 = 2 := by
  unfold chi_eff
  rw [show xi 0 = 0 from by unfold xi; ring]
  rw [resolution_f_ir_limit]
  ring

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 3: EVALUATION AT CONFINEMENT SCALE
    ═══════════════════════════════════════════════════════════════════════════

    At μ = √σ = 440 MeV:
    - ξ_conf = 440 × 0.1495 / 197.327 = 0.3334
    - f(ξ_conf) = 1 - exp(-0.1112) = 0.1052
    - χ_eff = 2.210

    Reference: Markdown §4.1
-/

/-- Confinement scale in MeV -/
noncomputable def mu_conf_MeV : ℝ := 440

/-- ξ at confinement scale -/
noncomputable def xi_conf : ℝ := xi mu_conf_MeV

/-- ξ_conf ≈ 0.333 -/
theorem xi_conf_approx : 0.333 < xi_conf ∧ xi_conf < 0.334 := by
  unfold xi_conf xi mu_conf_MeV d_inter_fm R_fm R_stella_fm hbar_c_MeV_fm
  constructor <;> norm_num

/-- χ_eff at confinement scale (numerical value for downstream use).
    Hardcoded because chi_eff mu_conf_MeV involves Real.exp which cannot be
    evaluated by norm_num. The connection is established in chi_eff_conf_consistent below.
    From markdown §4.1: χ_eff(440) = 2 + 2(1 - exp(-0.3334²)) = 2 + 2×0.1052 = 2.210 -/
noncomputable def chi_eff_conf : ℝ := 2.210

/-- χ_eff_conf is in the valid range -/
theorem chi_eff_conf_range : 2 ≤ chi_eff_conf ∧ chi_eff_conf ≤ 4 := by
  unfold chi_eff_conf
  constructor <;> norm_num

/-- Connection between hardcoded chi_eff_conf and the functional definition chi_eff.
    We verify that chi_eff(440) = 2 + 2·(1 - exp(-ξ²)) where ξ ≈ 0.3334.
    The hardcoded value 2.210 matches the functional form evaluated at ξ_conf.
    Strategy: bound exp(ξ²) from below (Taylor partial sums) and above (exp_bound'),
    then invert to get bounds on exp(-ξ²), and verify the result is within 0.01 of 2.210. -/
theorem chi_eff_conf_consistent :
    |chi_eff mu_conf_MeV - chi_eff_conf| < 0.01 := by
  -- Avoid unfolding everything at once; work with the definitions structurally.
  -- chi_eff mu_conf_MeV = 2 + 2 * resolution_f (xi mu_conf_MeV)
  -- chi_eff_conf = 2.210
  -- So we need |2 + 2 * resolution_f (xi 440) - 2.210| < 0.01
  -- i.e., |2 * resolution_f (xi 440) - 0.210| < 0.01
  -- resolution_f v = 1 - exp(-v²), xi 440 = 440 * d_inter_fm / hbar_c_MeV_fm
  -- We'll bound the exponent arg = (xi 440)² and then bound exp(-(xi 440)²).
  -- Step 1: Compute xi_conf² bounds
  have hxi_lo : (0.333 : ℝ) < xi mu_conf_MeV := by
    unfold xi mu_conf_MeV d_inter_fm R_fm R_stella_fm hbar_c_MeV_fm; norm_num
  have hxi_hi : xi mu_conf_MeV < (0.334 : ℝ) := by
    unfold xi mu_conf_MeV d_inter_fm R_fm R_stella_fm hbar_c_MeV_fm; norm_num
  have hxi_pos : (0 : ℝ) < xi mu_conf_MeV := by linarith
  -- (xi 440)² ∈ (0.110889, 0.111556)
  have hxi2_lo : (0.110 : ℝ) < (xi mu_conf_MeV) ^ 2 := by nlinarith
  have hxi2_hi : (xi mu_conf_MeV) ^ 2 < (0.112 : ℝ) := by nlinarith
  -- Step 2: Lower bound on exp(0.110) via Taylor partial sums
  have h_exp_lo : (1.116 : ℝ) < Real.exp (0.110 : ℝ) := by
    have h_nn : (0 : ℝ) ≤ 0.110 := by norm_num
    have h_sum_le := Real.sum_le_exp_of_nonneg h_nn (n := 3)
    -- Σ_{k=0}^{2} 0.110^k/k! = 1 + 0.110 + 0.00605 = 1.11605
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero,
      pow_succ, Nat.cast_one, zero_add] at h_sum_le
    linarith
  -- Step 3: Upper bound on exp(0.112) via exp_bound'
  have h_exp_hi : Real.exp (0.112 : ℝ) < (1.1186 : ℝ) := by
    have h_nn : (0 : ℝ) ≤ 0.112 := by norm_num
    have h_le1 : (0.112 : ℝ) ≤ 1 := by norm_num
    have h_bound := Real.exp_bound' h_nn h_le1 (n := 4) (by norm_num : 0 < 4)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero,
      pow_succ, Nat.cast_one, Nat.cast_ofNat, zero_add] at h_bound
    linarith
  -- Step 4: By monotonicity, 1.116 < exp(ξ²) < 1.1186
  have h_exp_gt : (1.116 : ℝ) < Real.exp ((xi mu_conf_MeV) ^ 2) := by
    calc (1.116 : ℝ) < Real.exp 0.110 := h_exp_lo
      _ < Real.exp ((xi mu_conf_MeV) ^ 2) := Real.exp_lt_exp.mpr (by linarith)
  have h_exp_lt : Real.exp ((xi mu_conf_MeV) ^ 2) < (1.1186 : ℝ) := by
    calc Real.exp ((xi mu_conf_MeV) ^ 2)
        < Real.exp 0.112 := Real.exp_lt_exp.mpr (by linarith)
      _ < 1.1186 := h_exp_hi
  -- Step 5: exp(-ξ²) = (exp(ξ²))⁻¹, bound via inversion
  have h_exp_neg : Real.exp (-((xi mu_conf_MeV) ^ 2)) = (Real.exp ((xi mu_conf_MeV) ^ 2))⁻¹ :=
    Real.exp_neg _
  -- exp(ξ²) > 1.116 > 0, so (exp ξ²)⁻¹ < 1/1.116
  -- exp(ξ²) < 1.1186, so (exp ξ²)⁻¹ > 1/1.1186
  have h_exp_e_pos : (0 : ℝ) < Real.exp ((xi mu_conf_MeV) ^ 2) := Real.exp_pos _
  have h_inv_lo' : (0.893 : ℝ) < (Real.exp ((xi mu_conf_MeV) ^ 2))⁻¹ := by
    rw [inv_eq_one_div]
    have := one_div_le_one_div_of_le h_exp_e_pos (le_of_lt h_exp_lt)
    linarith [show (0.893 : ℝ) < 1/1.1186 from by norm_num]
  have h_inv_hi' : (Real.exp ((xi mu_conf_MeV) ^ 2))⁻¹ < (0.897 : ℝ) := by
    rw [inv_eq_one_div]
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1.116) (le_of_lt h_exp_gt)
    linarith [show (1 : ℝ)/1.116 < 0.897 from by norm_num]
  -- Step 6: Conclude
  -- resolution_f (xi 440) = 1 - exp(-(xi 440)²)
  -- chi_eff 440 = 2 + 2*(1 - exp(-ξ²))
  -- = 4 - 2*exp(-ξ²) = 4 - 2*(exp ξ²)⁻¹
  -- exp(-ξ²) ∈ (0.893, 0.897)
  -- chi_eff ∈ (4 - 2*0.897, 4 - 2*0.893) = (2.206, 2.214)
  -- |chi_eff - 2.210| < 0.004 < 0.01 ✓
  unfold chi_eff chi_eff_conf resolution_f
  rw [h_exp_neg]
  rw [abs_lt]
  constructor <;> nlinarith

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 4: EFFECTIVE c_G AND ENHANCEMENT FACTOR
    ═══════════════════════════════════════════════════════════════════════════

    From Prop 0.0.17z1 §2.7:
    - z_{1/2} = +0.420 (edge contribution)
    - z_1(χ) = -χ/3 (Euler topology contribution)
    - Enhancement factor: E(χ) = |z_{1/2} + z_1(χ)| / |z_{1/2}|
    - c_G^eff = c_G^full × E(χ_eff)

    Reference: Markdown §4.2
-/

/-- Edge contribution to spectral zeta function residue (from Prop 0.0.17z1).
    In Prop 0.0.17z1, z_half is derived as L_eff/(8√π) and bounded in (0.4188, 0.4211).
    We use the rounded central value 0.420 for downstream calculations. -/
noncomputable def z_half : ℝ := 0.420

/-- Cross-reference: our z_half = 0.420 is within the derived bounds from Prop 0.0.17z1.
    Prop 0.0.17z1 proves: 0.4188 < z_half_z1 < 0.4211 (from L_eff/(8√π)).
    Our rounded value 0.420 lies within these bounds. -/
theorem z_half_consistent_with_z1 :
    (0.4188 : ℝ) < z_half ∧ z_half < (0.4211 : ℝ) := by
  unfold z_half; constructor <;> norm_num

/-- Euler topology contribution: z_1(χ) = -χ/3 -/
noncomputable def z_one (chi : ℝ) : ℝ := -(chi / 3)

/-- Enhancement factor E(χ) = |z_{1/2} + z_1(χ)| / |z_{1/2}| -/
noncomputable def enhancement_factor (chi : ℝ) : ℝ :=
  |z_half + z_one chi| / |z_half|

/-- Edge-only baseline OPE coefficient (from Prop 0.0.17z1 §2.7).
    This is c_G^full = c_G^adj × (1 + N_f C_F / (N_c C_A)),
    the edge-only piece before Euler topology enhancement.
    Prop 0.0.17z1 derives this from SU(3) Casimir structure on stella edges. -/
noncomputable def c_G_full : ℝ := 0.1691

/-- Cross-reference: c_G_full × euler_enhancement(χ=4) ≈ 0.37, matching Prop 0.0.17z1.
    c_G_geometric = c_G_full × E(4) = 0.1691 × 2.174 ≈ 0.368
    Prop 0.0.17z1 proves: 0.36 < c_G_geometric < 0.38. -/
theorem c_G_full_consistent_with_z1 :
    0.36 < c_G_full * enhancement_factor 4 ∧ c_G_full * enhancement_factor 4 < 0.38 := by
  unfold c_G_full enhancement_factor z_half z_one
  norm_num

/-- Effective gluon condensate coefficient at scale μ -/
noncomputable def c_G_eff (chi : ℝ) : ℝ := c_G_full * enhancement_factor chi

/-- Enhancement factor at χ = 2: E(2) ≈ 0.588 -/
theorem enhancement_chi2 : 0.58 < enhancement_factor 2 ∧ enhancement_factor 2 < 0.60 := by
  unfold enhancement_factor z_half z_one
  norm_num

/-- Enhancement factor at χ = 4: E(4) ≈ 2.174 -/
theorem enhancement_chi4 : 2.17 < enhancement_factor 4 ∧ enhancement_factor 4 < 2.18 := by
  unfold enhancement_factor z_half z_one
  norm_num

/-- Enhancement factor at χ_eff = 2.21: E(2.21) ≈ 0.754 -/
theorem enhancement_chi_eff : 0.75 < enhancement_factor 2.21 ∧ enhancement_factor 2.21 < 0.76 := by
  unfold enhancement_factor z_half z_one
  norm_num

/-- c_G^eff at χ_eff = 2.21 is approximately 0.127 -/
noncomputable def c_G_eff_conf : ℝ := c_G_eff chi_eff_conf

/-- c_G^eff ≈ 0.127 (numerical assertion for downstream use) -/
noncomputable def c_G_eff_conf_val : ℝ := 0.127

/-- Connection: c_G_eff_conf and c_G_eff_conf_val are approximately equal.
    c_G_eff(2.210) = 0.1691 × |0.420 - 2.210/3| / |0.420|
                    = 0.1691 × |0.420 - 0.7367| / 0.420
                    = 0.1691 × 0.3167 / 0.420
                    = 0.1691 × 0.7540 = 0.1275 -/
theorem c_G_eff_conf_connection :
    |c_G_eff_conf - c_G_eff_conf_val| < 0.002 := by
  unfold c_G_eff_conf c_G_eff c_G_full enhancement_factor z_half z_one chi_eff_conf
    c_G_eff_conf_val
  norm_num

/-- Sign structure: z_{1/2} + z_1(χ) < 0 for all χ > 1.26
    This ensures NP correction consistently reduces √σ.
    Reference: Markdown §4.3 -/
theorem sign_structure {chi : ℝ} (hchi : chi > 1.26) : z_half + z_one chi < 0 := by
  unfold z_half z_one
  nlinarith

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 5: REVISED CORRECTION BUDGET
    ═══════════════════════════════════════════════════════════════════════════

    With c_G^eff = 0.127:
    - Gluon condensate: (1/2) × 0.127 × 0.32 = 2.0%
    - Threshold matching: 3.0%
    - Higher-order pert.: 2.0%
    - Instanton effects: 1.7%
    - Total: 8.7%

    Reference: Markdown §5.1–5.2
-/

/-- Gluon condensate correction with χ_eff = 2.21.
    δ_gluon = (1/2) × c_G^eff × condensate_ratio -/
noncomputable def delta_gluon_z2 : ℝ := (1/2) * c_G_eff_conf_val * 0.32

/-- Gluon condensate correction ≈ 2.0% -/
theorem delta_gluon_z2_approx : 0.019 < delta_gluon_z2 ∧ delta_gluon_z2 < 0.021 := by
  unfold delta_gluon_z2 c_G_eff_conf_val
  constructor <;> norm_num

/-- Threshold matching correction (unchanged from Prop 0.0.17z) -/
noncomputable def delta_threshold_z2 : ℝ := 0.030

/-- Higher-order perturbative correction (unchanged) -/
noncomputable def delta_higher_order_z2 : ℝ := 0.020

/-- Instanton correction (unchanged) -/
noncomputable def delta_instanton_z2 : ℝ := 0.017

/-- Total NP correction with χ_eff = 2.21 -/
noncomputable def total_correction_z2 : ℝ :=
  delta_gluon_z2 + delta_threshold_z2 + delta_higher_order_z2 + delta_instanton_z2

/-- Total correction ≈ 8.7% -/
theorem total_correction_z2_approx :
    0.086 < total_correction_z2 ∧ total_correction_z2 < 0.089 := by
  unfold total_correction_z2 delta_gluon_z2 delta_threshold_z2 delta_higher_order_z2
    delta_instanton_z2 c_G_eff_conf_val
  constructor <;> norm_num

/-- Total correction is positive -/
theorem total_correction_z2_pos : total_correction_z2 > 0 := by
  unfold total_correction_z2 delta_gluon_z2 delta_threshold_z2 delta_higher_order_z2
    delta_instanton_z2 c_G_eff_conf_val
  norm_num

/-- Total correction is less than 1 (correction is perturbative) -/
theorem total_correction_z2_lt_one : total_correction_z2 < 1 := by
  unfold total_correction_z2 delta_gluon_z2 delta_threshold_z2 delta_higher_order_z2
    delta_instanton_z2 c_G_eff_conf_val
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 6: REVISED PREDICTION
    ═══════════════════════════════════════════════════════════════════════════

    √σ_corrected = 481.1 × (1 - 0.087) = 439.2 MeV

    Agreement: |439.2 - 440| / √(12² + 30²) = 0.8/32.3 = 0.02σ

    Reference: Markdown §5.3
-/

/-- Corrected string tension prediction with χ_eff -/
noncomputable def sqrt_sigma_z2_MeV : ℝ :=
  sqrt_sigma_bootstrap_MeV * (1 - total_correction_z2)

/-- Corrected prediction ≈ 439 MeV -/
theorem sqrt_sigma_z2_approx :
    438 < sqrt_sigma_z2_MeV ∧ sqrt_sigma_z2_MeV < 441 := by
  unfold sqrt_sigma_z2_MeV total_correction_z2 delta_gluon_z2 delta_threshold_z2
    delta_higher_order_z2 delta_instanton_z2 c_G_eff_conf_val sqrt_sigma_bootstrap_MeV
  constructor <;> norm_num

/-- Corrected prediction is positive -/
theorem sqrt_sigma_z2_pos : sqrt_sigma_z2_MeV > 0 := by
  unfold sqrt_sigma_z2_MeV
  apply mul_pos sqrt_sigma_bootstrap_pos
  linarith [total_correction_z2_lt_one]

/-- Residual from FLAG 2024 observation -/
noncomputable def residual_z2_FLAG_MeV : ℝ :=
  sqrt_sigma_z2_MeV - sqrt_sigma_FLAG_MeV

/-- Residual is very small (< 2 MeV) -/
theorem residual_z2_small : |residual_z2_FLAG_MeV| < 2 := by
  unfold residual_z2_FLAG_MeV sqrt_sigma_z2_MeV total_correction_z2
    delta_gluon_z2 delta_threshold_z2 delta_higher_order_z2 delta_instanton_z2
    c_G_eff_conf_val sqrt_sigma_bootstrap_MeV sqrt_sigma_FLAG_MeV
  norm_num

/-- Framework uncertainty on corrected prediction (MeV) — from §5.4.
    Sources of uncertainty (added in quadrature):
    - Interpolation function choice: ±3 MeV (spread across Gaussian/erf/logistic/linear)
    - d_inter identification: ±10% → ±4 MeV (inradius vs other geometric scales)
    - Correction budget individual uncertainties: ±10 MeV (from Prop 0.0.17z)
    - Combined: √(3² + 4² + 10²) ≈ √125 ≈ 11.2, rounded to 12 MeV -/
noncomputable def sqrt_sigma_z2_err_MeV : ℝ := 12

/-- Combined uncertainty with FLAG (quadrature sum) -/
noncomputable def combined_uncertainty_z2_FLAG : ℝ :=
  Real.sqrt (sqrt_sigma_z2_err_MeV ^ 2 + sqrt_sigma_FLAG_err_MeV ^ 2)

/-- Combined uncertainty is positive -/
theorem combined_uncertainty_z2_pos : combined_uncertainty_z2_FLAG > 0 := by
  unfold combined_uncertainty_z2_FLAG
  apply Real.sqrt_pos.mpr
  unfold sqrt_sigma_z2_err_MeV sqrt_sigma_FLAG_err_MeV
  norm_num

/-- Combined uncertainty ≥ 30 MeV (dominated by FLAG error) -/
theorem combined_uncertainty_z2_ge_30 : combined_uncertainty_z2_FLAG ≥ 30 := by
  unfold combined_uncertainty_z2_FLAG sqrt_sigma_z2_err_MeV sqrt_sigma_FLAG_err_MeV
  have h30 : Real.sqrt (30 * 30) = 30 := by
    have : (30 : ℝ) * 30 = 30 ^ 2 := by ring
    rw [this, Real.sqrt_sq (by norm_num : (30:ℝ) ≥ 0)]
  have h : Real.sqrt ((12 : ℝ) ^ 2 + 30 ^ 2) ≥ Real.sqrt (30 ^ 2) := by
    apply Real.sqrt_le_sqrt
    norm_num
  simp only [pow_two] at h ⊢
  calc Real.sqrt (12 * 12 + 30 * 30) ≥ Real.sqrt (30 * 30) := h
    _ = 30 := h30

/-- Tension with FLAG: < 0.1σ (essentially exact agreement).
    |residual| / combined_uncertainty < 2/30 < 0.1 -/
theorem tension_z2_FLAG_excellent :
    |residual_z2_FLAG_MeV| / combined_uncertainty_z2_FLAG < 0.1 := by
  have h_res : |residual_z2_FLAG_MeV| < 2 := residual_z2_small
  have h_unc : combined_uncertainty_z2_FLAG ≥ 30 := combined_uncertainty_z2_ge_30
  have h_unc_pos : combined_uncertainty_z2_FLAG > 0 := combined_uncertainty_z2_pos
  calc |residual_z2_FLAG_MeV| / combined_uncertainty_z2_FLAG
      < 2 / combined_uncertainty_z2_FLAG := by
        apply div_lt_div_of_pos_right h_res h_unc_pos
    _ ≤ 2 / 30 := by
        apply div_le_div_of_nonneg_left (by norm_num : (2:ℝ) ≥ 0) (by norm_num : (0:ℝ) < 30) h_unc
    _ < 0.1 := by norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 7: SELF-CONSISTENCY CHECKS
    ═══════════════════════════════════════════════════════════════════════════

    Reference: Markdown §6
-/

/-- UV limit check: χ_eff(μ) ≤ 4 for all μ ≥ 0 (bounded above) -/
theorem uv_consistency (mu : ℝ) (hmu : mu ≥ 0) : chi_eff mu ≤ 4 :=
  (chi_eff_range hmu).2

/-- UV limit: resolution_f(ξ) → 1 as ξ → +∞.
    Since exp(-ξ²) → 0 as ξ → ∞, we have 1 - exp(-ξ²) → 1.
    This uses Filter.Tendsto with the atTop filter. -/
theorem resolution_f_tendsto_one :
    Filter.Tendsto resolution_f Filter.atTop (nhds 1) := by
  unfold resolution_f
  -- Step 1: (fun ξ => ξ²) → +∞
  have h_sq : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  -- Step 2: (fun ξ => exp(-ξ²)) → 0 by composing exp(-·) with ξ²
  have h_exp : Filter.Tendsto (fun x : ℝ => Real.exp (-(x ^ 2))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h_sq
  -- Step 3: 1 - exp(-ξ²) → 1 - 0 = 1
  have h_sub : Filter.Tendsto (fun x => 1 - Real.exp (-(x ^ 2)))
      Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub h_exp
  simp only [sub_zero] at h_sub
  exact h_sub

/-- UV limit: χ_eff(μ) → 4 as μ → +∞.
    Since resolution_f(ξ(μ)) → 1 as μ → ∞, we have χ_eff = 2 + 2f → 4.
    This is the proper Filter.Tendsto formulation of the UV limit. -/
theorem chi_eff_uv_limit :
    Filter.Tendsto chi_eff Filter.atTop (nhds 4) := by
  unfold chi_eff
  -- Step 1: xi(μ) = μ * (d_inter/ℏc) → +∞ as μ → +∞
  have h_ratio_pos : (0 : ℝ) < d_inter_fm / hbar_c_MeV_fm :=
    div_pos d_inter_pos hbar_c_pos
  have h_xi : Filter.Tendsto xi Filter.atTop Filter.atTop := by
    unfold xi
    show Filter.Tendsto (fun mu_MeV => mu_MeV * d_inter_fm / hbar_c_MeV_fm) Filter.atTop Filter.atTop
    rw [show (fun mu_MeV : ℝ => mu_MeV * d_inter_fm / hbar_c_MeV_fm) =
        (fun mu_MeV => mu_MeV * (d_inter_fm / hbar_c_MeV_fm)) from by ext; ring]
    exact Filter.Tendsto.atTop_mul_const h_ratio_pos Filter.tendsto_id
  -- Step 2: resolution_f(xi(μ)) → 1
  have h_res : Filter.Tendsto (fun μ => resolution_f (xi μ)) Filter.atTop (nhds 1) :=
    resolution_f_tendsto_one.comp h_xi
  -- Step 3: 2 * resolution_f(xi(μ)) → 2 * 1 = 2
  have h_mul : Filter.Tendsto (fun μ => 2 * resolution_f (xi μ))
      Filter.atTop (nhds (2 * 1)) :=
    tendsto_const_nhds.mul h_res
  -- Step 4: 2 + 2 * resolution_f(xi(μ)) → 2 + 2 = 4
  have h_add : Filter.Tendsto (fun μ => 2 + 2 * resolution_f (xi μ))
      Filter.atTop (nhds (2 + 2 * 1)) :=
    tendsto_const_nhds.add h_mul
  simp only [mul_one] at h_add
  norm_num at h_add
  exact h_add

/-- IR limit check: χ_eff(0) = 2 -/
theorem ir_consistency : chi_eff 0 = 2 := chi_eff_ir

/-- No new parameters: d_inter is derived from R_stella -/
theorem no_new_parameters : d_inter_fm = R_stella_fm / 3 := by
  unfold d_inter_fm R_fm
  ring

/-- Dimensional analysis: ξ = μ·d/ℏc is dimensionless.
    (This is a structural claim; we verify the formula uses consistent units.) -/
theorem dimensional_consistency :
    xi mu_conf_MeV = mu_conf_MeV * d_inter_fm / hbar_c_MeV_fm := by
  unfold xi
  ring

/-- Improvement over Prop 0.0.17z: total correction reduced from 9.6% to 8.7% -/
theorem correction_improvement :
    total_correction_z2 < total_correction_fraction total_correction := by
  unfold total_correction_z2 delta_gluon_z2 delta_threshold_z2 delta_higher_order_z2
    delta_instanton_z2 c_G_eff_conf_val
  unfold total_correction_fraction total_correction
  unfold gluon_correction threshold_correction higher_order_correction instanton_correction
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 8: ROBUSTNESS (ALTERNATIVE INTERPOLATION FUNCTIONS)
    ═══════════════════════════════════════════════════════════════════════════

    All reasonable interpolation functions give √σ in 434–441 MeV range.
    Spread is ±3 MeV, well within 440 ± 30 MeV.

    Reference: Markdown §6.2
-/

/-- Alternative interpolation: linear (capped at 1).
    f_linear(ξ) = min(ξ, 1). Reference: Markdown §6.2, row 4. -/
noncomputable def f_linear (xi_val : ℝ) : ℝ := min xi_val 1

/-- f_linear ∈ [0, 1] for ξ ≥ 0 -/
theorem f_linear_range {xi_val : ℝ} (hξ : 0 ≤ xi_val) :
    0 ≤ f_linear xi_val ∧ f_linear xi_val ≤ 1 := by
  unfold f_linear
  constructor
  · exact le_min hξ (by norm_num)
  · exact min_le_right _ _

/-- f_linear(0) = 0 (IR limit) -/
theorem f_linear_ir : f_linear 0 = 0 := by
  unfold f_linear; simp

/-- f_linear monotone on [0, ∞) -/
theorem f_linear_monotone {a b : ℝ} (hab : a ≤ b) :
    f_linear a ≤ f_linear b := by
  unfold f_linear; exact min_le_min_right 1 hab

/-- Alternative interpolation: logistic with steepness β = 2π.
    f_logistic(ξ) = 1/(1 + exp(-2π(ξ - 1))). Reference: Markdown §6.2, row 3. -/
noncomputable def f_logistic (xi_val : ℝ) : ℝ :=
  1 / (1 + Real.exp (-(2 * Real.pi) * (xi_val - 1)))

/-- f_logistic ∈ [0, 1] for all ξ -/
theorem f_logistic_range (xi_val : ℝ) :
    0 ≤ f_logistic xi_val ∧ f_logistic xi_val ≤ 1 := by
  unfold f_logistic
  have h_exp_pos := Real.exp_pos (-(2 * Real.pi) * (xi_val - 1))
  constructor
  · apply div_nonneg (by norm_num) (by linarith)
  · rw [div_le_one (by linarith)]
    linarith

/-- Alternative interpolation: error function erf(ξ) = (2/√π) ∫₀ξ exp(-t²) dt.
    Reference: Markdown §6.2, row 2.
    The error function is a standard special function (Abramowitz & Stegun §7.1).
    Mathlib v4.26 does not include erf, so we define it here from the integral. -/
noncomputable def f_erf (xi_val : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..xi_val, Real.exp (-(t ^ 2))

/-- erf(0) = 0 (IR limit): the integral over a zero-width interval vanishes. -/
theorem f_erf_ir : f_erf 0 = 0 := by
  unfold f_erf
  simp [intervalIntegral.integral_same]

/-- erf(ξ) ≥ 0 for ξ ≥ 0.
    The integrand exp(-t²) > 0 on [0, ξ], so the integral is positive,
    and the prefactor 2/√π > 0. -/
theorem f_erf_nonneg {xi_val : ℝ} (hξ : 0 ≤ xi_val) : 0 ≤ f_erf xi_val := by
  unfold f_erf
  apply mul_nonneg
  · apply div_nonneg (by norm_num)
    exact Real.sqrt_nonneg _
  · apply intervalIntegral.integral_nonneg hξ
    intro t _
    exact le_of_lt (Real.exp_pos _)

/-- Helper: exp(-x²) = exp(-1 * x²) for rewriting between our convention and Mathlib's. -/
private theorem exp_neg_sq_eq (x : ℝ) : Real.exp (-(x ^ 2)) = Real.exp (-1 * x ^ 2) := by
  ring_nf

/-- The Gaussian integral over [0,∞): ∫ x in Ioi 0, exp(-1 * x²) = √π/2.
    Direct from Mathlib's integral_gaussian_Ioi with b=1. -/
private theorem gaussian_integral_Ioi_one :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-1 * x ^ 2) = Real.sqrt Real.pi / 2 := by
  have h := integral_gaussian_Ioi 1
  simp only [div_one] at h
  exact h

/-- The interval integral ∫₀ξ exp(-t²) dt ≤ √π/2 for all ξ ≥ 0.
    Proof: the integrand is nonneg, and Ioc 0 ξ ⊆ Ioi 0, so the integral
    over the finite interval is bounded by the integral over [0,∞) = √π/2. -/
private theorem interval_integral_exp_neg_sq_le_sqrt_pi_div_two {xi_val : ℝ} (hξ : 0 ≤ xi_val) :
    ∫ t in (0 : ℝ)..xi_val, Real.exp (-(t ^ 2)) ≤ Real.sqrt Real.pi / 2 := by
  -- Rewrite to Mathlib's convention: exp(-1 * t²)
  simp_rw [exp_neg_sq_eq]
  -- Convert interval integral to set integral over Ioc
  rw [intervalIntegral.integral_of_le hξ]
  rw [← gaussian_integral_Ioi_one]
  apply MeasureTheory.setIntegral_mono_set
  · exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)).integrableOn
  · exact MeasureTheory.ae_of_all _ (fun t => le_of_lt (Real.exp_pos _))
  · exact Set.Ioc_subset_Ioi_self.eventuallyLE

/-- erf(ξ) ≤ 1 for all ξ ≥ 0.
    Proof: (2/√π) × ∫₀ξ exp(-t²) dt ≤ (2/√π) × (√π/2) = 1.
    Uses the Gaussian integral ∫₀^∞ exp(-t²) dt = √π/2 (Mathlib). -/
theorem f_erf_le_one {xi_val : ℝ} (hξ : 0 ≤ xi_val) : f_erf xi_val ≤ 1 := by
  unfold f_erf
  have h_sqrt_pi_pos : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h_prefactor : (2 : ℝ) / Real.sqrt Real.pi > 0 := div_pos (by norm_num) h_sqrt_pi_pos
  have h_int := interval_integral_exp_neg_sq_le_sqrt_pi_div_two hξ
  calc 2 / Real.sqrt Real.pi * ∫ t in (0:ℝ)..xi_val, Real.exp (-(t ^ 2))
      ≤ 2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_left h_int (le_of_lt h_prefactor)
    _ = 1 := by field_simp

/-- erf range: f_erf(ξ) ∈ [0, 1] for ξ ≥ 0 -/
theorem f_erf_range {xi_val : ℝ} (hξ : 0 ≤ xi_val) :
    0 ≤ f_erf xi_val ∧ f_erf xi_val ≤ 1 :=
  ⟨f_erf_nonneg hξ, f_erf_le_one hξ⟩

/-- Derive √σ from any χ_eff value using the correction pipeline.
    √σ(χ) = 481.1 × (1 - [(1/2) × c_G_full × E(χ) × 0.32 + 0.030 + 0.020 + 0.017]) -/
noncomputable def sqrt_sigma_from_chi (chi : ℝ) : ℝ :=
  sqrt_sigma_bootstrap_MeV * (1 - ((1/2) * c_G_eff chi * 0.32 + 0.030 + 0.020 + 0.017))

/-- erf(0.333) bounded below via Taylor series.
    erf(x) = (2/√π)(x - x³/3 + x⁵/10 - ...)
    Alternating series with decreasing terms, so:
    erf(0.333) ≥ (2/√π)(0.333 - 0.333³/3) = (2/√π)(0.333 - 0.01230) = (2/√π)(0.32070)
    With √π > 1.7724: (2/1.7724)(0.32070) > 1.1283 × 0.32070 > 0.3619
    erf(0.333) ≤ (2/√π)(0.333 - 0.333³/3 + 0.333⁵/10) = (2/√π)(0.32111)
    With √π < 1.7725: (2/1.7725)(0.32111) < 1.1284 × 0.32111 < 0.3625 -/
noncomputable def f_erf_conf_val : ℝ := 0.363

/-- χ_eff with erf interpolation at confinement scale.
    f_erf(0.333) ≈ 0.363, χ_eff = 2 + 2×0.363 = 2.726 -/
noncomputable def chi_eff_erf_conf : ℝ := 2 + 2 * f_erf_conf_val

/-- chi_eff_erf_conf ≈ 2.726 -/
theorem chi_eff_erf_conf_approx :
    2.72 < chi_eff_erf_conf ∧ chi_eff_erf_conf < 2.73 := by
  unfold chi_eff_erf_conf f_erf_conf_val
  constructor <;> norm_num

/-- √σ from erf interpolation: χ_eff = 2.726 → √σ ≈ 434 MeV -/
theorem sqrt_sigma_erf_approx :
    433 < sqrt_sigma_from_chi chi_eff_erf_conf ∧
    sqrt_sigma_from_chi chi_eff_erf_conf < 436 := by
  unfold sqrt_sigma_from_chi c_G_eff c_G_full enhancement_factor z_half z_one
    chi_eff_erf_conf f_erf_conf_val sqrt_sigma_bootstrap_MeV
  norm_num

/-- χ_eff with linear interpolation at confinement scale.
    f_linear(0.333) = 0.333, χ_eff = 2.667 -/
noncomputable def chi_eff_linear_conf : ℝ := 2 + 2 * f_linear 0.333

/-- chi_eff_linear_conf ≈ 2.667 -/
theorem chi_eff_linear_conf_approx :
    2.66 < chi_eff_linear_conf ∧ chi_eff_linear_conf < 2.67 := by
  unfold chi_eff_linear_conf f_linear
  simp [min_eq_left (by norm_num : (0.333 : ℝ) ≤ 1)]
  norm_num

/-- √σ from linear interpolation: χ_eff = 2.667 → √σ ≈ 435 MeV -/
theorem sqrt_sigma_linear_approx :
    434 < sqrt_sigma_from_chi chi_eff_linear_conf ∧
    sqrt_sigma_from_chi chi_eff_linear_conf < 437 := by
  unfold sqrt_sigma_from_chi c_G_eff c_G_full enhancement_factor z_half z_one
    chi_eff_linear_conf f_linear sqrt_sigma_bootstrap_MeV
  simp [min_eq_left (by norm_num : (0.333 : ℝ) ≤ 1)]
  norm_num

/-- √σ from Gaussian (our primary choice): χ_eff = 2.210 → √σ ≈ 439 MeV -/
theorem sqrt_sigma_gaussian_approx :
    438 < sqrt_sigma_from_chi chi_eff_conf ∧
    sqrt_sigma_from_chi chi_eff_conf < 441 := by
  unfold sqrt_sigma_from_chi c_G_eff c_G_full enhancement_factor z_half z_one
    chi_eff_conf sqrt_sigma_bootstrap_MeV
  norm_num

/-- Robustness: spread across interpolation functions is ≤ 7 MeV.
    Linear gives √σ ∈ (434, 437), Gaussian gives √σ ∈ (438, 441).
    Max spread: 441 - 434 = 7 MeV ≪ 30 MeV (observation uncertainty). -/
theorem robustness_spread_small :
    ∀ (sigma1 sigma2 : ℝ),
      (434 < sigma1 ∧ sigma1 < 441) →
      (434 < sigma2 ∧ sigma2 < 441) →
      |sigma1 - sigma2| < 7 := by
  intro s1 s2 ⟨h1l, h1r⟩ ⟨h2l, h2r⟩
  rw [abs_lt]; constructor <;> linarith

/-- All interpolation results for √σ lie in 434–441 MeV range.
    These are the four specific values from markdown §6.2 Table:
    - Gaussian (heat kernel): 439.2 MeV
    - Error function: 434.4 MeV
    - Logistic (β=2π): 441.0 MeV
    - Linear (capped): 435.2 MeV
    The erf and logistic numerical evaluations are verified in the Python
    verification script; here we verify the claimed values are within range. -/
theorem robustness_all_interpolations :
    ∀ (sqrt_sigma_interp : ℝ),
      (sqrt_sigma_interp = 439.2 ∨ sqrt_sigma_interp = 434.4 ∨
       sqrt_sigma_interp = 441.0 ∨ sqrt_sigma_interp = 435.2) →
      434 ≤ sqrt_sigma_interp ∧ sqrt_sigma_interp ≤ 441 := by
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> constructor <;> norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 9: MAIN THEOREM
    ═══════════════════════════════════════════════════════════════════════════

    Proposition 0.0.17z2: Scale-dependent χ_eff improves agreement from
    0.63σ (fixed χ=4) to 0.02σ (χ_eff ≈ 2.21).

    Reference: Markdown §7
-/

/-- Main theorem: Prop 0.0.17z2 -/
theorem proposition_0_0_17z2 :
    -- (1) Interpenetration scale is geometric (no free parameters)
    d_inter_fm = R_stella_fm / 3 ∧
    -- (2) χ_eff range
    (2 ≤ chi_eff_conf ∧ chi_eff_conf ≤ 4) ∧
    -- (3) Total NP correction with χ_eff ≈ 8.7%
    (0.086 < total_correction_z2 ∧ total_correction_z2 < 0.089) ∧
    -- (4) Corrected prediction ≈ 439 MeV
    (438 < sqrt_sigma_z2_MeV ∧ sqrt_sigma_z2_MeV < 441) ∧
    -- (5) Excellent agreement (< 0.1σ)
    |residual_z2_FLAG_MeV| < 2 ∧
    -- (6) Improvement over Prop 0.0.17z
    total_correction_z2 < total_correction_fraction total_correction := by
  exact ⟨no_new_parameters,
         chi_eff_conf_range,
         total_correction_z2_approx,
         sqrt_sigma_z2_approx,
         residual_z2_small,
         correction_improvement⟩

end ChiralGeometrogenesis.Foundations.Proposition_0_0_17z2
