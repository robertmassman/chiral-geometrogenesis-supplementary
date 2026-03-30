/-
  Constants/Specialized.lean — Edge-mode decomposition and W-soliton
  existence/properties constants.

  Sections 22-edge and 27-W from the original Constants.lean.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import ChiralGeometrogenesis.Constants.Cosmology

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Constants

open Real

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 22: EDGE-MODE DECOMPOSITION (PROP 0.0.17ac)
    ═══════════════════════════════════════════════════════════════════════════

    Constants for the 64 = 52 + 12 decomposition of adj⊗adj channels
    into running (local) and non-running (holonomy) modes on the
    stella octangula.

    Reference: Proposition 0.0.17ac
-/

/-- Cycle rank (first Betti number) of the complete graph K₄:
    β₁(K₄) = |E| - |V| + 1 = 6 - 4 + 1 = 3.

    Counts the number of independent closed loops in the
    tetrahedral 1-skeleton.

    **Citation:** Standard graph theory -/
def cycle_rank_K4 : ℕ := 6 - 4 + 1

/-- β₁(K₄) = 3 -/
theorem cycle_rank_K4_value : cycle_rank_K4 = 3 := rfl

/-- Cycle rank of the stella octangula 1-skeleton:
    β₁(∂S) = β₁(K₊) + β₁(K₋) = 3 + 3 = 6.

    For a disconnected graph with c = 2 components:
    β₁ = |E| - |V| + c = 12 - 8 + 2 = 6.

    **Citation:** Proposition 0.0.17ac, Lemma 3.2.2 -/
def cycle_rank_stella : ℕ := 2 * cycle_rank_K4

/-- β₁(∂S) = 6 -/
theorem cycle_rank_stella_value : cycle_rank_stella = 6 := rfl

/-- Dimension of the adj⊗adj tensor product for SU(N_c):
    (N_c² - 1)² = 8² = 64 for SU(3).

    The decomposition: 8⊗8 = 1 ⊕ 8_s ⊕ 8_a ⊕ 10 ⊕ 10̄ ⊕ 27.
    Total: 1 + 8 + 8 + 10 + 10 + 27 = 64.

    **Citation:** Proposition 0.0.17ac §3.1 -/
def adj_tensor_dim (Nc : ℕ) : ℕ := (Nc * Nc - 1) * (Nc * Nc - 1)

/-- adj⊗adj dimension for SU(3) = 64 -/
theorem adj_tensor_dim_su3 : adj_tensor_dim 3 = 64 := rfl

/-- Number of non-running holonomy modes on the stella octangula:
    N_holonomy = β₁(∂S) × rank(SU(N_c)) = 6 × (N_c - 1).

    For SU(3): N_holonomy = 6 × 2 = 12.

    These modes parameterize the gauge-invariant configuration space
    (Cartan angles on independent cycles) and are protected from
    Wilsonian RG flow by the β-independent Weyl measure.

    **Citation:** Proposition 0.0.17ac, Theorem 3.4.1 -/
def holonomy_mode_count (Nc : ℕ) : ℕ := cycle_rank_stella * (Nc - 1)

/-- N_holonomy = 12 for SU(3) -/
theorem holonomy_mode_count_su3 : holonomy_mode_count 3 = 12 := rfl

/-- Number of running (local) face modes:
    N_local = (N_c² - 1)² - N_holonomy.

    For SU(3): N_local = 64 - 12 = 52.

    These modes participate in standard QCD running and give
    the coupling 1/α_s(M_P) = 52.

    **Citation:** Proposition 0.0.17ac, Corollary 3.4.2 -/
def local_mode_count (Nc : ℕ) : ℕ := adj_tensor_dim Nc - holonomy_mode_count Nc

/-- N_local = 52 for SU(3) -/
theorem local_mode_count_su3 : local_mode_count 3 = 52 := rfl

/-- The fundamental decomposition: 64 = 52 + 12 -/
theorem edge_mode_decomposition_su3 :
    adj_tensor_dim 3 = local_mode_count 3 + holonomy_mode_count 3 := rfl

/-- Weyl group order of SU(3): |W(SU(3))| = |S₃| = 6.

    The Weyl group permutes the eigenvalues of conjugacy class
    representatives on the maximal torus.

    **Citation:** Standard Lie theory -/
def weyl_group_order_su3 : ℕ := 6

/-- |W(SU(3))| = 3! -/
theorem weyl_group_order_su3_value : weyl_group_order_su3 = Nat.factorial 3 := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 27: W-SOLITON EXISTENCE AND PROPERTIES CONSTANTS (Theorem 4.3.2)
    ═══════════════════════════════════════════════════════════════════════════

    Constants for W-soliton mass bounds, self-interaction, and observational
    constraints. These supplement the W-sector constants in Sections 10–11
    (v_W, e_W, λ_HW, M_W_precision) with the ANW numerical coefficient,
    central mass estimate, and JWST self-interaction bound.

    Reference: docs/proofs/Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md
-/

/-- ANW numerical coefficient: 72.96 (dimensionless).

    **Physical meaning:**
    The Adkins-Nappi-Witten (1983) numerically-optimized B = 1 hedgehog Skyrmion
    mass coefficient. The physical mass is M = (ANW coefficient) × v_W / e_W.
    This equals 1.232 × 6π² ≈ 72.96, reflecting that the B = 1 hedgehog sits
    23.2% above the Faddeev-Bogomolny topological lower bound (6π² ≈ 59.22).

    **Citation:** Adkins, Nappi & Witten (1983), Nucl. Phys. B 228, 552–566.
                  Theorem 4.3.2 §4.4, §5.1 -/
noncomputable def anw_coefficient : ℝ := 72.96

/-- ANW coefficient > 0 -/
theorem anw_coefficient_pos : anw_coefficient > 0 := by
  unfold anw_coefficient; norm_num

/-- ANW coefficient > 6π² (exceeds Faddeev bound).

    The ANW numerical result is 23.2% above the topological lower bound.
    This is a fundamental property of the Skyrme model: no BPS solution exists,
    so the actual soliton energy strictly exceeds the Faddeev bound. -/
theorem anw_gt_faddeev : anw_coefficient > 6 * Real.pi ^ 2 := by
  unfold anw_coefficient
  -- Need: 72.92 > 6π²
  -- π < 3.15, so π² < 9.9225, 6 × 9.9225 = 59.535 < 72.92
  have h1 : Real.pi < 3.15 := pi_lt_d2
  have h2 : Real.pi ^ 2 < 3.15 ^ 2 := by
    exact sq_lt_sq' (by linarith [Real.pi_pos]) h1
  nlinarith

/-- ANW-to-Faddeev ratio: 72.92 / (6π²) ≈ 1.232.

    More precisely: 1.22 < 72.92/(6π²) < 1.25. -/
theorem anw_faddeev_ratio_approx :
    1.22 < anw_coefficient / (6 * Real.pi ^ 2) ∧
    anw_coefficient / (6 * Real.pi ^ 2) < 1.25 := by
  unfold anw_coefficient
  have hpi_pos : (0 : ℝ) < 6 * Real.pi ^ 2 := by positivity
  have h_pi_lt : Real.pi < 3.15 := pi_lt_d2
  have h_pi_gt : 3.14 < Real.pi := pi_gt_d2
  have h_pi_sq_ub : Real.pi ^ 2 < 3.15 ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) h_pi_lt
  have h_pi_sq_lb : 3.14 ^ 2 < Real.pi ^ 2 :=
    sq_lt_sq' (by linarith [Real.pi_pos]) (by linarith)
  constructor
  · -- 1.22 < 72.92 / (6π²)  ⟺  1.22 × 6π² < 72.92  ⟺  7.32π² < 72.92
    -- π² < 9.9225, so 7.32 × 9.9225 = 72.63 < 72.92 ✓
    rw [lt_div_iff₀ hpi_pos]
    nlinarith
  · -- 72.92 / (6π²) < 1.25  ⟺  72.92 < 1.25 × 6π²  ⟺  72.92 < 7.5π²
    -- π² > 9.8596, so 7.5 × 9.8596 = 73.95 > 72.92 ✓
    rw [div_lt_iff₀ hpi_pos]
    nlinarith

/-- W-soliton mass using ANW coefficient: M_W^ANW = 72.92 × v_W / e_W.

    This is the numerically-optimized mass (upper estimate), as opposed to
    the Faddeev lower bound M_W = 6π² v_W / e_W.

    **Citation:** Theorem 4.3.2 §4.4 -/
noncomputable def M_W_anw_GeV : ℝ := anw_coefficient * v_W_precision_GeV / skyrme_e_W

/-- M_W^ANW > 0 -/
theorem M_W_anw_pos : M_W_anw_GeV > 0 := by
  unfold M_W_anw_GeV
  apply div_pos
  · exact mul_pos anw_coefficient_pos v_W_precision_pos
  · exact skyrme_e_W_pos

/-- M_W^ANW ≈ 1993 GeV -/
theorem M_W_anw_approx :
    1990 < M_W_anw_GeV ∧ M_W_anw_GeV < 2000 := by
  unfold M_W_anw_GeV anw_coefficient v_W_precision_GeV skyrme_e_W
  constructor <;> norm_num

/-- W-soliton central mass estimate: M_W = 1800 GeV.

    **Physical meaning:**
    The geometric mean of the Faddeev lower bound (~1620 GeV) and the
    ANW numerical result (~1993 GeV), representing the best estimate.

    **Citation:** Theorem 4.3.2 §4.4 -/
noncomputable def M_W_central_GeV : ℝ := 1800

/-- M_W central > 0 -/
theorem M_W_central_pos : M_W_central_GeV > 0 := by
  unfold M_W_central_GeV; norm_num

/-- W-soliton mass uncertainty: ±500 GeV.

    **Physical meaning:**
    Encompasses parameter uncertainties (v_W ± 15 GeV, e_W ± 0.3)
    and the Faddeev-to-ANW systematic (23.2% one-sided).

    **Citation:** Theorem 4.3.2 §4.4, uncertainty budget table -/
noncomputable def M_W_uncertainty_GeV : ℝ := 500

/-- M_W uncertainty > 0 -/
theorem M_W_uncertainty_pos : M_W_uncertainty_GeV > 0 := by
  unfold M_W_uncertainty_GeV; norm_num

/-- Central mass is between Faddeev and ANW bounds. -/
theorem M_W_central_between_bounds :
    M_W_precision_GeV < M_W_central_GeV ∧ M_W_central_GeV < M_W_anw_GeV := by
  constructor
  · unfold M_W_precision_GeV M_W_central_GeV; norm_num
  · unfold M_W_central_GeV M_W_anw_GeV anw_coefficient v_W_precision_GeV skyrme_e_W
    norm_num

/-- JWST 2025 Bullet Cluster self-interaction bound: σ/m < 0.2 cm²/g.

    **Physical meaning:**
    The tightest current constraint on dark matter self-interaction,
    from JWST observations of the Bullet Cluster.

    **Citation:** Cha et al. (2025), arXiv:2601.22245.
                  Theorem 4.3.2 §8.3 -/
noncomputable def jwst_sigma_m_bound : ℝ := 0.2

/-- JWST bound > 0 -/
theorem jwst_sigma_m_bound_pos : jwst_sigma_m_bound > 0 := by
  unfold jwst_sigma_m_bound; norm_num

/-- W-soliton lifetime lower bound: τ_W > 10^34 years.

    **Physical meaning:**
    The W-soliton is topologically protected against decay. As a complete
    gauge singlet with no sphaleron path, the topological charge Q_W is
    exactly conserved. The lifetime exceeds 10^34 years.

    **Citation:** Theorem 4.3.2 §5.3, §5.4 -/
noncomputable def tau_W_lower_bound_years : ℝ := 1e34

/-- τ_W lower bound > 0 -/
theorem tau_W_lower_bound_pos : tau_W_lower_bound_years > 0 := by
  unfold tau_W_lower_bound_years; norm_num

/-- W-soliton EFT cutoff: Λ_W = 4π v_W ≈ 1546 GeV.

    **Physical meaning:**
    The Skyrme model is a low-energy EFT valid below this scale.
    M_W/Λ_W ≈ 1.2 indicates higher-order operators contribute.

    **Citation:** Theorem 4.3.2 §9.3 -/
noncomputable def Lambda_W_GeV : ℝ := 4 * Real.pi * v_W_precision_GeV

/-- Λ_W > 0 -/
theorem Lambda_W_pos : Lambda_W_GeV > 0 := by
  unfold Lambda_W_GeV
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) v_W_precision_pos

/-- Λ_W ≈ 1546 GeV -/
theorem Lambda_W_approx :
    1540 < Lambda_W_GeV ∧ Lambda_W_GeV < 1550 := by
  unfold Lambda_W_GeV v_W_precision_GeV
  constructor
  · nlinarith [pi_gt_d2]
  · nlinarith [pi_lt_d2]

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 28: SKYRME PARAMETER GEOMETRIC DERIVATION (Proposition 4.3.5)
    ═══════════════════════════════════════════════════════════════════════════

    Constants for the pressure-kurtosis geometric determination of the
    W-sector Skyrme parameter e_W = 4.5 ± 1.2.

    Reference: docs/proofs/Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md
-/

/-- Effective dimensionless regularization parameter: ε̃ = 0.130.

    **Physical meaning:**
    The angular smoothing scale of the pressure function at the W vertex,
    at the resolution relevant for the Skyrme (four-derivative) term.
    Differs from the physical ε = 0.50 (Definition 0.1.3) because the
    Skyrme term probes finer angular structure than the kinetic term.

    **Determination:** Self-consistently determined by two independent routes:
    - GL-Skyrme matching (§6.7.2): ε̃_GL = 0.127
    - NJL bosonization inversion (§6.7.3): ε̃_NJL = 0.132
    Central value ε̃ = 0.130 is the arithmetic mean.

    **Citation:** Proposition 4.3.5 §4.6 -/
noncomputable def epsilon_tilde_W : ℝ := 0.130

/-- ε̃ > 0 -/
theorem epsilon_tilde_W_pos : epsilon_tilde_W > 0 := by
  unfold epsilon_tilde_W; norm_num

/-- ε̃ < 1 (well within domain angular radius) -/
theorem epsilon_tilde_W_lt_one : epsilon_tilde_W < 1 := by
  unfold epsilon_tilde_W; norm_num

/-- Uncertainty in ε̃: ±0.035 (constrained range [0.10, 0.16]).

    **Citation:** Proposition 4.3.5 §5.1 -/
noncomputable def epsilon_tilde_W_uncertainty : ℝ := 0.035

/-- δε̃ > 0 -/
theorem epsilon_tilde_W_uncertainty_pos : epsilon_tilde_W_uncertainty > 0 := by
  unfold epsilon_tilde_W_uncertainty; norm_num

/-- Skyrme parameter uncertainty: δe_W = 1.2 (±27%).

    **Physical meaning:**
    Dominated by regularization (+29%/−18% symmetrized to ±24%) and
    higher-order gradient terms (±12%), combined in quadrature.

    **Citation:** Proposition 4.3.5 §5.4 -/
noncomputable def skyrme_e_W_uncertainty : ℝ := 1.2

/-- δe_W > 0 -/
theorem skyrme_e_W_uncertainty_pos : skyrme_e_W_uncertainty > 0 := by
  unfold skyrme_e_W_uncertainty; norm_num

/-- The Skyrme parameter is within the QCD phenomenological range [4.25, 5.45].

    **Citation:** Proposition 4.3.5 §6.2 -/
theorem skyrme_e_W_in_QCD_range :
    4.25 ≤ skyrme_e_W ∧ skyrme_e_W ≤ 5.45 := by
  unfold skyrme_e_W
  constructor <;> norm_num

end ChiralGeometrogenesis.Constants
