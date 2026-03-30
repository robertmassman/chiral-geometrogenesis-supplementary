/-
  Constants/Core.lean — Fundamental particle physics, QCD beta function,
  SU(3) Lie algebra, color/phase geometry, and mathematical constants.

  Sections 1-4 and 11 from the original Constants.lean.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Constants

open Real

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: FUNDAMENTAL PARTICLE PHYSICS
    ═══════════════════════════════════════════════════════════════════════════

    Core parameters from QCD and the Standard Model.
-/

/-- Number of colors in QCD: N_c = 3.

    **Physical basis:**
    - R-ratio in e⁺e⁻ → hadrons
    - π⁰ → γγ decay rate
    - Number of light neutrino species (LEP)

    **Citation:** PDG 2024, QCD section -/
def N_c : ℕ := 3

/-- N_c is positive (used in many divisions) -/
theorem N_c_pos : N_c > 0 := by decide

/-- N_c ≠ 0 -/
theorem N_c_ne_zero : N_c ≠ 0 := by decide

/-- Number of light quark flavors: N_f = 3 (u, d, s).

    **Physical basis:**
    Counts quarks with mass ≪ Λ_QCD:
    - Up: m_u ≈ 2 MeV
    - Down: m_d ≈ 5 MeV
    - Strange: m_s ≈ 95 MeV

    **Citation:** PDG 2024, Quark Masses -/
def N_f : ℕ := 3

/-- N_f is positive -/
theorem N_f_pos : N_f > 0 := by decide

/-- Light quark flavors for chiral limit: N_f = 2 (u, d only).

    **Physical basis:**
    In the chiral limit for pion physics, only u and d quarks
    are treated as massless. Strange quark mass is not negligible.

    **Citation:** Gasser & Leutwyler, Ann. Phys. 158 (1984) -/
def N_f_chiral : ℕ := 2

/-- ℏc in MeV·fm (fundamental unit conversion constant).

    **Value:** 197.327 MeV·fm (CODATA 2018)

    **Usage:** Converts between energy (MeV) and length (fm) scales.
    r = ℏc/E gives the characteristic length for energy scale E.

    **Citation:** CODATA 2018, ℏc = 197.3269804 MeV·fm -/
noncomputable def hbar_c_MeV_fm : ℝ := 197.327

/-- ℏc > 0 -/
theorem hbar_c_pos : hbar_c_MeV_fm > 0 := by
  unfold hbar_c_MeV_fm; norm_num

/-- Number of quark/lepton generations -/
def numberOfGenerations : ℕ := 3

/-- Baryon number change in sphaleron processes (ΔB = 3) -/
def baryonNumberChange : ℤ := 3

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: QCD AND BETA FUNCTION
    ═══════════════════════════════════════════════════════════════════════════

    Constants related to asymptotic freedom and confinement.
-/

/-- QCD scale Λ_QCD in MeV (5-flavor MS-bar scheme).

    **Value:** 213 ± 8 MeV (PDG 2024)

    **Convention:** MS-bar scheme, 5-flavor (includes b quark)

    **Citation:** PDG 2024, αs running -/
noncomputable def lambdaQCD : ℝ := 213

/-- Λ_QCD > 0 -/
theorem lambdaQCD_pos : lambdaQCD > 0 := by
  unfold lambdaQCD; norm_num

/-- Pure-gauge (N_f = 0) MS-bar QCD scale: Λ_MS̄_PG ≈ 258 MeV.

    **Value:** 0.5315 × 485 MeV = 257.78 ≈ 258 MeV.

    **Derivation:**
    Λ_MS̄/√σ = 0.5315 (Ishikawa et al. 2017, published JHEP version)
    √σ_PG = 485 MeV (pure-gauge string tension, N_f = 0)
    Λ_MS̄_PG = 0.5315 × 485 ≈ 257.8 ≈ 258 MeV

    **Note:** Distinct from `lambdaQCD` (N_f = 5 MS-bar, 213 MeV).
    Used in Theorem 7.4.7 Part (b): C_gap = m_{0⁺⁺}/Λ_MS̄_PG ≈ 6.4.

    **Citation:** T. Ishikawa et al., JHEP 12 (2017) 067, arXiv:1702.06289. -/
noncomputable def lambdaQCD_pure_gauge : ℝ := 258

/-- Λ_QCD_PG > 0 -/
theorem lambdaQCD_pure_gauge_pos : lambdaQCD_pure_gauge > 0 := by
  unfold lambdaQCD_pure_gauge; norm_num

/-- One-loop beta function coefficient formula:
    β₀ = (11N_c - 2N_f) / (48π²)

    **Derivation:**
    At one-loop: β(g) = -β₀ g³ + O(g⁵)
    β₀ = (1/16π²) × [11C₂(G)/3 - 4T(R)N_f/3]
    For SU(N): C₂(G) = N, T(R) = 1/2

    **Citation:** Gross & Wilczek (1973), Politzer (1973) -/
noncomputable def beta0_formula (Nc Nf : ℕ) : ℝ :=
  (11 * Nc - 2 * Nf) / (3 * 16 * Real.pi^2)

/-- β₀ for SU(3) with N_f = 3 flavors -/
noncomputable def beta0 : ℝ := beta0_formula N_c N_f

/-- β₀ for pure Yang-Mills (N_f = 0) -/
noncomputable def beta0_pure_YM : ℝ := beta0_formula N_c 0

/-- Asymptotic freedom: β₀ > 0 for SU(3) with N_f = 3 -/
theorem beta0_positive : beta0 > 0 := by
  unfold beta0 beta0_formula N_c N_f
  have hdenom : (3 * 16 * Real.pi^2 : ℝ) > 0 := by
    apply mul_pos
    · apply mul_pos <;> norm_num
    · exact sq_pos_of_pos Real.pi_pos
  apply div_pos _ hdenom
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 3: SU(3) LIE ALGEBRA STRUCTURE
    ═══════════════════════════════════════════════════════════════════════════

    Structural constants for SU(N) Lie algebras.
-/

/-- Rank of SU(N): rank = N - 1 -/
def su_rank (N : ℕ) : ℕ := N - 1

/-- SU(3) rank = 2 -/
theorem su3_rank : su_rank 3 = 2 := rfl

/-- Dimension of adjoint representation: dim = N² - 1 -/
def adjoint_dim (N : ℕ) : ℕ := N * N - 1

/-- SU(3) adjoint dimension = 8 -/
theorem su3_adjoint_dim : adjoint_dim 3 = 8 := rfl

/-- Number of roots: N² - N = N(N-1) -/
def num_roots (N : ℕ) : ℕ := N * N - N

/-- SU(3) has 6 roots -/
theorem su3_num_roots : num_roots 3 = 6 := rfl

/-- Number of zero weights (Cartan generators): N - 1 -/
def num_zero_weights (N : ℕ) : ℕ := N - 1

/-- Killing form coefficient for SU(3): K(T_a, T_a) = -12

    **Derivation:**
    K(X,Y) = Tr(ad_X ∘ ad_Y) = -2N·Tr(XY) for su(N)
    With Tr(T_a T_b) = 2δ_ab: K(T_a, T_a) = -2·3·2 = -12

    **Citation:** Humphreys, "Lie Algebras" (1972), §8.5 -/
def killingCoefficient : ℝ := -12

/-- Dual Coxeter number h∨ = N for SU(N) -/
def dualCoxeterNumber (N : ℕ) : ℕ := N

/-- SU(3) dual Coxeter number = 3 -/
theorem su3_dual_coxeter : dualCoxeterNumber 3 = 3 := rfl

/-- Gell-Mann matrix trace normalization: Tr(λ_a λ_b) = 2δ_ab

    **Convention:** Standard physics convention (not math's Tr = 1/2)

    **Citation:** Gell-Mann (1962), Cheng & Li "Gauge Theory" Ch.5 -/
def gellMannTraceNorm : ℝ := 2

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 4: COLOR/PHASE GEOMETRY
    ═══════════════════════════════════════════════════════════════════════════

    Phase angles for the three-color field structure.
-/

/-- Color phase offset: Δφ = 2π/3 (120°).

    **Physical meaning:**
    The three color fields (R, G, B) are phase-shifted by 120°
    to maintain SU(3) symmetry. This is the minimal phase offset
    that yields color neutrality when summed.

    **Citation:** Definition 0.1.2 (Three Color Fields) -/
noncomputable def colorPhaseOffset : ℝ := 2 * Real.pi / 3

/-- Red phase: φ_R = 0 (reference phase) -/
noncomputable def phi_R : ℝ := 0

/-- Green phase: φ_G = 2π/3 -/
noncomputable def phi_G : ℝ := 2 * Real.pi / 3

/-- Blue phase: φ_B = 4π/3 -/
noncomputable def phi_B : ℝ := 4 * Real.pi / 3

/-- Phase separation is exactly 2π/3 -/
theorem phase_separations :
    phi_G - phi_R = colorPhaseOffset ∧
    phi_B - phi_G = colorPhaseOffset := by
  unfold phi_R phi_G phi_B colorPhaseOffset
  constructor <;> ring

/-- Phases sum to 2π (color neutrality condition) -/
theorem phase_sum : phi_R + phi_G + phi_B = 2 * Real.pi := by
  unfold phi_R phi_G phi_B; ring

/-- ω² = 2 (characteristic frequency squared from limit cycle).

    **Physical meaning:**
    The emergent oscillation frequency from the three-field
    coupled dynamics satisfies ω² = 2 in natural units.

    **Citation:** Theorem 0.2.4 (Pre-geometric Energy) -/
def omegaSquared : ℝ := 2

/-- Characteristic frequency ω = √2 -/
noncomputable def omegaCharacteristic : ℝ := Real.sqrt 2

/-- ω² relation holds -/
theorem omega_sq_relation : omegaCharacteristic ^ 2 = omegaSquared := by
  unfold omegaCharacteristic omegaSquared
  rw [sq_sqrt]; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 11: MATHEMATICAL CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Pure mathematical constants used in geometric constructions.
-/

/-- Golden ratio: φ = (1 + √5)/2 ≈ 1.618034.

    **Properties:**
    - φ² = φ + 1
    - 1/φ = φ - 1
    - Appears in icosahedral/dodecahedral symmetry

    **Citation:** Standard mathematical constant -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- φ > 0 -/
theorem goldenRatio_pos : goldenRatio > 0 := by
  unfold goldenRatio
  have h : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  linarith

/-- φ > 1 -/
theorem goldenRatio_gt_one : goldenRatio > 1 := by
  unfold goldenRatio
  have h : Real.sqrt 5 > 1 := by
    have h5 : (5:ℝ) > 1 := by norm_num
    have h1 : Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) h5
    simp only [Real.sqrt_one] at h1
    exact h1
  linarith

/-- Golden ratio inverse: 1/φ = φ - 1 = (√5 - 1)/2 ≈ 0.618034 -/
noncomputable def goldenRatioInverse : ℝ := (Real.sqrt 5 - 1) / 2

/-- Relation: φ · (1/φ) = 1 -/
theorem goldenRatio_inverse_relation : goldenRatio * goldenRatioInverse = 1 := by
  unfold goldenRatio goldenRatioInverse
  have h5 : (0:ℝ) ≤ 5 := by norm_num
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt h5
  field_simp
  linarith [hsq]

/-- White direction norm: 1/√3 (unit vector along diagonal).

    **Physical meaning:**
    The "white" direction in color space is (1,1,1)/√3,
    representing the color-neutral combination. -/
noncomputable def whiteDirectionNorm : ℝ := 1 / Real.sqrt 3

end ChiralGeometrogenesis.Constants
