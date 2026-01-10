/-
  Constants.lean

  Centralized Physical and Mathematical Constants for Chiral Geometrogenesis

  This file provides the SINGLE CANONICAL SOURCE for all constants used
  throughout the Lean formalization. Other files should import this file
  rather than redefining constants locally.

  Organization:
  1. Fundamental Particle Physics (N_c, N_f, ℏc)
  2. QCD and Beta Function (Λ_QCD, β₀)
  3. SU(3) Lie Algebra Structure (rank, dimension, Killing form)
  4. Color/Phase Geometry (phase offsets, ω²)
  5. Stella Octangula Geometry (symmetry orders, distances)
  6. Gravitational/Planck Constants (G, c, M_P)
  7. Experimental Values (pion decay, observation radius)
  8. Derived Constants (confinement radius, anomaly coefficients)

  Reference: docs/proofs/reference/Physical-Constants-Reference.md
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
    SECTION 5: STELLA OCTANGULA GEOMETRY
    ═══════════════════════════════════════════════════════════════════════════

    Combinatorial and symmetry constants for the stella octangula.

    NOTE: R_stella is the characteristic radius, chosen to match observed √σ = 440 MeV:
      R_stella = ℏc/√σ = 197.327/440 = 0.44847 fm
-/

/-- Stella octangula characteristic radius R_stella = ℏc/√σ ≈ 0.44847 fm.

    **Physical meaning:**
    This is the single phenomenological input at the QCD level.
    All QCD scales (√σ, f_π, Λ_QCD) derive from this single value.

    **Value determination:**
    R_stella = ℏc/√σ = 197.327 MeV·fm / 440 MeV = 0.44847 fm
    This ensures exact agreement with observed string tension.

    **Citation:** Proposition 0.0.17j -/
noncomputable def R_stella_fm : ℝ := 0.44847

/-- R_stella > 0 -/
theorem R_stella_pos : R_stella_fm > 0 := by unfold R_stella_fm; norm_num

/-- Historical value R_stella = 0.45 fm (for reference)

    This was the original approximation. The precise value 0.44847 fm
    is derived from matching √σ = 440 MeV exactly. -/
noncomputable def R_stella_approx_fm : ℝ := 0.45

/-- Order of W(F₄) Weyl group: |W(F₄)| = 1152.

    **Citation:** Humphreys, "Reflection Groups" (1990), Table 2.4 -/
def WF4_order : ℕ := 1152

/-- Order of stella octangula symmetry group: |S₄ × Z₂| = 48.

    **Breakdown:**
    - S₄ (tetrahedral rotations): order 24
    - Z₂ (antipodal/parity swap): order 2
    - Total: 24 × 2 = 48

    **Citation:** Coxeter, "Regular Polytopes" (1973), §2.3 -/
def stella_symmetry_order : ℕ := 48

/-- Number of 24-cell vertices (enhancement factor) -/
def cell24_vertices : ℕ := 24

/-- W(F₄) factorization: 1152 = 24 × 48 -/
theorem WF4_factorization : WF4_order = cell24_vertices * stella_symmetry_order := rfl

/-- Intrinsic edge length in natural units (normalized to 1) -/
noncomputable def intrinsicEdgeLength : ℝ := 1

/-- Intrinsic center-to-vertex distance -/
noncomputable def intrinsicCenterToVertex : ℝ := 1

/-- Intrinsic diagonal distance: 2/√3 -/
noncomputable def intrinsicDiagonalDistance : ℝ := 2 / Real.sqrt 3

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 6: FUNDAMENTAL PHYSICAL CONSTANTS (SI UNITS)
    ═══════════════════════════════════════════════════════════════════════════

    Speed of light, gravitational constant, and Planck constant in SI units.
    These are the base constants from which Planck units are derived.
-/

/-- Speed of light in vacuum: c = 299792458 m/s (exact by definition).

    **Citation:** BIPM SI definition (2019) -/
noncomputable def c_SI : ℝ := 299792458

/-- c > 0 -/
theorem c_SI_pos : c_SI > 0 := by unfold c_SI; norm_num

/-- Gravitational constant: G = 6.67430 × 10⁻¹¹ m³/(kg·s²).

    **Citation:** CODATA 2018, G = 6.67430(15) × 10⁻¹¹ m³ kg⁻¹ s⁻² -/
noncomputable def G_SI : ℝ := 6.67430e-11

/-- G > 0 -/
theorem G_SI_pos : G_SI > 0 := by unfold G_SI; norm_num

/-- Reduced Planck constant: ℏ = 1.054571817 × 10⁻³⁴ J·s.

    **Citation:** CODATA 2018, ℏ = 1.054571817... × 10⁻³⁴ J s -/
noncomputable def hbar_SI : ℝ := 1.054571817e-34

/-- ℏ > 0 -/
theorem hbar_SI_pos : hbar_SI > 0 := by unfold hbar_SI; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 7: PLANCK UNITS
    ═══════════════════════════════════════════════════════════════════════════

    Derived Planck units from fundamental constants.
-/

/-- Planck length: ℓ_P = √(ℏG/c³) ≈ 1.616255 × 10⁻³⁵ m.

    **Citation:** CODATA 2018 -/
noncomputable def planck_length_SI : ℝ := Real.sqrt (hbar_SI * G_SI / c_SI^3)

/-- Planck length numerical value (for direct comparisons) -/
noncomputable def planck_length_value : ℝ := 1.616255e-35

/-- Planck length in femtometers: ℓ_P ≈ 1.6 × 10⁻²⁰ fm -/
noncomputable def planck_length_fm : ℝ := 1.6e-20

/-- Planck time: t_P = √(ℏG/c⁵) ≈ 5.391 × 10⁻⁴⁴ s.

    **Citation:** CODATA 2018 -/
noncomputable def planck_time_SI : ℝ := Real.sqrt (hbar_SI * G_SI / c_SI^5)

/-- Planck time numerical value -/
noncomputable def planck_time_value : ℝ := 5.391247e-44

/-- Planck angular frequency: ω_P = 1/t_P = √(c⁵/(Gℏ)) ≈ 1.855 × 10⁴³ rad/s -/
noncomputable def planck_frequency_SI : ℝ := 1 / planck_time_SI

/-- Planck frequency from formula (equivalent definition) -/
noncomputable def planck_frequency_formula : ℝ := Real.sqrt (c_SI^5 / (G_SI * hbar_SI))

/-- Planck energy: E_P = ℏω_P ≈ 1.956 × 10⁹ J ≈ 1.22 × 10¹⁹ GeV -/
noncomputable def planck_energy_SI : ℝ := hbar_SI * planck_frequency_SI

/-- Planck energy in GeV: M_P ≈ 1.22089 × 10¹⁹ GeV.

    **Citation:** PDG 2024 -/
noncomputable def planck_mass_GeV : ℝ := 1.22089e19

/-- Planck mass (reduced): M_P = √(ℏc/G) -/
noncomputable def planck_mass_SI : ℝ := Real.sqrt (hbar_SI * c_SI / G_SI)

/-- Planck frequency is positive -/
theorem planck_frequency_pos : planck_frequency_SI > 0 := by
  unfold planck_frequency_SI planck_time_SI
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  apply div_pos
  · apply mul_pos hbar_SI_pos G_SI_pos
  · exact pow_pos c_SI_pos 5

/-- Planck time is positive -/
theorem planck_time_pos : planck_time_SI > 0 := by
  unfold planck_time_SI
  apply Real.sqrt_pos.mpr
  apply div_pos
  · apply mul_pos hbar_SI_pos G_SI_pos
  · exact pow_pos c_SI_pos 5

/-- Planck length is positive -/
theorem planck_length_pos : planck_length_SI > 0 := by
  unfold planck_length_SI
  apply Real.sqrt_pos.mpr
  apply div_pos
  · apply mul_pos hbar_SI_pos G_SI_pos
  · exact pow_pos c_SI_pos 3

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 8: GRAVITATIONAL CONSTANTS STRUCTURE
    ═══════════════════════════════════════════════════════════════════════════

    Constants for emergent gravity (Theorem 5.2.1).
-/

/-- Physical constants structure for gravitational sector.

    **Design rationale:**
    G, c, M_P are kept in a structure because:
    1. They must satisfy consistency relations
    2. Proofs often need all three together
    3. Different unit systems can instantiate differently

    **Citation:** Theorem 5.2.1 (Emergent Metric) -/
structure GravitationalConstants where
  /-- Newton's gravitational constant G [m³/(kg·s²)] -/
  G : ℝ
  /-- G > 0 -/
  G_pos : G > 0
  /-- Speed of light c [m/s] -/
  c : ℝ
  /-- c > 0 -/
  c_pos : c > 0
  /-- Planck mass M_P [energy units] -/
  M_P : ℝ
  /-- M_P > 0 -/
  M_P_pos : M_P > 0

namespace GravitationalConstants

/-- The gravitational coupling κ = 8πG/c⁴.

    This sets the strength of the metric perturbation from stress-energy.

    **Citation:** Theorem 5.2.1, §1 -/
noncomputable def gravitationalCoupling (gc : GravitationalConstants) : ℝ :=
  8 * Real.pi * gc.G / gc.c^4

/-- κ > 0 (gravitational coupling is positive) -/
theorem gravitationalCoupling_pos (gc : GravitationalConstants) :
    gc.gravitationalCoupling > 0 := by
  unfold gravitationalCoupling
  apply div_pos
  · apply mul_pos
    · apply mul_pos (by norm_num : (8 : ℝ) > 0) Real.pi_pos
    · exact gc.G_pos
  · exact pow_pos gc.c_pos 4

/-- The chiral decay constant f_χ = M_P/√(8π).

    This determines Newton's constant: G = 1/(8π f_χ²)

    **Citation:** Theorem 5.2.1, §1 -/
noncomputable def chiralDecayConstant (gc : GravitationalConstants) : ℝ :=
  gc.M_P / Real.sqrt (8 * Real.pi)

/-- f_χ > 0 -/
theorem chiralDecayConstant_pos (gc : GravitationalConstants) :
    gc.chiralDecayConstant > 0 := by
  unfold chiralDecayConstant
  apply div_pos gc.M_P_pos
  apply Real.sqrt_pos.mpr
  apply mul_pos (by norm_num : (8 : ℝ) > 0) Real.pi_pos

/-- The Planck density ρ_Planck = c⁴/(8πG).

    This is the scale where metric fluctuations become order-1.

    **Citation:** Theorem 5.2.1, §10.3 -/
noncomputable def planckDensity (gc : GravitationalConstants) : ℝ :=
  gc.c^4 / (8 * Real.pi * gc.G)

/-- ρ_Planck > 0 -/
theorem planckDensity_pos (gc : GravitationalConstants) :
    gc.planckDensity > 0 := by
  unfold planckDensity
  apply div_pos
  · exact pow_pos gc.c_pos 4
  · apply mul_pos
    · apply mul_pos (by norm_num : (8 : ℝ) > 0) Real.pi_pos
    · exact gc.G_pos

/-- The chiral decay constant squared: f_χ² = M_P²/(8π) -/
theorem chiralDecayConstant_sq (gc : GravitationalConstants) :
    gc.chiralDecayConstant ^ 2 = gc.M_P ^ 2 / (8 * Real.pi) := by
  unfold chiralDecayConstant
  rw [div_pow, sq_sqrt]
  exact le_of_lt (mul_pos (by norm_num : (8:ℝ) > 0) Real.pi_pos)

/-- Key relation: 8π f_χ² = M_P² (intermediate step). -/
theorem newton_chiral_intermediate (gc : GravitationalConstants) :
    8 * Real.pi * gc.chiralDecayConstant ^ 2 = gc.M_P ^ 2 := by
  rw [chiralDecayConstant_sq]
  have h8pi_pos : 8 * Real.pi > 0 := mul_pos (by norm_num : (8:ℝ) > 0) Real.pi_pos
  have h8pi_ne : 8 * Real.pi ≠ 0 := ne_of_gt h8pi_pos
  field_simp

/-- κ · ρ_Planck = 1 (dimensionless ratio).

    When ρ = ρ_Planck, the metric perturbation h ~ κρ ~ 1.

    **Citation:** Misner, Thorne & Wheeler (1973), Gravitation, §17.4 -/
theorem kappa_planck_density_unity (gc : GravitationalConstants) :
    gc.gravitationalCoupling * gc.planckDensity = 1 := by
  unfold gravitationalCoupling planckDensity
  have hc4_ne : gc.c^4 ≠ 0 := ne_of_gt (pow_pos gc.c_pos 4)
  have h8 : (8 : ℝ) > 0 := by norm_num
  have h8piG_ne : 8 * Real.pi * gc.G ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos h8 Real.pi_pos) gc.G_pos)
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hc4_ne h8piG_ne)]
  ring

end GravitationalConstants

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 9: EXPERIMENTAL VALUES (QCD)
    ═══════════════════════════════════════════════════════════════════════════

    Measured values for comparison with predictions.
-/

/-- Experimental pion decay rate: Γ(π⁰ → γγ) = 7.72 eV.

    **Citation:** PDG 2024, π⁰ → γγ branching ratio -/
noncomputable def experimentalPionDecayRate_eV : ℝ := 7.72

/-- Uncertainty in pion decay rate: ±0.12 eV -/
noncomputable def experimentalPionDecayUncertainty_eV : ℝ := 0.12

/-- Pion decay constant f_π = 92.1 MeV (observed value).

    **Physical meaning:**
    Determines the strength of pion coupling to the axial current.
    f_π appears in the PCAC relation: ∂μA^a_μ = f_π m_π² π^a

    **Citation:** PDG 2024, f_π = 92.1 ± 0.8 MeV -/
noncomputable def f_pi_observed_MeV : ℝ := 92.1

/-- f_π > 0 -/
theorem f_pi_observed_pos : f_pi_observed_MeV > 0 := by
  unfold f_pi_observed_MeV; norm_num

/-- Uncertainty in pion decay constant: ±0.8 MeV -/
noncomputable def f_pi_uncertainty_MeV : ℝ := 0.8

/-- Lower bound of f_π: 92.1 - 0.8 = 91.3 MeV -/
noncomputable def f_pi_lower_MeV : ℝ := f_pi_observed_MeV - f_pi_uncertainty_MeV

/-- Upper bound of f_π: 92.1 + 0.8 = 92.9 MeV -/
noncomputable def f_pi_upper_MeV : ℝ := f_pi_observed_MeV + f_pi_uncertainty_MeV

/-- Physical observation radius: 0.22 fm.

    **Physical meaning:**
    Characteristic scale at which color field correlations
    transition from perturbative to non-perturbative. -/
noncomputable def observationRadius_physical : ℝ := 0.22

/-- String tension √σ observed value: 440 MeV.

    **Physical meaning:**
    The QCD string tension σ determines the linear confining potential
    between quarks: V(r) = σr at large r. √σ ≈ 440 MeV is the
    characteristic confinement scale.

    **Citation:** Lattice QCD, Bali (2001), √σ = 440 ± 20 MeV -/
noncomputable def sqrt_sigma_observed_MeV : ℝ := 440

/-- √σ > 0 -/
theorem sqrt_sigma_observed_pos : sqrt_sigma_observed_MeV > 0 := by
  unfold sqrt_sigma_observed_MeV; norm_num

/-- Predicted string tension √σ = ℏc/R_stella = 440.0 MeV.

    **Derivation:**
    √σ = ℏc/R_stella = 197.327/0.44847 = 440.0 MeV

    This matches the observed value exactly by construction,
    as R_stella is determined from √σ_observed.

    **Citation:** Proposition 0.0.17j -/
noncomputable def sqrt_sigma_predicted_MeV : ℝ := hbar_c_MeV_fm / R_stella_fm

/-- √σ_predicted > 0 -/
theorem sqrt_sigma_predicted_pos : sqrt_sigma_predicted_MeV > 0 := by
  unfold sqrt_sigma_predicted_MeV
  exact div_pos hbar_c_pos R_stella_pos

/-- String tension √σ in GeV (for high-energy calculations) -/
noncomputable def sqrt_sigma_GeV : ℝ := 0.440

/-- Uncertainty in √σ: ±30 MeV (≈ ±0.030 GeV) -/
noncomputable def sqrt_sigma_uncertainty_GeV : ℝ := 0.030

/-- Internal frequency ω = √σ/(N_c-1) = 220 MeV.

    **Physical meaning:**
    The internal frequency of the phase-locked rotating condensate.
    Derived from Casimir mode partition on the Cartan torus.

    **Derivation:** ω = √σ/(N_c-1) = 440/2 = 220 MeV

    **Citation:** Proposition 0.0.17l -/
noncomputable def omega_internal_MeV : ℝ := 220

/-- ω > 0 -/
theorem omega_internal_pos : omega_internal_MeV > 0 := by
  unfold omega_internal_MeV; norm_num

/-- Chiral VEV v_χ = f_π = √σ/5 = 88 MeV (predicted value).

    **Physical meaning:**
    The vacuum expectation value of the chiral condensate.
    Equals f_π in the nonlinear sigma model parameterization.

    **Derivation:** v_χ = √σ/[(N_c-1)+(N_f²-1)] = 440/5 = 88 MeV

    **Citation:** Proposition 0.0.17m -/
noncomputable def v_chi_predicted_MeV : ℝ := 88

/-- v_χ > 0 -/
theorem v_chi_predicted_pos : v_chi_predicted_MeV > 0 := by
  unfold v_chi_predicted_MeV; norm_num

/-- Chiral coupling g_χ = 4π/9 ≈ 1.396.

    **Physical meaning:**
    The effective coupling constant for the chiral drag mechanism.

    **Citation:** Proposition 3.1.1c -/
noncomputable def g_chi : ℝ := 4 * Real.pi / 9

/-- g_χ > 0 -/
theorem g_chi_pos : g_chi > 0 := by
  unfold g_chi
  apply div_pos
  · apply mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos
  · norm_num

/-- EFT cutoff Λ = 4πf_π ≈ 1105 MeV (predicted value).

    **Physical meaning:**
    The cutoff scale for chiral perturbation theory.

    **Derivation:** Λ = 4π × f_π = 4π × 88 = 1105 MeV

    **Citation:** Proposition 0.0.17d -/
noncomputable def Lambda_eft_predicted_MeV : ℝ := 4 * Real.pi * 88

/-- Λ_EFT > 0 -/
theorem Lambda_eft_predicted_pos : Lambda_eft_predicted_MeV > 0 := by
  unfold Lambda_eft_predicted_MeV
  apply mul_pos
  · apply mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos
  · norm_num

/-- Base mass scale = √σ/18 = 24.4 MeV.

    **Physical meaning:**
    The base mass scale before helicity coupling η_f in the mass formula:
    m_f = (g_χ ω/Λ) v_χ η_f = (√σ/18) η_f

    **Derivation:** (g_χ ω/Λ) v_χ = (5/18) × (√σ/5) = √σ/18

    **Citation:** Proposition 0.0.17m, Corollary 0.0.17m.2 -/
noncomputable def base_mass_scale_MeV : ℝ := 440 / 18

/-- Base mass scale > 0 -/
theorem base_mass_scale_pos : base_mass_scale_MeV > 0 := by
  unfold base_mass_scale_MeV; norm_num

/-- Charged pion mass m_π = 139.57 MeV.

    **Physical meaning:**
    The lightest strongly-interacting particle, sets the resolution limit
    for probing hadronic structure.

    **Citation:** PDG 2024, m_π± = 139.57039 ± 0.00018 MeV -/
noncomputable def m_pi_MeV : ℝ := 139.57

/-- m_π > 0 -/
theorem m_pi_pos : m_pi_MeV > 0 := by unfold m_pi_MeV; norm_num

/-- Reduced pion Compton wavelength λ̄_π = ℏc/m_π = 1.4138 fm.

    **Physical meaning:**
    The natural QFT length scale for pion physics. -/
noncomputable def lambda_bar_pi_fm : ℝ := hbar_c_MeV_fm / m_pi_MeV

/-- λ̄_π > 0 -/
theorem lambda_bar_pi_pos : lambda_bar_pi_fm > 0 := by
  unfold lambda_bar_pi_fm
  exact div_pos hbar_c_pos m_pi_pos

/-- Regularization parameter ε = 1/2 (dimensionless, in units of R_stella).

    **Physical meaning:**
    The regularization scale in pressure functions P_c(x) = 1/(|x - x_c|² + ε²).
    Derived from self-consistency: the core size equals the observation scale.

    **Derivation:**
    ε = √σ/(2πm_π) = 440/(2π × 139.57) ≈ 0.5017 ≈ 1/2

    **Citation:** Proposition 0.0.17o -/
noncomputable def epsilon_regularization : ℝ := 1 / 2

/-- ε > 0 -/
theorem epsilon_regularization_pos : epsilon_regularization > 0 := by
  unfold epsilon_regularization; norm_num

/-- ε < 1 (well within stella boundary) -/
theorem epsilon_regularization_lt_one : epsilon_regularization < 1 := by
  unfold epsilon_regularization; norm_num

/-- Regularization parameter from physical formula: ε = √σ/(2πm_π).

    This is the formula-derived value, which gives ε ≈ 0.5017.
    The simplified value ε = 1/2 is used in practice. -/
noncomputable def epsilon_from_formula : ℝ :=
  sqrt_sigma_observed_MeV / (2 * Real.pi * m_pi_MeV)

/-- Dimensional regularization scale ε_dim = ε × R_stella ≈ 0.224 fm.

    **Physical meaning:**
    The physical core size at each vertex.

    **Derivation:**
    ε_dim = (1/2) × 0.4485 fm = 0.224 fm -/
noncomputable def epsilon_dim_fm : ℝ := epsilon_regularization * R_stella_fm

/-- ε_dim > 0 -/
theorem epsilon_dim_pos : epsilon_dim_fm > 0 := by
  unfold epsilon_dim_fm
  exact mul_pos epsilon_regularization_pos R_stella_pos

/-- Stability bound: ε < 1/√3 for positive energy curvature.

    From Theorem 0.2.3: α = 2a₀²(1 - 3ε²)/(1 + ε²)⁴ > 0 requires ε² < 1/3.

    **Citation:** Proposition 0.0.17o §3.6 -/
noncomputable def epsilon_stability_bound : ℝ := 1 / Real.sqrt 3

/-- Avogadro's number (integer approximation): 6.02 × 10²³ -/
def avogadro : ℕ := 602214076000000000000000

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 10: ELECTROWEAK CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Standard Model electroweak parameters.
-/

/-- Weak mixing angle: sin²θ_W = 0.2232 (at M_Z scale, MS-bar).

    **Physical meaning:**
    The Weinberg angle relates the electromagnetic and weak couplings:
    e = g sin θ_W = g' cos θ_W

    **Citation:** PDG 2024, sin²θ_W(M_Z) = 0.23121 ± 0.00004 (on-shell),
    0.2232 in MS-bar scheme at electroweak scale -/
noncomputable def sinSqThetaW : ℝ := 0.2232

/-- sin²θ_W > 0 -/
theorem sinSqThetaW_pos : sinSqThetaW > 0 := by
  unfold sinSqThetaW; norm_num

/-- sin²θ_W < 1 (physical constraint) -/
theorem sinSqThetaW_lt_one : sinSqThetaW < 1 := by
  unfold sinSqThetaW; norm_num

/-- cot²θ_W = (1 - sin²θ_W)/sin²θ_W ≈ 3.48 -/
noncomputable def cotSqThetaW : ℝ := (1 - sinSqThetaW) / sinSqThetaW

/-- cot²θ_W > 0 -/
theorem cotSqThetaW_pos : cotSqThetaW > 0 := by
  unfold cotSqThetaW sinSqThetaW
  apply div_pos
  · norm_num
  · norm_num

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

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 12: DERIVED CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Constants computed from base constants above.
-/

/-- Anomaly coefficient: 2N_f -/
def anomalyCoefficient : ℕ := 2 * N_f

/-- Anomaly coefficient = 6 for N_f = 3 -/
theorem anomalyCoefficient_value : anomalyCoefficient = 6 := rfl

/-- Witten-Zumino-Witten coefficient: N_c -/
def WZW_coefficient : ℕ := N_c

/-- 't Hooft fermion legs: 2N_f -/
def tHooft_fermion_legs : ℕ := 2 * N_f

/-- Confinement radius from Λ_QCD: r = ℏc/Λ_QCD -/
noncomputable def confinementRadius : ℝ := hbar_c_MeV_fm / lambdaQCD

/-- Confinement radius > 0 -/
theorem confinementRadius_pos : confinementRadius > 0 := by
  unfold confinementRadius
  exact div_pos hbar_c_pos lambdaQCD_pos

/-- Confinement radius is approximately 0.93 fm -/
theorem confinementRadius_value :
    confinementRadius = 197.327 / 213 := by
  unfold confinementRadius hbar_c_MeV_fm lambdaQCD
  rfl

/-- Dimensionless integral J = π/4 (from radial integration).

    **Physical meaning:**
    Appears in energy integrals over the stella octangula geometry.

    **Citation:** Theorem 0.2.1 (Integrability) -/
noncomputable def dimensionlessIntegralJ : ℝ := Real.pi / 4

/-- J > 0 -/
theorem dimensionlessIntegralJ_pos : dimensionlessIntegralJ > 0 := by
  unfold dimensionlessIntegralJ
  exact div_pos Real.pi_pos (by norm_num : (4:ℝ) > 0)

/-- Total mode count for phase equipartition: N_c² + N_f² -/
def total_mode_count (Nc Nf : ℕ) : ℕ := Nc * Nc + Nf * Nf

/-- Mode count for SU(3) with N_f = 2: 9 + 4 = 13 -/
theorem mode_count_su3_nf2 : total_mode_count 3 2 = 13 := rfl

/-- Mode count for SU(3) with N_f = 3: 9 + 9 = 18 -/
theorem mode_count_su3_nf3 : total_mode_count 3 3 = 18 := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 13: HOLOGRAPHIC/LATTICE CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Constants for FCC lattice spacing and holographic entropy.
    Reference: Proposition 0.0.17r
-/

/-- Order of Z₃ center of SU(3): |Z(SU(3))| = 3.

    **Physical meaning:**
    The center of SU(3) is Z₃ = {1, ω, ω²} where ω = exp(2πi/3).
    This determines the entropy per site on black hole horizons.

    **Citation:** Definition 0.1.2 -/
def Z3_center_order : ℕ := 3

/-- |Z(SU(3))| = N_c -/
theorem Z3_center_order_eq_Nc : Z3_center_order = N_c := rfl

/-- Bekenstein-Hawking factor = 4.

    **Physical meaning:**
    The factor 4 in S = A/(4ℓ_P²) arises from 1/4 = 2π/(8π)
    in Einstein's equations. Derived via Paths A (Sakharov)
    and C (Jacobson equilibrium).

    **Citation:** Proposition 0.0.17r §3.2 -/
def bekenstein_factor : ℕ := 4

/-- Hexagonal cell factor N_cell = 2.

    **Physical meaning:**
    For the (111) plane of FCC, the hexagonal unit cell
    contains effectively 2 sites.

    **Citation:** Proposition 0.0.17r §4.3 -/
def hexagonal_cell_factor : ℕ := 2

/-- FCC lattice spacing coefficient: (8/√3)·ln(3) ≈ 5.074.

    **Physical meaning:**
    The coefficient in a² = coefficient × ℓ_P² for the FCC lattice
    spacing determined by holographic self-consistency.

    **Derivation:**
    coefficient = 4 × N_cell × ln|Z(G)| / √3
                = 4 × 2 × ln(3) / √3
                = 8·ln(3)/√3 ≈ 5.074

    **Citation:** Proposition 0.0.17r §2 -/
noncomputable def fcc_lattice_coefficient : ℝ :=
  8 * Real.log 3 / Real.sqrt 3

/-- FCC lattice coefficient > 0 -/
theorem fcc_lattice_coefficient_pos : fcc_lattice_coefficient > 0 := by
  unfold fcc_lattice_coefficient
  apply div_pos
  · apply mul_pos (by norm_num : (8:ℝ) > 0)
    exact Real.log_pos (by norm_num : (1:ℝ) < 3)
  · exact Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)

/-- FCC lattice spacing ratio: a/ℓ_P = √((8/√3)·ln(3)) ≈ 2.253.

    **Citation:** Proposition 0.0.17r §4.4 -/
noncomputable def fcc_lattice_spacing_ratio : ℝ :=
  Real.sqrt fcc_lattice_coefficient

/-- a/ℓ_P > 0 -/
theorem fcc_lattice_spacing_ratio_pos : fcc_lattice_spacing_ratio > 0 := by
  unfold fcc_lattice_spacing_ratio
  exact Real.sqrt_pos.mpr fcc_lattice_coefficient_pos

/-- Logarithmic correction coefficient α = 3/2.

    **Physical meaning:**
    The coefficient in the logarithmic correction to BH entropy:
    S = A/(4ℓ_P²) - α·ln(A/ℓ_P²) + O(1)

    **Derivation:**
    α = |Z(G)| × n_zero / 2 = 3 × 1 / 2 = 3/2
    where n_zero = 1 is the number of zero modes on a sphere.

    **Citation:** Proposition 0.0.17r §8.1 -/
noncomputable def log_correction_alpha : ℝ := 3 / 2

/-- α = 3/2 (value check) -/
theorem log_correction_alpha_value : log_correction_alpha = 3 / 2 := rfl

/-- α > 0 -/
theorem log_correction_alpha_pos : log_correction_alpha > 0 := by
  unfold log_correction_alpha; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 14: NEUTRINO MIXING CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Neutrino mixing angles and related parameters from NuFIT 6.0.
    These are used in Phase 8 predictions (θ₁₃, θ₂₃ corrections).

    Reference: NuFIT 6.0 (2024), Normal Ordering
-/

/-- Wolfenstein parameter: λ = sin θ_C ≈ 0.22451.

    **Physical meaning:**
    The sine of the Cabibbo angle, governing quark mixing strength.
    In CG, derived geometrically as λ = sin(72°)/φ³.

    **Citation:** Extension 3.1.2b, PDG 2024 -/
noncomputable def wolfenstein_lambda : ℝ := 0.22451

/-- λ > 0 -/
theorem wolfenstein_lambda_pos : wolfenstein_lambda > 0 := by
  unfold wolfenstein_lambda; norm_num

/-- λ < 1 (physical constraint) -/
theorem wolfenstein_lambda_lt_one : wolfenstein_lambda < 1 := by
  unfold wolfenstein_lambda; norm_num

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

end ChiralGeometrogenesis.Constants
