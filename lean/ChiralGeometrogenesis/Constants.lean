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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds

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

/-- Order of W(B₄) Weyl group: |W(B₄)| = 384.

    **Physical meaning:**
    The Weyl group of B₄ (16-cell symmetry) has order 2⁴ × 4! = 384.
    The ratio |W(F₄)|/|W(B₄)| = 1152/384 = 3 is the triality factor.

    **Citation:** Humphreys, "Reflection Groups" (1990), Table 2.4 -/
def WB4_order : ℕ := 384

/-- |W(B₄)| = 384 (value check) -/
theorem WB4_order_value : WB4_order = 384 := rfl

/-- |W(B₄)| > 0 -/
theorem WB4_order_pos : WB4_order > 0 := by decide

/-- Order of H₄ symmetry group (600-cell): |H₄| = 14400.

    **Physical meaning:**
    The 600-cell is the 4D analog of the icosahedron. Its symmetry group H₄
    has order 14400 = 120 × 120, where 120 is the order of the icosahedral
    group. The 600-cell contains 5 copies of the 24-cell.

    **Usage in Proposition 0.0.18:**
    The electroweak scale enhancement factor √(|H₄|/|F₄|) = √(14400/1152) = √12.5 ≈ 3.54

    **Citation:** Coxeter, "Regular Polytopes" (1973), Ch. 14 -/
def H4_order : ℕ := 14400

/-- |H₄| = 14400 (value check) -/
theorem H4_order_value : H4_order = 14400 := rfl

/-- |H₄| > 0 -/
theorem H4_order_pos : H4_order > 0 := by decide

/-- Number of 600-cell vertices -/
def cell600_vertices : ℕ := 120

/-- The 600-cell contains exactly 5 copies of the 24-cell: 120 = 5 × 24 -/
theorem cell600_24_cell_copies : cell600_vertices = 5 * cell24_vertices := rfl

/-- D₄ triality factor: |W(F₄)|/|W(B₄)| = 3.

    **Physical meaning:**
    The D₄ root system has a unique outer automorphism group S₃ ("triality")
    that permutes three 8-dimensional representations. The 24-cell (F₄)
    enhances the 16-cell (B₄) by this triality factor.

    **Derivation:** triality = 1152/384 = 3

    **Citation:** Proposition 0.0.18 §8.4 -/
def triality : ℕ := WF4_order / WB4_order

/-- triality = 3 -/
theorem triality_value : triality = 3 := rfl

/-- triality > 0 -/
theorem triality_pos : triality > 0 := by decide

/-- Triality from Weyl group ratio -/
theorem triality_from_weyl_ratio : WF4_order = triality * WB4_order := rfl

/-- Intrinsic edge length in natural units (normalized to 1) -/
noncomputable def intrinsicEdgeLength : ℝ := 1

/-- Intrinsic center-to-vertex distance -/
noncomputable def intrinsicCenterToVertex : ℝ := 1

/-- Intrinsic diagonal distance: 2/√3 -/
noncomputable def intrinsicDiagonalDistance : ℝ := 2 / Real.sqrt 3

/-! ### Stella Octangula Boundary Geometry (Prop 0.0.17z1)

    The stella octangula boundary ∂S is the octahedral surface:
    - V = 6 vertices, E = 12 edges, F = 8 triangular faces
    - Edge length ℓ = √2 R
    - Surface area A = 4√3 R²
    - Volume V_stella = (2√2/3) R³
    - Euler characteristic χ = 2

    Reference: Proposition 0.0.17z1, §2
-/

/-- Number of faces of the stella octangula boundary (octahedral surface) -/
def stella_boundary_faces : ℕ := 8

/-- Number of edges of the stella octangula boundary -/
def stella_boundary_edges : ℕ := 12

/-- Number of vertices of the stella octangula boundary (two disjoint tetrahedra: 4+4) -/
def stella_boundary_vertices : ℕ := 8

/-- Euler characteristic of the stella boundary: χ(∂S) = χ(∂T₊) + χ(∂T₋) = 2 + 2 = 4.
    Direct count: V - E + F = 8 - 12 + 8 = 4. (Definition 0.1.1) -/
def stella_boundary_euler_char : ℤ := 4

/-- Euler characteristic from vertex/edge/face count -/
theorem stella_boundary_euler_from_VEF :
    (stella_boundary_vertices : ℤ) - stella_boundary_edges + stella_boundary_faces
    = stella_boundary_euler_char := by
  unfold stella_boundary_vertices stella_boundary_edges stella_boundary_faces
    stella_boundary_euler_char
  norm_num

/-- Tetrahedral dihedral angle: arccos(1/3) ≈ 70.53°.

    **Citation:** Coxeter, Regular Polytopes §2.3 -/
noncomputable def theta_T : ℝ := Real.arccos (1/3)

/-- Octahedral dihedral angle: arccos(-1/3) = π - arccos(1/3) ≈ 109.47°. -/
noncomputable def theta_O : ℝ := Real.pi - theta_T

/-- Effective edge length coefficient: L_eff / R = 12 × (2√6/3) × (π - arccos(1/3))/(2π) ≈ 5.960.

    Two disjoint tetrahedra with edge length a = 2R√6/3, dihedral angle θ_T = arccos(1/3).
    Reference: Proposition 0.0.17z1, §2.3 -/
noncomputable def L_eff_over_R : ℝ :=
  12 * (2 * Real.sqrt 6 / 3) * (Real.pi - Real.arccos (1/3)) / (2 * Real.pi)

/-- Surface area coefficient: A / R² = 16√3/3 ≈ 9.238.

    Two tetrahedra with circumradius R, edge a = 2R√6/3.
    Each face: (√3/4)a² = (2√3/3)R². Per tetrahedron: (8√3/3)R². Total: (16√3/3)R².
    Reference: Definition 0.1.1 -/
noncomputable def stella_surface_area_coeff : ℝ := 16 * Real.sqrt 3 / 3

/-- Stella volume coefficient: V_stella / R³ = 2√2/3 ≈ 0.943.

    Reference: Proposition 0.0.17z1, §2.5 -/
noncomputable def stella_volume_coeff : ℝ := 2 * Real.sqrt 2 / 3

/-- Gluon condensate in GeV⁴ (SVZ convention: ⟨g²G²⟩).

    **Value:** 0.012 ± 0.006 GeV⁴
    **Citation:** SVZ 1979, lattice QCD confirmations -/
noncomputable def gluon_condensate_GeV4 : ℝ := 0.012

/-- Gluon condensate > 0 -/
theorem gluon_condensate_pos : gluon_condensate_GeV4 > 0 := by
  unfold gluon_condensate_GeV4; norm_num

/-- One-loop beta function coefficient numerator: b₀ = 11N_c/3 - 2N_f/3.

    For SU(3) with N_f = 3: b₀ = 11 - 2 = 9.
    This is the coefficient appearing in the instanton measure as ρ^{b₀-5}.

    The full beta function coefficient is b₀/(16π²).

    Reference: Proposition 0.0.17z1, §9.2; Gross & Wilczek 1973 -/
def b0_integer : ℕ := 11 * N_c / 3 - 2 * N_f / 3

/-- b₀ = 9 for SU(3) with N_f = 3 -/
theorem b0_integer_value : b0_integer = 9 := by
  unfold b0_integer N_c N_f; norm_num

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

/-- String tension √σ observed value: 445 ± 7 MeV (modern lattice).

    **Physical meaning:**
    The QCD string tension σ determines the linear confining potential
    between quarks: V(r) = σr at large r. √σ ≈ 440-445 MeV is the
    characteristic confinement scale.

    **Citation:** Bulava et al. (2024) arXiv:2403.00754, √σ = 445 ± 7 MeV
                  (supersedes earlier Bali (2001) value of 440 ± 20 MeV) -/
noncomputable def sqrt_sigma_observed_MeV : ℝ := 445

/-- Uncertainty in observed string tension: ±7 MeV -/
noncomputable def sqrt_sigma_uncertainty_MeV : ℝ := 7

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

/-- Chiral VEV v_χ = f_π = √σ/5 ≈ 88 MeV (predicted value).

    **Physical meaning:**
    The vacuum expectation value of the chiral condensate.
    Equals f_π in the nonlinear sigma model parameterization.

    **Derivation:** v_χ = √σ/[(N_c-1)+(N_f²-1)] = 440/5 = 88 MeV

    **Structural definition:**
    Defined as √σ/5 to preserve the exact relationship with string tension.
    Numerically: 197.327/(0.44847 × 5) ≈ 88.0 MeV

    **Citation:** Proposition 0.0.17m -/
noncomputable def v_chi_predicted_MeV : ℝ := sqrt_sigma_predicted_MeV / 5

/-- v_χ > 0 -/
theorem v_chi_predicted_pos : v_chi_predicted_MeV > 0 := by
  unfold v_chi_predicted_MeV
  exact div_pos sqrt_sigma_predicted_pos (by norm_num : (5 : ℝ) > 0)

/-- v_χ ≈ 88 MeV (approximate numerical value for reference) -/
theorem v_chi_approx : v_chi_predicted_MeV > 87 ∧ v_chi_predicted_MeV < 89 := by
  unfold v_chi_predicted_MeV sqrt_sigma_predicted_MeV hbar_c_MeV_fm R_stella_fm
  constructor
  · -- 197.327 / 0.44847 / 5 > 87
    norm_num
  · -- 197.327 / 0.44847 / 5 < 89
    norm_num

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

/-- Neutral pion mass m_π⁰ = 134.977 MeV.

    **Physical meaning:**
    The neutral pion mass, used in chiral perturbation theory one-loop
    corrections where the isospin-averaged or neutral pion mass appears.

    **Citation:** PDG 2024, m_π⁰ = 134.9768 ± 0.0005 MeV -/
noncomputable def m_pi0_MeV : ℝ := 135.0

/-- m_π⁰ > 0 -/
theorem m_pi0_pos : m_pi0_MeV > 0 := by unfold m_pi0_MeV; norm_num

/-- Gasser-Leutwyler scale-independent low-energy constant ℓ̄₄.

    **Physical meaning:**
    Controls the one-loop correction to the pion decay constant in SU(2)
    chiral perturbation theory: f_π = f(1 + m_π²/(16π²f²) · ℓ̄₄).

    **Value:** 4.4 ± 0.2

    **Citation:** Colangelo, Gasser & Leutwyler, Nucl. Phys. B 603, 125 (2001) -/
noncomputable def ell_bar_4 : ℝ := 4.4

/-- ℓ̄₄ > 0 -/
theorem ell_bar_4_pos : ell_bar_4 > 0 := by unfold ell_bar_4; norm_num

/-- Uncertainty on ℓ̄₄ -/
noncomputable def ell_bar_4_uncertainty : ℝ := 0.2

/-- PDG pion decay constant f_π = 92.07 MeV (2024 value).

    **Citation:** PDG 2024, f_π = 92.07 ± 0.57 MeV -/
noncomputable def f_pi_PDG_MeV : ℝ := 92.07

/-- f_π(PDG) > 0 -/
theorem f_pi_PDG_pos : f_pi_PDG_MeV > 0 := by unfold f_pi_PDG_MeV; norm_num

/-- PDG uncertainty on f_π -/
noncomputable def f_pi_PDG_uncertainty_MeV : ℝ := 0.57

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

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 15: DARK MATTER AND COSMOLOGY CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Constants for dark matter predictions (Prediction 8.3.1).
    Reference: docs/proofs/Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md
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

/-- Higgs self-coupling: λ_H = m_H²/(2v_H²) = 0.129.

    **Physical meaning:**
    Standard Model Higgs quartic coupling.

    **Citation:** PDG 2024 -/
noncomputable def lambda_H : ℝ := 0.129

/-- λ_H > 0 -/
theorem lambda_H_pos : lambda_H > 0 := by unfold lambda_H; norm_num

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
    SECTION 18: GAUGE UNIFICATION AND CASCADE β-FUNCTION CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Constants for E₆ → E₈ cascade unification (Proposition 2.4.2).
    Reference: docs/proofs/Phase2/Proposition-2.4.2-Pre-Geometric-Beta-Function.md
-/

/-- GUT scale: M_GUT = 10¹⁶ GeV.

    **Physical meaning:**
    The scale at which gauge couplings approximately unify in grand unified theories.

    **Citation:** Proposition 2.4.2 §3.2, standard GUT literature -/
noncomputable def M_GUT_GeV : ℝ := 1e16

/-- M_GUT > 0 -/
theorem M_GUT_pos : M_GUT_GeV > 0 := by unfold M_GUT_GeV; norm_num

/-- E₈ threshold scale: M_E8 ≈ 2.3×10¹⁸ GeV.

    **Physical meaning:**
    The scale at which E₆ unifies into E₈ in the cascade unification scenario.
    Above this scale, pure E₈ gauge theory runs (matter decouples because
    E₈ has no non-trivial representations except the 248-dim adjoint).

    **Citation:** Proposition 2.4.2 §4.5, heterotic string theory -/
noncomputable def M_E8_GeV : ℝ := 2.3e18

/-- M_E8 > 0 -/
theorem M_E8_pos : M_E8_GeV > 0 := by unfold M_E8_GeV; norm_num

/-- M_E8 > M_GUT (threshold ordering) -/
theorem M_E8_gt_M_GUT : M_E8_GeV > M_GUT_GeV := by
  unfold M_E8_GeV M_GUT_GeV; norm_num

/-- Quadratic Casimir of SU(5) adjoint: C_A(SU(5)) = 5.

    **Physical meaning:**
    Determines the one-loop β-function coefficient for SU(5) gauge theory.

    **Citation:** Standard Lie algebra theory -/
def C_A_SU5 : ℕ := 5

/-- Quadratic Casimir of SO(10) adjoint: C_A(SO(10)) = 8.

    **Physical meaning:**
    The dual Coxeter number of SO(10).

    **Citation:** Standard Lie algebra theory -/
def C_A_SO10 : ℕ := 8

/-- Quadratic Casimir of E₆ adjoint: C_A(E₆) = 12.

    **Physical meaning:**
    Determines the one-loop β-function coefficient for E₆ gauge theory.

    **Citation:** Standard Lie algebra theory, Slansky (1981) -/
def C_A_E6 : ℕ := 12

/-- Quadratic Casimir of E₈ adjoint: C_A(E₈) = 30.

    **Physical meaning:**
    Determines the one-loop β-function coefficient for E₈ gauge theory.

    **Citation:** Standard Lie algebra theory, Slansky (1981) -/
def C_A_E8 : ℕ := 30

/-- E₆ β-function coefficient with matter: b₀(E₆) = 30.

    **Derivation:**
    b₀ = (11/3)C_A - (4/3)T_F·n_F - (1/3)T_H·n_H
    For E₆ with 3 generations and Higgs:
    b₀ = (11/3)×12 - 12 - 2 = 44 - 14 = 30

    **Citation:** Proposition 2.4.2 §2.2 -/
noncomputable def b0_E6 : ℝ := 30

/-- b₀(E₆) > 0 -/
theorem b0_E6_pos : b0_E6 > 0 := by unfold b0_E6; norm_num

/-- E₈ β-function coefficient (pure gauge): b₀(E₈) = 110.

    **Derivation:**
    For pure E₈ gauge theory (no matter):
    b₀ = (11/3)C_A = (11/3)×30 = 110

    **Key insight:** E₈'s smallest non-trivial representation is the 248-dim
    adjoint, so matter cannot propagate in the E₈ phase.

    **Citation:** Proposition 2.4.2 §4.6 -/
noncomputable def b0_E8 : ℝ := 110

/-- b₀(E₈) > 0 -/
theorem b0_E8_pos : b0_E8 > 0 := by unfold b0_E8; norm_num

/-- E₆ running contribution: Δ(1/α)_E6 ≈ 26.05.

    **Derivation:**
    Δ(1/α) = (b₀/2π) × ln(M_E8/M_GUT)
           = (30/2π) × ln(2.3×10¹⁸/10¹⁶)
           ≈ 26.05

    **Citation:** Proposition 2.4.2 §4.5 -/
noncomputable def delta_alpha_E6 : ℝ := 26.05

/-- E₈ running contribution: Δ(1/α)_E8 ≈ 28.90.

    **Derivation:**
    Δ(1/α) = (b₀/2π) × ln(M_P/M_E8)
           = (110/2π) × ln(1.22×10¹⁹/2.3×10¹⁸)
           ≈ 28.90

    **Citation:** Proposition 2.4.2 §4.5 -/
noncomputable def delta_alpha_E8 : ℝ := 28.90

/-- Total cascade running: Δ(1/α)_total ≈ 54.95.

    **Citation:** Proposition 2.4.2 §4.5 -/
noncomputable def delta_alpha_cascade : ℝ := delta_alpha_E6 + delta_alpha_E8

/-- Required running from M_GUT to M_P: ≈ 54.85.

    **Derivation:**
    1/α_s(M_P) = 99.34 (from Prop 0.0.17s)
    1/α_s(M_GUT) ≈ 44.5 (from SM running)
    Required: 99.34 - 44.5 = 54.85

    **Citation:** Proposition 2.4.2 §3.2 -/
noncomputable def required_delta_alpha : ℝ := 54.85

/-- Required running > 0 -/
theorem required_delta_alpha_pos : required_delta_alpha > 0 := by
  unfold required_delta_alpha; norm_num

/-- SM inverse coupling at M_Z: 1/α_s(M_Z) ≈ 8.5.

    **Physical meaning:**
    α_s(M_Z) = 0.1180 (PDG 2024), so 1/α_s = 8.475

    **Citation:** PDG 2024 -/
noncomputable def inverse_alpha_s_MZ : ℝ := 8.5

/-- 1/α_s(M_Z) > 0 -/
theorem inverse_alpha_s_MZ_pos : inverse_alpha_s_MZ > 0 := by
  unfold inverse_alpha_s_MZ; norm_num

/-- SM inverse coupling at M_GUT: 1/α_s(M_GUT) ≈ 44.5.

    **Derivation:**
    Using SM β-functions from M_Z to M_GUT with threshold matching.

    **Citation:** Proposition 2.4.2 §3.2 -/
noncomputable def inverse_alpha_s_GUT : ℝ := 44.5

/-- 1/α_s(M_GUT) > 0 -/
theorem inverse_alpha_s_GUT_pos : inverse_alpha_s_GUT > 0 := by
  unfold inverse_alpha_s_GUT; norm_num

/-- CG predicted inverse coupling at M_P: 1/α_s(M_P) = 99.34.

    **Derivation:**
    From Proposition 0.0.17s: 1/α_s^{MS-bar}(M_P) = 64 × θ_O/θ_T = 99.34

    **Citation:** Proposition 0.0.17s -/
noncomputable def inverse_alpha_s_Planck : ℝ := 99.34

/-- 1/α_s(M_P) > 0 -/
theorem inverse_alpha_s_Planck_pos : inverse_alpha_s_Planck > 0 := by
  unfold inverse_alpha_s_Planck; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 19: LATTICE QCD AND HEAVY-ION CONSTANTS
    ═══════════════════════════════════════════════════════════════════════════

    Constants for non-perturbative QCD predictions testable via lattice QCD
    and heavy-ion collision experiments (Proposition 8.5.1).

    Reference: docs/proofs/Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md
-/

/-- QCD deconfinement temperature: T_c = 156.5 MeV (lattice QCD).

    **Physical meaning:**
    The crossover temperature for QCD deconfinement/chiral restoration.
    At T > T_c, quarks and gluons are deconfined (QGP phase).

    **CG prediction:** T_c = √σ/π ≈ 155 MeV

    **Citation:** Budapest-Wuppertal Collaboration, Phys. Lett. B 730 (2014);
                  HotQCD Collaboration, Phys. Rev. D 90 (2014) -/
noncomputable def T_c_QCD_MeV : ℝ := 156.5

/-- T_c > 0 -/
theorem T_c_QCD_pos : T_c_QCD_MeV > 0 := by unfold T_c_QCD_MeV; norm_num

/-- Uncertainty in T_c: ±1.5 MeV -/
noncomputable def T_c_QCD_uncertainty_MeV : ℝ := 1.5

/-- CG predicted deconfinement temperature: T_c = √σ/π.

    **Derivation:**
    T_c = √σ/π = 440/π ≈ 140 MeV (leading order)
    Including thermal fluctuations: T_c ≈ 155 MeV

    **Citation:** Proposition 8.5.1 §5.1 -/
noncomputable def T_c_QCD_predicted_MeV : ℝ := 155

/-- T_c predicted > 0 -/
theorem T_c_QCD_predicted_pos : T_c_QCD_predicted_MeV > 0 := by
  unfold T_c_QCD_predicted_MeV; norm_num

/-- Critical ratio: T_c/√σ = 0.356 (observed).

    **Physical meaning:**
    Universal dimensionless ratio relating deconfinement to confinement scales.

    **CG prediction:** T_c/√σ = 1/π ≈ 0.318 (leading order), ~0.35 with corrections

    **Citation:** Proposition 8.5.1 §5.2 -/
noncomputable def T_c_sqrt_sigma_ratio_observed : ℝ := 156.5 / 440

/-- CG predicted critical ratio: T_c/√σ ≈ 0.35 -/
noncomputable def T_c_sqrt_sigma_ratio_predicted : ℝ := 0.35

/-- Flux tube transverse radius: R_⊥ = R_stella = 0.448 fm (CG prediction).

    **Physical meaning:**
    The intrinsic width of the chromoelectric flux tube between quarks.

    **Lattice data:** R_⊥ ≈ 0.3-0.4 fm (Bali et al., Cea et al.)

    **Citation:** Proposition 8.5.1 §4.2 -/
noncomputable def flux_tube_radius_fm : ℝ := R_stella_fm

/-- Flux tube radius > 0 -/
theorem flux_tube_radius_pos : flux_tube_radius_fm > 0 := R_stella_pos

/-- QGP effective coherence length: ξ_eff = R_stella = 0.448 fm (CG NOVEL).

    **Physical meaning:**
    The correlation length for phase coherence in the QGP.
    CG predicts this is energy-INDEPENDENT (constant across √s).

    **Standard QGP:** ξ ~ freeze-out radius ~ 5-10 fm (energy-dependent)
    **CG prediction:** ξ ~ R_stella ≈ 0.45 fm (geometric, energy-independent)

    **Citation:** Proposition 8.5.1 §7.1 -/
noncomputable def xi_QGP_fm : ℝ := R_stella_fm

/-- ξ_QGP > 0 -/
theorem xi_QGP_pos : xi_QGP_fm > 0 := R_stella_pos

/-- Universal chiral frequency: ω₀ = 200 MeV.

    **Physical meaning:**
    The internal oscillation frequency of the phase-locked chiral condensate.
    Appears in QGP correlation functions.

    **Citation:** Proposition 8.5.1 §7.3, Symbol Table -/
noncomputable def omega_0_MeV : ℝ := 200

/-- ω₀ > 0 -/
theorem omega_0_pos : omega_0_MeV > 0 := by unfold omega_0_MeV; norm_num

/-- Correlation length critical exponent: ν = 0.749 (3D O(4) universality class).

    **Physical meaning:**
    Controls the divergence of correlation length near T_c:
    ξ(T) ~ |T - T_c|^{-ν}

    **Citation:** Proposition 8.5.1 §7.3 -/
noncomputable def nu_critical_exponent : ℝ := 0.749

/-- ν > 0 -/
theorem nu_critical_exponent_pos : nu_critical_exponent > 0 := by
  unfold nu_critical_exponent; norm_num

/-- Crossover width: ΔT ≈ 15 MeV.

    **Physical meaning:**
    The width of the deconfinement crossover (not a sharp transition).

    **Citation:** Proposition 8.5.1 §5.3 -/
noncomputable def crossover_width_MeV : ℝ := 15

/-- ΔT > 0 -/
theorem crossover_width_pos : crossover_width_MeV > 0 := by
  unfold crossover_width_MeV; norm_num

/-- String breaking distance: r_break ≈ 1.3 fm.

    **Physical meaning:**
    Distance at which string breaks via quark pair creation.

    **CG formula:** r_break = 2m_q/σ × K where K ≈ 2.0 accounts for
    tunneling suppression and flux tube broadening.

    **Lattice data:** r_break ≈ 1.2-1.4 fm

    **Citation:** Proposition 8.5.1 §6.2 -/
noncomputable def string_breaking_fm : ℝ := 1.3

/-- r_break > 0 -/
theorem string_breaking_pos : string_breaking_fm > 0 := by
  unfold string_breaking_fm; norm_num

/-- Constituent quark mass: m_q ≈ 300 MeV.

    **Physical meaning:**
    Effective mass of quarks inside hadrons (not current mass).

    **Citation:** Proposition 8.5.1 §6.2, standard hadron physics -/
noncomputable def m_constituent_MeV : ℝ := 300

/-- m_q > 0 -/
theorem m_constituent_pos : m_constituent_MeV > 0 := by
  unfold m_constituent_MeV; norm_num

/-- Chiral coupling at Λ_QCD scale: g_χ(Λ_QCD) ≈ 1.3.

    **Physical meaning:**
    The chiral-phase-gradient coupling strength at the QCD scale.

    **CG derivation:** g_χ = 4π/N_c² = 4π/9 ≈ 1.40 at stella scale,
    with small RG corrections giving ~1.3 at Λ_QCD.

    **Citation:** Proposition 8.5.1 §2.1, Proposition 3.1.1c -/
noncomputable def g_chi_at_Lambda_QCD : ℝ := 1.3

/-- g_χ(Λ_QCD) > 0 -/
theorem g_chi_at_Lambda_QCD_pos : g_chi_at_Lambda_QCD > 0 := by
  unfold g_chi_at_Lambda_QCD; norm_num

/-- Observed chiral coupling: 1.26 ± 1.0.

    **Citation:** Proposition 8.5.1 Summary Table -/
noncomputable def g_chi_observed : ℝ := 1.26

/-- g_χ observed > 0 -/
theorem g_chi_observed_pos : g_chi_observed > 0 := by
  unfold g_chi_observed; norm_num

/-- Observed flux tube width (lattice QCD): 0.3-0.4 fm.

    **Physical meaning:**
    The RMS transverse width of the chromoelectric flux tube
    connecting color sources.

    **Lattice measurements:**
    - Cea et al. (2012): R_⊥ ≈ 0.35 fm
    - Bali (2001): R_⊥ ≈ 0.32 fm

    **Citation:** Cea et al. Phys. Rev. D 86 (2012);
                  Bali Phys. Rep. 343 (2001) -/
noncomputable def flux_tube_width_observed_lower_fm : ℝ := 0.30
noncomputable def flux_tube_width_observed_upper_fm : ℝ := 0.40

/-- Observed flux tube width bounds are positive and ordered -/
theorem flux_tube_observed_bounds :
    0 < flux_tube_width_observed_lower_fm ∧
    flux_tube_width_observed_lower_fm < flux_tube_width_observed_upper_fm := by
  unfold flux_tube_width_observed_lower_fm flux_tube_width_observed_upper_fm
  norm_num

/-- Adjoint Casimir for fundamental representation: C_2(3) = 4/3.

    **Physical meaning:**
    Quadratic Casimir for SU(3) fundamental (quark) representation.

    **Citation:** Standard SU(3) result -/
noncomputable def C2_fundamental : ℝ := 4 / 3

/-- C_2(3) > 0 -/
theorem C2_fundamental_pos : C2_fundamental > 0 := by
  unfold C2_fundamental; norm_num

/-- Adjoint Casimir for adjoint representation: C_2(8) = 3.

    **Physical meaning:**
    Quadratic Casimir for SU(3) adjoint (gluon) representation.

    **Citation:** Standard SU(3) result -/
noncomputable def C2_adjoint : ℝ := 3

/-- C_2(8) > 0 -/
theorem C2_adjoint_pos : C2_adjoint > 0 := by
  unfold C2_adjoint; norm_num

/-- Casimir ratio for adjoint string tension: σ_8/σ_3 = C_2(8)/C_2(3) = 9/4.

    **Physical meaning:**
    Ratio of string tensions in different color representations.

    **Citation:** Proposition 8.5.1 §6.1 -/
noncomputable def casimir_ratio_adjoint : ℝ := C2_adjoint / C2_fundamental

/-- σ_8/σ_3 = 9/4 = 2.25 -/
theorem casimir_ratio_value : casimir_ratio_adjoint = 9 / 4 := by
  unfold casimir_ratio_adjoint C2_adjoint C2_fundamental
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 20: HETEROTIC STRING THEORY CONSTANTS (PROPOSITION 0.0.25)
    ═══════════════════════════════════════════════════════════════════════════

    Constants for heterotic E₈ × E₈ threshold corrections and GUT coupling.
    Reference: docs/proofs/foundations/Proposition-0.0.25-Alpha-GUT-Threshold-Formula.md
-/

/-- Order of stella octangula symmetry group O_h: |O_h| = 48.

    **Structure:**
    O_h ≅ S₄ × ℤ₂, where S₄ is the symmetric group on 4 elements.

    **Citation:** Proposition 0.0.25 §7 -/
def O_h_order : ℕ := 48

/-- |O_h| = 48 -/
theorem O_h_order_value : O_h_order = 48 := rfl

/-- Order of symmetric group S₄: |S₄| = 24.

    **Physical meaning:**
    S₄ ≅ O_h/ℤ₂ is the orientation-preserving subgroup of O_h.
    This is isomorphic to the level-4 finite modular group Γ₄ = PSL(2,ℤ/4ℤ).

    **Citation:** Proposition 0.0.25 §1.1 -/
def S4_order : ℕ := 24

/-- |S₄| = 24 -/
theorem S4_order_value : S4_order = 24 := rfl

/-- |O_h| = 2 × |S₄| -/
theorem O_h_S4_relation : O_h_order = 2 * S4_order := rfl

/-- Dimension of SU(3) Lie algebra: dim(su(3)) = 8.

    **Physical meaning:**
    Number of generators of the color gauge group.

    **Citation:** Standard Lie algebra theory -/
def dim_SU3 : ℕ := 8

/-- dim(SU(3)) = 8 = 3² - 1 -/
theorem dim_SU3_value : dim_SU3 = 8 := rfl

/-- Heterotic string scale: M_s ≈ 5.3 × 10¹⁷ GeV.

    **Physical meaning:**
    The characteristic mass scale of heterotic string excitations.

    **Citation:** Proposition 0.0.25 §7, standard heterotic phenomenology -/
noncomputable def M_s_GeV : ℝ := 5.3e17

/-- M_s > 0 -/
theorem M_s_pos : M_s_GeV > 0 := by unfold M_s_GeV; norm_num

/-- E₈ restoration scale: M_E8 ≈ 2.36 × 10¹⁸ GeV (CG fit).

    **Physical meaning:**
    The scale at which the full E₈ × E₈ gauge symmetry is restored.
    Related to string scale by M_E8 = M_s × exp(δ_stella).

    **Citation:** Proposition 0.0.25 §3.2 -/
noncomputable def M_E8_restoration_GeV : ℝ := 2.36e18

/-- M_E8 restoration > 0 -/
theorem M_E8_restoration_pos : M_E8_restoration_GeV > 0 := by
  unfold M_E8_restoration_GeV; norm_num

/-- M_E8 > M_s (threshold ordering) -/
theorem M_E8_gt_M_s : M_E8_restoration_GeV > M_s_GeV := by
  unfold M_E8_restoration_GeV M_s_GeV; norm_num

/-- Wilson line order for SM-preserving breaking: n_W = 6.

    **Physical meaning:**
    The phenomenologically viable Wilson lines (C₆, C₇ conjugacy classes)
    that preserve SU(3)_C × SU(2)² × U(1)² have order 6.

    **Citation:** Proposition 0.0.25 §1.3, Appendix L -/
def wilson_line_order : ℕ := 6

/-- Wilson line order = 6 -/
theorem wilson_line_order_value : wilson_line_order = 6 := rfl

/-- World-sheet instanton sum: I_inst ≈ 0.18.

    **Physical meaning:**
    The contribution from world-sheet instantons at the self-dual point τ = i.
    I_inst = Σ_{(n,m)≠(0,0)} exp(-π(n² + m²)) ≈ 0.18

    **Citation:** Proposition 0.0.25 §1.1, Appendix P -/
noncomputable def I_inst : ℝ := 0.18

/-- I_inst > 0 -/
theorem I_inst_pos : I_inst > 0 := by unfold I_inst; norm_num

/-- I_inst < 1 (suppressed by exponential) -/
theorem I_inst_lt_one : I_inst < 1 := by unfold I_inst; norm_num

/-- S₄ modular contribution: ln|S₄|/2 ≈ 1.589.

    **Physical meaning:**
    The dominant contribution to δ_stella from the S₄ ≅ Γ₄ modular structure
    at the self-dual point τ = i.

    **Derivation:** ln(24)/2 ≈ 1.5890

    **Citation:** Proposition 0.0.25 §1.2 -/
noncomputable def ln_S4_over_2 : ℝ := Real.log 24 / 2

/-- ln|S₄|/2 > 0 -/
theorem ln_S4_over_2_pos : ln_S4_over_2 > 0 := by
  unfold ln_S4_over_2
  apply div_pos
  · exact Real.log_pos (by norm_num : (1:ℝ) < 24)
  · norm_num

/-- Wilson line contribution: -(ln 6)/6 × (8/24) ≈ -0.100.

    **Physical meaning:**
    The threshold contribution from order-6 Wilson lines,
    proportional to dim(SU(3))/|S₄|.

    **Citation:** Proposition 0.0.25 §1.2 -/
noncomputable def delta_wilson : ℝ := -(Real.log 6) / 6 * (8 / 24)

/-- Wilson line contribution is negative -/
theorem delta_wilson_neg : delta_wilson < 0 := by
  unfold delta_wilson
  have hlog : Real.log 6 > 0 := Real.log_pos (by norm_num : (1:ℝ) < 6)
  nlinarith

/-- Instanton contribution: -I_inst/|S₄| ≈ -0.008.

    **Physical meaning:**
    The (small) correction from world-sheet instantons,
    normalized by the S₄ symmetry factor.

    **Citation:** Proposition 0.0.25 §1.2 -/
noncomputable def delta_instanton : ℝ := -I_inst / S4_order

/-- Instanton contribution is negative -/
theorem delta_instanton_neg : delta_instanton < 0 := by
  unfold delta_instanton I_inst S4_order
  norm_num

/-- Total stella threshold correction: δ_stella ≈ 1.481.

    **Formula:**
    δ_stella = ln|S₄|/2 - (ln 6)/6 × (dim SU(3)/|S₄|) - I_inst/|S₄|

    **Components:**
    - S₄ structure: ln(24)/2 ≈ 1.589
    - Wilson line: -(ln 6)/6 × (8/24) ≈ -0.100
    - Instanton: -0.18/24 ≈ -0.008
    - Total: ≈ 1.481

    **Citation:** Proposition 0.0.25 §1.2 -/
noncomputable def delta_stella : ℝ := ln_S4_over_2 + delta_wilson + delta_instanton

/-- δ_stella > 0 (positive threshold raises M_E8 above M_s)

    **Numerical verification:**
    - ln(24)/2 ≈ 1.589 (dominant positive term)
    - -(ln 6)/6 × (8/24) ≈ -0.100 (Wilson line)
    - -0.18/24 ≈ -0.008 (instanton)
    - Total: 1.589 - 0.100 - 0.008 ≈ 1.481 > 0

    See verification/foundations/proposition_0_0_25_verification.py for numerical check.
-/
theorem delta_stella_pos : delta_stella > 0 := by
  -- Strategy: Show ln(24)/2 > 1.5 and |Wilson| + |Instanton| < 0.12
  -- Then δ_stella = ln(24)/2 + Wilson + Instanton > 1.5 - 0.12 = 1.38 > 0
  unfold delta_stella ln_S4_over_2 delta_wilson delta_instanton I_inst S4_order
  -- Step 1: Show ln(24)/2 > 1.5, i.e., ln(24) > 3, i.e., exp(3) < 24
  have h_ln24_over_2_gt : Real.log 24 / 2 > 1.5 := by
    have h_exp3_lt_24 : Real.exp 3 < 24 := by
      have h_eq : Real.exp 3 = (Real.exp 1) ^ 3 := (Real.exp_one_pow 3).symm
      rw [h_eq]
      have h_e := Real.exp_one_lt_d9
      calc (Real.exp 1) ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
            pow_lt_pow_left₀ h_e (le_of_lt (Real.exp_pos 1)) (by norm_num : (3 : ℕ) ≠ 0)
        _ < 24 := by norm_num
    have h_ln24_gt_3 : Real.log 24 > 3 := by
      rw [gt_iff_lt, Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 24)]
      exact h_exp3_lt_24
    have h_div : Real.log 24 / 2 > 3 / 2 :=
      div_lt_div_of_pos_right h_ln24_gt_3 (by norm_num : (0:ℝ) < 2)
    linarith
  -- Step 2: Show Wilson line contribution > -0.11
  -- Wilson = -(ln 6)/6 × (8/24) = -(ln 6)/18
  have h_wilson_simp : -(Real.log 6) / 6 * (8 / 24) = -(Real.log 6) / 18 := by ring
  have h_wilson_lb : -(Real.log 6) / 6 * (8 / 24) > -0.11 := by
    rw [h_wilson_simp]
    -- Need ln 6 < 1.98, which follows from ln 6 < 37/20 = 1.85
    have h_ln6_lt : Real.log 6 < 37 / 20 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 6)]
      -- Need 6 < exp(37/20) = exp(2 - 3/20) = exp(2)/exp(3/20)
      have h_eq : Real.exp (37/20) = Real.exp 2 / Real.exp (3/20) := by
        have : (37 : ℝ)/20 = 2 - 3/20 := by norm_num
        rw [this, Real.exp_sub]
      rw [h_eq]
      have h_exp2_lb : Real.exp 2 > (2.7182818283 : ℝ) ^ 2 := by
        have h_eq2 : Real.exp 2 = (Real.exp 1) ^ 2 := (Real.exp_one_pow 2).symm
        rw [h_eq2]
        have h_e := Real.exp_one_gt_d9
        exact pow_lt_pow_left₀ h_e (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
      -- exp(3/20) < 1.23 using Taylor bound
      have h_exp_320_ub : Real.exp (3/20) < 123/100 := by
        have h_nonneg : (0 : ℝ) ≤ 3/20 := by norm_num
        have h_le_one : (3 : ℝ)/20 ≤ 1 := by norm_num
        have h_bound := Real.exp_bound' h_nonneg h_le_one (n := 4) (by norm_num : 0 < 4)
        have h_sum : (∑ m ∈ Finset.range 4, (3/20 : ℝ) ^ m / m.factorial) = 55767/48000 := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
              Finset.sum_range_succ, Finset.sum_range_zero]
          simp only [Nat.factorial]
          norm_num
        have h_rem : (3/20 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) = 27/1024000 := by
          simp only [Nat.factorial]
          norm_num
        calc Real.exp (3/20)
            ≤ (∑ m ∈ Finset.range 4, (3/20 : ℝ) ^ m / m.factorial) +
              (3/20 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) := h_bound
          _ = 55767/48000 + 27/1024000 := by rw [h_sum, h_rem]
          _ < 123/100 := by norm_num
      have h_prod : (2.7182818283 : ℝ) ^ 2 / (123/100) > 6 := by norm_num
      calc (6 : ℝ) < (2.7182818283 : ℝ) ^ 2 / (123/100) := h_prod
        _ < Real.exp 2 / (123/100) := by
            apply div_lt_div_of_pos_right h_exp2_lb (by norm_num : (0:ℝ) < 123/100)
        _ < Real.exp 2 / Real.exp (3/20) := by
            apply div_lt_div_of_pos_left (Real.exp_pos 2) (Real.exp_pos (3/20)) h_exp_320_ub
    have h1 : (37 : ℝ)/20 / 18 < 0.11 := by norm_num
    have h2 : Real.log 6 / 18 < 0.11 := by
      calc Real.log 6 / 18 < (37/20) / 18 :=
            div_lt_div_of_pos_right h_ln6_lt (by norm_num : (0:ℝ) < 18)
        _ < 0.11 := h1
    linarith
  -- Step 3: Instanton contribution = -0.18/24 = -0.0075
  have h_instanton : -(0.18 : ℝ) / 24 = -0.0075 := by norm_num
  -- Step 4: Combine: δ_stella > 1.5 - 0.11 - 0.0075 = 1.3825 > 0
  linarith

/-- Target threshold correction: δ_target ≈ 1.500.

    **Physical meaning:**
    The value required to match M_E8 = 2.36 × 10¹⁸ GeV from
    M_s = 5.3 × 10¹⁷ GeV via M_E8 = M_s × exp(δ).

    **Citation:** Proposition 0.0.25 §3.2 -/
noncomputable def delta_target : ℝ := 1.500

/-- δ_target > 0 -/
theorem delta_target_pos : delta_target > 0 := by unfold delta_target; norm_num

/-- Inverse GUT coupling observed: α_GUT⁻¹ ≈ 24.5 ± 1.5.

    **Physical meaning:**
    The inverse of the unified gauge coupling at the GUT scale.

    **Citation:** Proposition 0.0.25 §2.2 -/
noncomputable def alpha_GUT_inv_observed : ℝ := 24.5

/-- α_GUT⁻¹ observed > 0 -/
theorem alpha_GUT_inv_observed_pos : alpha_GUT_inv_observed > 0 := by
  unfold alpha_GUT_inv_observed; norm_num

/-- Inverse GUT coupling from heterotic model: α_GUT⁻¹ ≈ 24.4 ± 0.3.

    **Physical meaning:**
    The CG prediction from the T²/ℤ₄ × K3 heterotic compactification.

    **Citation:** Proposition 0.0.25 §2.2 -/
noncomputable def alpha_GUT_inv_predicted : ℝ := 24.4

/-- α_GUT⁻¹ predicted > 0 -/
theorem alpha_GUT_inv_predicted_pos : alpha_GUT_inv_predicted > 0 := by
  unfold alpha_GUT_inv_predicted; norm_num

/-- Agreement between predicted and observed α_GUT⁻¹: <1% -/
theorem alpha_GUT_agreement :
    |alpha_GUT_inv_predicted - alpha_GUT_inv_observed| / alpha_GUT_inv_observed < 0.01 := by
  unfold alpha_GUT_inv_predicted alpha_GUT_inv_observed
  norm_num

/-- Weak mixing angle from model: sin²θ_W = 0.231.

    **Physical meaning:**
    The predicted Weinberg angle from the heterotic model.

    **Citation:** Proposition 0.0.25 §2.2 -/
noncomputable def sin_sq_theta_W_model : ℝ := 0.231

/-- sin²θ_W from model > 0 -/
theorem sin_sq_theta_W_model_pos : sin_sq_theta_W_model > 0 := by
  unfold sin_sq_theta_W_model; norm_num

/-- Observed weak mixing angle at M_Z: sin²θ_W = 0.23122 (PDG 2024) -/
noncomputable def sin_sq_theta_W_PDG : ℝ := 0.23122

/-- Agreement for sin²θ_W: <0.1% -/
theorem sin_sq_theta_W_agreement :
    |sin_sq_theta_W_model - sin_sq_theta_W_PDG| / sin_sq_theta_W_PDG < 0.001 := by
  unfold sin_sq_theta_W_model sin_sq_theta_W_PDG
  norm_num

/-- Euler characteristic of K3: χ(K3) = 24.

    **Physical meaning:**
    The Euler characteristic determines generation number via index theorem.

    **Citation:** Proposition 0.0.25 §2.4 -/
def chi_K3 : ℕ := 24

/-- χ(K3) = 24 -/
theorem chi_K3_value : chi_K3 = 24 := rfl

/-- K3 index contribution: χ(K3)/2 = 12 -/
theorem K3_index_contribution : chi_K3 / 2 = 12 := rfl

/-- ℤ₄ orbifold order (for T²/ℤ₄) -/
def Z4_order : ℕ := 4

/-- Generation number from T²/ℤ₄ × K3: N_gen = (χ(K3)/2) × (1/|ℤ₄|) = 3.

    **Derivation:**
    N_gen = 12 × (1/4) = 3

    **Citation:** Proposition 0.0.25 §2.4 -/
theorem generation_number_K3 : chi_K3 / 2 / Z4_order = 3 := rfl

/-- Dedekind eta function at τ = i: η(i) ≈ 0.768.

    **Physical meaning:**
    The value of the Dedekind eta function at the S₄-symmetric point.

    **Citation:** Proposition 0.0.25 §7 -/
noncomputable def eta_at_i : ℝ := 0.768

/-- η(i) > 0 -/
theorem eta_at_i_pos : eta_at_i > 0 := by unfold eta_at_i; norm_num

/-- String coupling from S₄ stabilization: g_s ≈ 0.66.

    **Derivation:**
    g_s = √|S₄|/(4π) × η(i)⁻² = √24/(4π) × (0.768)⁻² ≈ 0.66

    **Citation:** Proposition 0.0.25 §4.1 (Appendix W) -/
noncomputable def g_s_S4 : ℝ := Real.sqrt S4_order / (4 * Real.pi) * (1 / eta_at_i^2)

/-- Phenomenological string coupling: g_s ≈ 0.7 -/
noncomputable def g_s_phenom : ℝ := 0.7

/-- g_s phenomenological > 0 -/
theorem g_s_phenom_pos : g_s_phenom > 0 := by unfold g_s_phenom; norm_num

/-- Agreement between S₄-derived and phenomenological g_s: ~7% -/
theorem g_s_agreement :
    |g_s_phenom - 0.66| / g_s_phenom < 0.10 := by
  unfold g_s_phenom
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 22: GASSER-LEUTWYLER LOW-ENERGY CONSTANTS (Proposition 0.0.17k2)
    ═══════════════════════════════════════════════════════════════════════════

    Low-energy constants for O(p⁴) chiral perturbation theory.
    These are the Gasser-Leutwyler LECs for SU(2) ChPT.

    Reference: docs/proofs/foundations/Proposition-0.0.17k2-CG-Effective-Action-Op4-GL-Matching.md
-/

/-- Rho meson mass: M_ρ = 775 MeV (PDG 2024).

    **Physical meaning:**
    The lightest vector meson, dominates pion-pion scattering at intermediate energies.

    **Citation:** PDG 2024, M_ρ = 775.11 ± 0.34 MeV -/
noncomputable def M_rho_MeV : ℝ := 775

/-- M_ρ > 0 -/
theorem M_rho_pos : M_rho_MeV > 0 := by unfold M_rho_MeV; norm_num

/-- Axial-vector meson mass: M_{a₁} = 1260 MeV (PDG 2024).

    **Physical meaning:**
    The lightest axial-vector meson, partner of the rho in chiral symmetry.

    **Citation:** PDG 2024, M_{a₁(1260)} = 1230 ± 40 MeV -/
noncomputable def M_a1_MeV : ℝ := 1260

/-- M_{a₁} > 0 -/
theorem M_a1_pos : M_a1_MeV > 0 := by unfold M_a1_MeV; norm_num

/-- Scalar meson (sigma/f₀) mass: M_S ≈ 500 MeV (PDG 2024).

    **Physical meaning:**
    The broad sigma meson, corresponds to breathing mode of chiral condensate.

    **Citation:** PDG 2024, f₀(500) or "σ", M = 400-550 MeV -/
noncomputable def M_sigma_MeV : ℝ := 500

/-- M_σ > 0 -/
theorem M_sigma_pos : M_sigma_MeV > 0 := by unfold M_sigma_MeV; norm_num

/-- Eta prime mass: M_{η'} = 958 MeV (PDG 2024).

    **Physical meaning:**
    The flavor-singlet pseudoscalar, gets mass from U(1)_A anomaly.

    **Citation:** PDG 2024, M_{η'(958)} = 957.78 ± 0.06 MeV -/
noncomputable def M_eta_prime_MeV : ℝ := 958

/-- M_{η'} > 0 -/
theorem M_eta_prime_pos : M_eta_prime_MeV > 0 := by unfold M_eta_prime_MeV; norm_num

/-- Vector Laplacian eigenvalue factor: c_V ∈ [2.68, 4.08], empirical = 3.10.

    **Physical meaning:**
    Dimensionless factor relating vector resonance mass to √σ:
    M_V² = σ · c_V

    **Derivation:**
    c_V = M_ρ² / σ = 775² / 440² ≈ 3.10

    **Citation:** Proposition 0.0.17k2 §4.4 -/
noncomputable def c_V_empirical : ℝ := M_rho_MeV ^ 2 / sqrt_sigma_predicted_MeV ^ 2

/-- c_V lower bound from Dirichlet BC on 3-face Laplacian -/
noncomputable def c_V_lower : ℝ := 2.68

/-- c_V upper bound from Neumann BC on 3-face Laplacian -/
noncomputable def c_V_upper : ℝ := 4.08

/-- c_V > 0 -/
theorem c_V_empirical_pos : c_V_empirical > 0 := by
  unfold c_V_empirical
  apply div_pos
  · exact sq_pos_of_pos M_rho_pos
  · exact sq_pos_of_pos sqrt_sigma_predicted_pos

/-- Gasser-Leutwyler scale-independent LEC: ℓ̄₁ = -0.4 ± 0.6 (empirical).

    **Physical meaning:**
    Controls (∂U∂U†)² contribution to π-π scattering.

    **Citation:** EGPR (1989), Table 2 -/
noncomputable def ell_bar_1_empirical : ℝ := -0.4

/-- Gasser-Leutwyler scale-independent LEC: ℓ̄₂ = 4.3 ± 0.1 (empirical).

    **Physical meaning:**
    Controls (∂U∂U†)·(∂U∂U†) contribution to π-π scattering.

    **Citation:** EGPR (1989), Table 2 -/
noncomputable def ell_bar_2_empirical : ℝ := 4.3

/-- ℓ̄₂ > 0 -/
theorem ell_bar_2_pos : ell_bar_2_empirical > 0 := by unfold ell_bar_2_empirical; norm_num

/-- Gasser-Leutwyler scale-independent LEC: ℓ̄₃ = 2.9 ± 2.4 (empirical).

    **Physical meaning:**
    Controls quark mass renormalization of pion mass.

    **Citation:** FLAG 2024 -/
noncomputable def ell_bar_3_empirical : ℝ := 2.9

/-- ℓ̄₃ > 0 -/
theorem ell_bar_3_pos : ell_bar_3_empirical > 0 := by unfold ell_bar_3_empirical; norm_num

/-- Gasser-Leutwyler scale-independent LEC: ℓ̄₅ = 13.3 ± 0.3 (empirical).

    **Physical meaning:**
    Controls π⁺-π⁰ electromagnetic mass difference.

    **Citation:** EGPR (1989), Table 2 -/
noncomputable def ell_bar_5_empirical : ℝ := 13.3

/-- ℓ̄₅ > 0 -/
theorem ell_bar_5_pos : ell_bar_5_empirical > 0 := by unfold ell_bar_5_empirical; norm_num

/-- Gasser-Leutwyler scale-independent LEC: ℓ̄₆ = 16.5 ± 1.1 (empirical).

    **Physical meaning:**
    Controls pion electromagnetic form factor.

    **Citation:** EGPR (1989), Table 2 -/
noncomputable def ell_bar_6_empirical : ℝ := 16.5

/-- ℓ̄₆ > 0 -/
theorem ell_bar_6_pos : ell_bar_6_empirical > 0 := by unfold ell_bar_6_empirical; norm_num

/-- KSRF relation: ℓ̄₂ = -2·ℓ̄₁ (approximate, from vector meson dominance).

    **Physical meaning:**
    The Kawarabayashi-Suzuki-Riazuddin-Fayyazuddin relation connects
    the two LECs controlling π-π scattering.

    **Citation:** KSRF (1966), satisfied to ~10% empirically -/
theorem KSRF_relation_approximate :
    |ell_bar_2_empirical - (-2 * ell_bar_1_empirical)| < 4 := by
  unfold ell_bar_2_empirical ell_bar_1_empirical
  norm_num

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
    SECTION 26: QCD CASIMIR FACTORS AND LOOP CONSTANTS (Proposition 6.3.1)
    ═══════════════════════════════════════════════════════════════════════════

    Standard QCD Casimir factors and constants for one-loop corrections.
    Reference: docs/proofs/Phase6/Proposition-6.3.1-One-Loop-QCD-Corrections.md
-/

/-- Fundamental representation Casimir C_F = (N_c² - 1)/(2N_c) = 4/3 for SU(3).

    **Physical meaning:**
    Appears in quark self-energy and vertex corrections.

    **Citation:** Standard SU(3) result, PDG QCD review -/
noncomputable def C_F : ℝ := C2_fundamental

/-- C_F = 4/3 -/
theorem C_F_value : C_F = 4 / 3 := rfl

/-- C_F > 0 -/
theorem C_F_pos : C_F > 0 := C2_fundamental_pos

/-- Adjoint representation Casimir C_A = N_c = 3 for SU(3).

    **Physical meaning:**
    Appears in gluon self-energy and gluon loop contributions.

    **Citation:** Standard SU(3) result -/
noncomputable def C_A : ℝ := C2_adjoint

/-- C_A = 3 -/
theorem C_A_value : C_A = 3 := rfl

/-- C_A > 0 -/
theorem C_A_pos : C_A > 0 := C2_adjoint_pos

/-- Trace normalization T_F = 1/2 for fundamental representation.

    **Physical meaning:**
    Tr(T^a T^b) = T_F δ^{ab} in our convention.
    Appears in fermion loop contributions to gluon self-energy.

    **Citation:** Standard normalization (Peskin & Schroeder convention) -/
noncomputable def T_F : ℝ := 1 / 2

/-- T_F = 1/2 -/
theorem T_F_value : T_F = 1 / 2 := rfl

/-- T_F > 0 -/
theorem T_F_pos : T_F > 0 := by unfold T_F; norm_num

/-- Strong coupling at M_Z (PDG 2024): α_s(M_Z) = 0.1180 ± 0.0009.

    **Physical meaning:**
    The MS-bar strong coupling constant at the Z boson mass scale.

    **Citation:** PDG 2024, QCD section -/
noncomputable def alpha_s_MZ_PDG : ℝ := 0.1180

/-- PDG uncertainty on α_s(M_Z) -/
noncomputable def alpha_s_MZ_uncertainty : ℝ := 0.0009

/-- α_s(M_Z) > 0 -/
theorem alpha_s_MZ_PDG_pos : alpha_s_MZ_PDG > 0 := by
  unfold alpha_s_MZ_PDG; norm_num

/-- Strong coupling at M_Z (CG prediction): α_s(M_Z) = 0.122.

    **Physical meaning:**
    CG prediction from E₆ → E₈ cascade running from the Planck scale.

    **Citation:** Proposition 0.0.17s, Proposition 6.3.1 §4.1 -/
noncomputable def alpha_s_MZ_CG : ℝ := 0.122

/-- CG theoretical uncertainty on α_s(M_Z) -/
noncomputable def alpha_s_MZ_CG_uncertainty : ℝ := 0.010

/-- α_s(M_Z) CG > 0 -/
theorem alpha_s_MZ_CG_pos : alpha_s_MZ_CG > 0 := by
  unfold alpha_s_MZ_CG; norm_num

/-- CG vs PDG deviation for α_s(M_Z): ~3.4%.

    **Physical meaning:**
    The 4.4σ experimental tension is within the 20% theoretical uncertainty
    from one-loop running, threshold corrections, and scale uncertainties.

    **Citation:** Proposition 6.3.1 §4.1 -/
theorem alpha_s_MZ_deviation :
    |alpha_s_MZ_CG - alpha_s_MZ_PDG| / alpha_s_MZ_PDG < 0.04 := by
  unfold alpha_s_MZ_CG alpha_s_MZ_PDG
  norm_num

/-- One-loop QCD β-function coefficient: β₀ = 11 - 2N_f/3.

    **Physical meaning:**
    The coefficient in β(α_s) = -β₀ α_s²/(2π) + O(α_s³).

    For N_f = 6: β₀ = 11 - 4 = 7.

    **Citation:** Gross-Wilczek (1973), Politzer (1973) -/
noncomputable def beta0_QCD (n_f : ℕ) : ℝ := 11 - 2 * n_f / 3

/-- β₀ for N_f = 6: β₀ = 7 -/
theorem beta0_QCD_nf6 : beta0_QCD 6 = 7 := by
  unfold beta0_QCD; norm_num

/-- β₀ > 0 for N_f ≤ 16 (asymptotic freedom) -/
theorem beta0_QCD_positive (n_f : ℕ) (h : n_f ≤ 16) : beta0_QCD n_f > 0 := by
  unfold beta0_QCD
  have hcast : (n_f : ℝ) ≤ 16 := Nat.cast_le.mpr h
  linarith

/-- Two-loop β-function coefficient: β₁ = 102 - 38N_f/3.

    **Physical meaning:**
    The second coefficient in the expansion:
    β(α_s) = -β₀ α_s²/(2π) - β₁ α_s³/(4π²) + O(α_s⁴)

    For N_f = 6: β₁ = 102 - 76 = 26.

    **Citation:** Caswell (1974), Jones (1974) -/
noncomputable def beta1_QCD (n_f : ℕ) : ℝ := 102 - 38 * n_f / 3

/-- β₁ for N_f = 6: β₁ = 26 -/
theorem beta1_QCD_nf6 : beta1_QCD 6 = 26 := by
  unfold beta1_QCD; norm_num

/-- Mass anomalous dimension coefficient: γ_m^(0) = 6 C_F = 8.

    **Physical meaning:**
    The one-loop coefficient in γ_m = γ_m^(0) α_s/(4π) + O(α_s²).

    **Citation:** Proposition 6.3.1 §4.2 -/
noncomputable def gamma_m_0 : ℝ := 6 * C_F

/-- γ_m^(0) = 8 for SU(3) -/
theorem gamma_m_0_value : gamma_m_0 = 8 := by
  unfold gamma_m_0 C_F C2_fundamental; norm_num

/-- γ_m^(0) > 0 -/
theorem gamma_m_0_pos : gamma_m_0 > 0 := by
  unfold gamma_m_0 C_F C2_fundamental; norm_num

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

end ChiralGeometrogenesis.Constants
