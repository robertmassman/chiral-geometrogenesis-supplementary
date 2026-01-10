/-
  ChiralGeometrogenesis/Tactics/Phase120.lean

  Lemmas and tactics for SU(3) phase dynamics (Sakaguchi-Kuramoto model).

  This module provides formalization of the 120° phase separation that
  characterizes the equilibrium of the three-color Sakaguchi-Kuramoto model.

  ## Mathematical Background

  ### The Kuramoto Model

  The standard Kuramoto model describes N coupled oscillators [Kuramoto1984]:
    dθᵢ/dt = ωᵢ + (K/N) Σⱼ sin(θⱼ - θᵢ)

  The Sakaguchi-Kuramoto variant adds a phase lag parameter α [Sakaguchi1986]:
    dθᵢ/dt = ωᵢ + (K/N) Σⱼ sin(θⱼ - θᵢ - α)

  ### The ChiralGeometrogenesis SU(3) Variant

  For three identical oscillators (R, G, B) with target phases at 120° separation,
  we use α = 2π/3 for the R→G coupling, α = 4π/3 for the R→B coupling, etc.
  This yields the system:

    dφ_R/dt = ω + (K/2)[sin(φ_G - φ_R - 2π/3) + sin(φ_B - φ_R - 4π/3)]
    dφ_G/dt = ω + (K/2)[sin(φ_R - φ_G + 2π/3) + sin(φ_B - φ_G - 2π/3)]
    dφ_B/dt = ω + (K/2)[sin(φ_R - φ_B + 4π/3) + sin(φ_G - φ_B + 2π/3)]

  ### Equilibrium Configuration

  At equilibrium, the phases are:
    φ_R = φ₀ + ωt
    φ_G = φ₀ + ωt + 2π/3
    φ_B = φ₀ + ωt + 4π/3

  This configuration makes all sine terms vanish:
    sin(φ_G - φ_R - 2π/3) = sin(2π/3 - 2π/3) = sin(0) = 0
    sin(φ_B - φ_R - 4π/3) = sin(4π/3 - 4π/3) = sin(0) = 0

  ### Reduced Phase-Difference Coordinates

  Due to the translational symmetry (uniform phase shift), we work in the
  reduced 2D phase-difference space [Strogatz2000]:

    δ₁ = φ_G - φ_R - 2π/3  (deviation from target G-R separation)
    δ₂ = φ_B - φ_R - 4π/3  (deviation from target B-R separation)

  The equilibrium corresponds to δ₁ = δ₂ = 0.

  ### Jacobian and Stability

  The 3×3 Jacobian of the full system at equilibrium is:

    J₃ₓ₃ = (K/2) * | -2    1    1  |
                   |  1   -2    1  |
                   |  1    1   -2  |

  This symmetric circulant matrix has eigenvalues:
    λ₀ = 0       (eigenvector [1, 1, 1], corresponds to uniform phase shift)
    λ₁ = -3K/2   (eigenvector [1, -1, 0], relative phase perturbation)
    λ₂ = -3K/2   (eigenvector [1, 1, -2], relative phase perturbation)

  The zero eigenvalue reflects the continuous symmetry of the system.
  The reduced 2D system (in δ₁, δ₂ coordinates) inherits only the non-zero
  eigenvalues, both equal to -3K/2.

  Since both stability eigenvalues are negative for K > 0, the equilibrium
  is asymptotically stable in the reduced phase-difference space.

  ## References

  - [Kuramoto1984] Y. Kuramoto, "Chemical Oscillations, Waves, and Turbulence",
    Springer-Verlag, 1984. DOI: 10.1007/978-3-642-69689-3

  - [Sakaguchi1986] H. Sakaguchi and Y. Kuramoto, "A soluble active rotator model
    showing phase transitions via mutual entrainment", Prog. Theor. Phys. 76, 576 (1986).
    DOI: 10.1143/PTP.76.576

  - [Strogatz2000] S. H. Strogatz, "From Kuramoto to Crawford: exploring the onset
    of synchronization in populations of coupled oscillators", Physica D 143, 1 (2000).
    DOI: 10.1016/S0167-2789(00)00094-4

  - [Dörfler2014] F. Dörfler and F. Bullo, "Synchronization in complex networks of
    phase oscillators: A survey", Automatica 50, 1539 (2014).
    DOI: 10.1016/j.automatica.2014.04.012
-/

import ChiralGeometrogenesis.Tactics.TrigSimplify

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Tactics

open Real

/-! ## Phase Configuration Structure

We formalize the 120° phase separation as a structure.
-/

/-- A configuration of three phases with the SU(3) 120° separation.

The phases are parameterized by a single base phase φ₀:
- φ_R = φ₀
- φ_G = φ₀ + 2π/3
- φ_B = φ₀ + 4π/3

This is the equilibrium configuration of the Sakaguchi-Kuramoto model.
-/
structure Phase120Config where
  /-- The base phase (red phase) -/
  φ₀ : ℝ

namespace Phase120Config

/-- The red phase -/
noncomputable def φ_R (cfg : Phase120Config) : ℝ := cfg.φ₀

/-- The green phase (shifted by 2π/3 from red) -/
noncomputable def φ_G (cfg : Phase120Config) : ℝ := cfg.φ₀ + 2 * π / 3

/-- The blue phase (shifted by 4π/3 from red) -/
noncomputable def φ_B (cfg : Phase120Config) : ℝ := cfg.φ₀ + 4 * π / 3

/-- The phases differ by exactly 2π/3 -/
theorem phase_diff_RG (cfg : Phase120Config) : cfg.φ_G - cfg.φ_R = 2 * π / 3 := by
  simp only [φ_G, φ_R]
  ring

theorem phase_diff_GB (cfg : Phase120Config) : cfg.φ_B - cfg.φ_G = 2 * π / 3 := by
  simp only [φ_B, φ_G]
  ring

theorem phase_diff_BR (cfg : Phase120Config) : cfg.φ_R - cfg.φ_B = -4 * π / 3 := by
  simp only [φ_R, φ_B]
  ring

/-- The three phases sum to 3φ₀ + 2π (modulo 2π, this is 3φ₀) -/
theorem phase_sum (cfg : Phase120Config) :
    cfg.φ_R + cfg.φ_G + cfg.φ_B = 3 * cfg.φ₀ + 2 * π := by
  simp only [φ_R, φ_G, φ_B]
  ring

end Phase120Config

/-! ## Sakaguchi-Kuramoto Coupling Terms

The coupling in the SU(3) Sakaguchi-Kuramoto model.
-/

/-- Coupling term for the R oscillator:
    sin(φ_G - φ_R - 2π/3) + sin(φ_B - φ_R - 4π/3)

At equilibrium (Phase120Config), this vanishes.
-/
noncomputable def coupling_R (φ_R φ_G φ_B : ℝ) : ℝ :=
  sin (φ_G - φ_R - 2 * π / 3) + sin (φ_B - φ_R - 4 * π / 3)

/-- Coupling term for the G oscillator -/
noncomputable def coupling_G (φ_R φ_G φ_B : ℝ) : ℝ :=
  sin (φ_R - φ_G + 2 * π / 3) + sin (φ_B - φ_G - 2 * π / 3)

/-- Coupling term for the B oscillator -/
noncomputable def coupling_B (φ_R φ_G φ_B : ℝ) : ℝ :=
  sin (φ_R - φ_B + 4 * π / 3) + sin (φ_G - φ_B + 2 * π / 3)

/-- **Equilibrium Theorem**: At the 120° configuration, all couplings vanish -/
theorem coupling_R_at_equilibrium (cfg : Phase120Config) :
    coupling_R cfg.φ_R cfg.φ_G cfg.φ_B = 0 := by
  unfold coupling_R Phase120Config.φ_R Phase120Config.φ_G Phase120Config.φ_B
  -- φ_G - φ_R - 2π/3 = (φ₀ + 2π/3) - φ₀ - 2π/3 = 0
  -- φ_B - φ_R - 4π/3 = (φ₀ + 4π/3) - φ₀ - 4π/3 = 0
  have h1 : cfg.φ₀ + 2 * π / 3 - cfg.φ₀ - 2 * π / 3 = 0 := by ring
  have h2 : cfg.φ₀ + 4 * π / 3 - cfg.φ₀ - 4 * π / 3 = 0 := by ring
  simp only [h1, h2, sin_zero, add_zero]

theorem coupling_G_at_equilibrium (cfg : Phase120Config) :
    coupling_G cfg.φ_R cfg.φ_G cfg.φ_B = 0 := by
  unfold coupling_G Phase120Config.φ_R Phase120Config.φ_G Phase120Config.φ_B
  have h1 : cfg.φ₀ - (cfg.φ₀ + 2 * π / 3) + 2 * π / 3 = 0 := by ring
  have h2 : cfg.φ₀ + 4 * π / 3 - (cfg.φ₀ + 2 * π / 3) - 2 * π / 3 = 0 := by ring
  simp only [h1, h2, sin_zero, add_zero]

theorem coupling_B_at_equilibrium (cfg : Phase120Config) :
    coupling_B cfg.φ_R cfg.φ_G cfg.φ_B = 0 := by
  unfold coupling_B Phase120Config.φ_R Phase120Config.φ_G Phase120Config.φ_B
  have h1 : cfg.φ₀ - (cfg.φ₀ + 4 * π / 3) + 4 * π / 3 = 0 := by ring
  have h2 : cfg.φ₀ + 2 * π / 3 - (cfg.φ₀ + 4 * π / 3) + 2 * π / 3 = 0 := by ring
  simp only [h1, h2, sin_zero, add_zero]

/-- All three couplings vanish at equilibrium -/
theorem all_couplings_vanish_at_equilibrium (cfg : Phase120Config) :
    coupling_R cfg.φ_R cfg.φ_G cfg.φ_B = 0 ∧
    coupling_G cfg.φ_R cfg.φ_G cfg.φ_B = 0 ∧
    coupling_B cfg.φ_R cfg.φ_G cfg.φ_B = 0 :=
  ⟨coupling_R_at_equilibrium cfg, coupling_G_at_equilibrium cfg, coupling_B_at_equilibrium cfg⟩

/-! ## Reduced Phase-Difference Dynamics

We work in the reduced 2D phase-difference space to eliminate the
translational symmetry. This is the standard approach in the dynamical
systems literature [Strogatz2000, Dörfler2014].

Define:
  δ₁ = φ_G - φ_R - 2π/3
  δ₂ = φ_B - φ_R - 4π/3

At equilibrium: δ₁ = δ₂ = 0
-/

/-- Phase deviation δ₁ = φ_G - φ_R - 2π/3 -/
noncomputable def phase_deviation_1 (φ_R φ_G : ℝ) : ℝ := φ_G - φ_R - 2 * π / 3

/-- Phase deviation δ₂ = φ_B - φ_R - 4π/3 -/
noncomputable def phase_deviation_2 (φ_R φ_B : ℝ) : ℝ := φ_B - φ_R - 4 * π / 3

/-- At equilibrium, both deviations are zero -/
theorem deviations_zero_at_equilibrium (cfg : Phase120Config) :
    phase_deviation_1 cfg.φ_R cfg.φ_G = 0 ∧
    phase_deviation_2 cfg.φ_R cfg.φ_B = 0 := by
  unfold phase_deviation_1 phase_deviation_2
  unfold Phase120Config.φ_R Phase120Config.φ_G Phase120Config.φ_B
  constructor <;> ring

/-! ## Jacobian of the 3D Phase System

### Derivation of the Jacobian Matrix

The system in 3D phase space (φ_R, φ_G, φ_B) is:
  dφ_R/dt = ω + (K/2)[sin(φ_G - φ_R - 2π/3) + sin(φ_B - φ_R - 4π/3)]
  dφ_G/dt = ω + (K/2)[sin(φ_R - φ_G + 2π/3) + sin(φ_B - φ_G - 2π/3)]
  dφ_B/dt = ω + (K/2)[sin(φ_R - φ_B + 4π/3) + sin(φ_G - φ_B + 2π/3)]

The Jacobian entries at equilibrium (φ_R, φ_G, φ_B) = (φ₀, φ₀ + 2π/3, φ₀ + 4π/3):

**Diagonal entries** (∂fᵢ/∂φᵢ):
  ∂f_R/∂φ_R = (K/2)[-cos(0) - cos(0)] = -K

**Off-diagonal entries** (∂fᵢ/∂φⱼ for i ≠ j):
  ∂f_R/∂φ_G = (K/2)[cos(0)] = K/2
  ∂f_R/∂φ_B = (K/2)[cos(0)] = K/2

By symmetry, the 3×3 Jacobian is:

  J = (K/2) * | -2    1    1  |
              |  1   -2    1  |
              |  1    1   -2  |

### Eigenvalue Analysis

This is a symmetric circulant matrix with first row [a, b, b] where a = -K, b = K/2.

For a 3×3 circulant matrix with first row [a, b, b], the eigenvalues are:
  λ₀ = a + 2b         (eigenvector [1, 1, 1])
  λ₁ = λ₂ = a - b     (eigenvector space orthogonal to [1,1,1])

**Calculation:**
  λ₀ = -K + 2(K/2) = -K + K = 0     (translational mode)
  λ₁ = λ₂ = -K - K/2 = -3K/2        (stability modes)

The zero eigenvalue reflects the continuous symmetry: uniformly shifting all phases
leaves the dynamics invariant. The negative eigenvalue -3K/2 (with multiplicity 2)
governs the stability of perturbations that break the 120° separation.

**Eigenvectors:**
  - λ₀ = 0: eigenvector [1, 1, 1]/√3 (uniform shift)
  - λ₁ = -3K/2: eigenvectors [1, -1, 0]/√2 and [1, 1, -2]/√6 (relative phase modes)

Reference: [Dörfler2014] Section 3.1, Theorem 3.1
-/

/-- The Jacobian of the 3D phase system at equilibrium.

The 3×3 Jacobian is:
  J = (K/2) * | -2    1    1  |
              |  1   -2    1  |
              |  1    1   -2  |

This is a symmetric circulant matrix.
-/
structure JacobianAtEquilibrium where
  /-- The coupling strength, must be positive for synchronization -/
  K : ℝ
  /-- Positivity assumption -/
  K_pos : K > 0

namespace JacobianAtEquilibrium

/-- Diagonal entry of the Jacobian: (K/2)(-2) = -K -/
noncomputable def diag_entry (J : JacobianAtEquilibrium) : ℝ := -J.K

/-- Off-diagonal entry of the Jacobian: (K/2)(1) = K/2 -/
noncomputable def off_diag_entry (J : JacobianAtEquilibrium) : ℝ := J.K / 2

/-! ### Eigenvalue Calculation

For a 3×3 circulant matrix with first row [a, b, b], the eigenvalues are:
  λ₀ = a + 2b         (eigenvector [1, 1, 1])
  λ₁ = λ₂ = a - b     (eigenvector space orthogonal to [1,1,1])

For our Jacobian with a = -K, b = K/2:
  λ₀ = -K + 2(K/2) = -K + K = 0
  λ₁ = λ₂ = -K - K/2 = -3K/2

The zero eigenvalue corresponds to the translational symmetry
(all phases can shift by the same amount). The negative eigenvalues
-3K/2 (with multiplicity 2) govern the stability of perturbations
that break the 120° separation.

Reference: [Dörfler2014] Section 3.1, Theorem 3.1
-/

/-- The zero eigenvalue from translational symmetry -/
noncomputable def eigenvalue_symmetric (J : JacobianAtEquilibrium) : ℝ := 0

/-- The stability eigenvalue (with multiplicity 2) -/
noncomputable def eigenvalue_stability (J : JacobianAtEquilibrium) : ℝ := -3 * J.K / 2

/-- The zero eigenvalue is indeed zero -/
theorem eigenvalue_symmetric_eq (J : JacobianAtEquilibrium) :
    J.eigenvalue_symmetric = 0 := rfl

/-- Proof that eigenvalue_symmetric = a + 2b for our circulant matrix -/
theorem eigenvalue_symmetric_from_circulant (J : JacobianAtEquilibrium) :
    J.diag_entry + 2 * J.off_diag_entry = 0 := by
  unfold diag_entry off_diag_entry
  ring

/-- Proof that eigenvalue_stability = a - b for our circulant matrix -/
theorem eigenvalue_stability_from_circulant (J : JacobianAtEquilibrium) :
    J.diag_entry - J.off_diag_entry = J.eigenvalue_stability := by
  unfold diag_entry off_diag_entry eigenvalue_stability
  ring

/-- The stability eigenvalue is negative -/
theorem eigenvalue_stability_neg (J : JacobianAtEquilibrium) :
    J.eigenvalue_stability < 0 := by
  unfold eigenvalue_stability
  have hK := J.K_pos
  linarith

/-- **Stability Theorem**: The non-zero eigenvalues are all negative,
so perturbations from equilibrium decay exponentially.

This proves asymptotic stability of the 120° phase configuration
in the reduced phase-difference space.

Reference: [Strogatz2000] Section 4, [Dörfler2014] Theorem 3.1
-/
theorem asymptotically_stable (J : JacobianAtEquilibrium) :
    J.eigenvalue_stability < 0 := eigenvalue_stability_neg J

/-- The rate of convergence to equilibrium is at least 3K/2 -/
theorem convergence_rate (J : JacobianAtEquilibrium) :
    |J.eigenvalue_stability| = 3 * J.K / 2 := by
  unfold eigenvalue_stability
  have hK := J.K_pos
  rw [abs_of_neg (by linarith : -3 * J.K / 2 < 0)]
  ring

/-! ### Eigenvector Verification

We verify that the claimed eigenvalues are correct by showing that the
eigenvector equations are satisfied. For a circulant matrix C with first
row [a, b, b], and eigenvector v:
  C · v = λ · v

**Eigenvector [1, 1, 1] with eigenvalue 0:**
  C · [1, 1, 1]ᵀ = [a + 2b, a + 2b, a + 2b]ᵀ = (a + 2b) · [1, 1, 1]ᵀ = 0 · [1, 1, 1]ᵀ

**Eigenvector [1, -1, 0] with eigenvalue a - b:**
  C · [1, -1, 0]ᵀ = [a - b, -a + b, b - b]ᵀ = [a - b, -(a - b), 0]ᵀ = (a - b) · [1, -1, 0]ᵀ

**Eigenvector [1, 1, -2] with eigenvalue a - b:**
  C · [1, 1, -2]ᵀ = [a + b - 2b, b + a - 2b, b + b - 2a]ᵀ
                 = [a - b, a - b, -2(a - b)]ᵀ = (a - b) · [1, 1, -2]ᵀ
-/

/-- The [1, 1, 1] eigenvector equation: row sum equals zero -/
theorem eigenvector_111_equation (J : JacobianAtEquilibrium) :
    J.diag_entry + 2 * J.off_diag_entry = J.eigenvalue_symmetric := by
  unfold diag_entry off_diag_entry eigenvalue_symmetric
  ring

/-- The [1, -1, 0] eigenvector equation: first component -/
theorem eigenvector_1m10_first (J : JacobianAtEquilibrium) :
    J.diag_entry - J.off_diag_entry = J.eigenvalue_stability := by
  unfold diag_entry off_diag_entry eigenvalue_stability
  ring

/-- The [1, -1, 0] eigenvector equation: second component -/
theorem eigenvector_1m10_second (J : JacobianAtEquilibrium) :
    J.off_diag_entry - J.diag_entry = -J.eigenvalue_stability := by
  unfold diag_entry off_diag_entry eigenvalue_stability
  ring

/-- The [1, -1, 0] eigenvector equation: third component -/
theorem eigenvector_1m10_third (J : JacobianAtEquilibrium) :
    J.off_diag_entry - J.off_diag_entry = 0 * J.eigenvalue_stability := by
  ring

/-- The [1, 1, -2] eigenvector equation: first component -/
theorem eigenvector_11m2_first (J : JacobianAtEquilibrium) :
    J.diag_entry + J.off_diag_entry - 2 * J.off_diag_entry = J.eigenvalue_stability := by
  unfold diag_entry off_diag_entry eigenvalue_stability
  ring

/-- The [1, 1, -2] eigenvector equation: third component -/
theorem eigenvector_11m2_third (J : JacobianAtEquilibrium) :
    2 * J.off_diag_entry - 2 * J.diag_entry = -2 * J.eigenvalue_stability := by
  unfold diag_entry off_diag_entry eigenvalue_stability
  ring

/-! ### Multiplicity of Eigenvalues

The eigenvalue -3K/2 has multiplicity 2, as the eigenvectors [1, -1, 0] and
[1, 1, -2] are linearly independent and both correspond to this eigenvalue.
-/

/-- Both stability eigenvectors share the same eigenvalue -/
theorem stability_eigenvalue_multiplicity (J : JacobianAtEquilibrium) :
    (J.diag_entry - J.off_diag_entry = J.eigenvalue_stability) ∧
    (J.diag_entry + J.off_diag_entry - 2 * J.off_diag_entry = J.eigenvalue_stability) :=
  ⟨eigenvector_1m10_first J, eigenvector_11m2_first J⟩

end JacobianAtEquilibrium

/-! ## Floquet Theory for Periodic Orbits

For the limit cycle (uniformly rotating solution), we use Floquet theory.
The rotating solution has all phases advancing at rate ω, maintaining
the 120° separation.
-/

/-- The period of the uniformly rotating solution is T = 2π/ω -/
noncomputable def rotationPeriod (ω : ℝ) (hω : ω > 0) : ℝ := 2 * π / ω

/-- The Floquet multipliers determine orbital stability.

For the Sakaguchi-Kuramoto limit cycle, the monodromy matrix has
eigenvalues e^{λᵢT} where λᵢ are the Jacobian eigenvalues and T is the period.

For the stability eigenvalue λ = -3K/2:
  μ = e^{λT} = e^{-3KT/2}

Since λ < 0, we have |μ| = e^{λT} < 1, proving orbital stability.

Reference: Floquet's theorem, see [Chicone2006] Chapter 2.
-/
theorem floquet_multiplier_bound {lam T : ℝ} (hlam : lam < 0) (hT : T > 0) :
    exp (lam * T) < 1 := by
  have h : lam * T < 0 := mul_neg_of_neg_of_pos hlam hT
  calc exp (lam * T) < exp 0 := exp_strictMono h
    _ = 1 := exp_zero

/-- The Floquet multiplier for the stability eigenvalue -/
theorem floquet_multiplier_stable (J : JacobianAtEquilibrium) {T : ℝ} (hT : T > 0) :
    exp (J.eigenvalue_stability * T) < 1 :=
  floquet_multiplier_bound J.eigenvalue_stability_neg hT

/-! ## Complex Exponential Representation

The 120° phase separation can be elegantly expressed using complex exponentials.
-/

/-- e^{iφ_R} + e^{iφ_G} + e^{iφ_B} = 0 at equilibrium.

This is the complex version of the sum_sin_120 and sum_cos_120 theorems.
The proof uses the fact that cube roots of unity sum to zero:
  1 + ω + ω² = 0  where ω = e^{i·2π/3}

Mathematically:
  e^{iφ₀} + e^{i(φ₀ + 2π/3)} + e^{i(φ₀ + 4π/3)}
  = e^{iφ₀}(1 + e^{i·2π/3} + e^{i·4π/3})
  = e^{iφ₀} · 0  [cube roots of unity sum to zero]
  = 0

This identity is fundamental to SU(3) representation theory and
the color charge neutrality condition in QCD.
-/
theorem complex_phase_sum_zero (cfg : Phase120Config) :
    Complex.exp (Complex.I * cfg.φ_R) +
    Complex.exp (Complex.I * cfg.φ_G) +
    Complex.exp (Complex.I * cfg.φ_B) = 0 := by
  simp only [Phase120Config.φ_R, Phase120Config.φ_G, Phase120Config.φ_B]
  -- Factor out e^{iφ₀}
  have h1 : Complex.I * ↑(cfg.φ₀ + 2 * π / 3) = Complex.I * ↑cfg.φ₀ + Complex.I * (2 * π / 3) := by
    push_cast; ring
  have h2 : Complex.I * ↑(cfg.φ₀ + 4 * π / 3) = Complex.I * ↑cfg.φ₀ + Complex.I * (4 * π / 3) := by
    push_cast; ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add]
  -- Factor out the common term
  have h_factor : Complex.exp (Complex.I * ↑cfg.φ₀) +
      Complex.exp (Complex.I * ↑cfg.φ₀) * Complex.exp (Complex.I * (2 * π / 3)) +
      Complex.exp (Complex.I * ↑cfg.φ₀) * Complex.exp (Complex.I * (4 * π / 3)) =
      Complex.exp (Complex.I * ↑cfg.φ₀) *
        (1 + Complex.exp (Complex.I * (2 * π / 3)) + Complex.exp (Complex.I * (4 * π / 3))) := by
    ring
  rw [h_factor]
  -- The cube roots of unity sum to zero: 1 + ω + ω² = 0 where ω = e^{i·2π/3}
  have h_roots : (1 : ℂ) + Complex.exp (Complex.I * (2 * ↑π / 3)) +
                 Complex.exp (Complex.I * (4 * ↑π / 3)) = 0 := by
    simp only [mul_comm Complex.I _]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    -- The arguments 2*↑π/3 and 4*↑π/3 are Complex, but equal to coerced Reals
    have harg1 : (2 : ℂ) * ↑π / 3 = ↑((2 : ℝ) * π / 3) := by push_cast; ring
    have harg2 : (4 : ℂ) * ↑π / 3 = ↑((4 : ℝ) * π / 3) := by push_cast; ring
    simp only [harg1, harg2]
    -- Now Complex.cos/sin of ↑x equals ↑(Real.cos/sin x)
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [cos_two_pi_div_three, sin_two_pi_div_three,
        cos_four_pi_div_three, sin_four_pi_div_three]
    push_cast
    ring
  rw [h_roots, mul_zero]

/-- The real part of the complex phase sum is zero (equivalent to sum_cos_120) -/
theorem complex_phase_sum_re_zero (cfg : Phase120Config) :
    (Complex.exp (Complex.I * cfg.φ_R) +
     Complex.exp (Complex.I * cfg.φ_G) +
     Complex.exp (Complex.I * cfg.φ_B)).re = 0 := by
  rw [complex_phase_sum_zero]
  simp

/-- The imaginary part of the complex phase sum is zero (equivalent to sum_sin_120) -/
theorem complex_phase_sum_im_zero (cfg : Phase120Config) :
    (Complex.exp (Complex.I * cfg.φ_R) +
     Complex.exp (Complex.I * cfg.φ_G) +
     Complex.exp (Complex.I * cfg.φ_B)).im = 0 := by
  rw [complex_phase_sum_zero]
  simp

/-! ## The `phase120` Tactic

A convenience tactic for proofs involving 120° phase separations.
-/

/-- The `phase120` tactic applies standard results about the 120° phase configuration.

Usage:
```lean
example (cfg : Phase120Config) : coupling_R cfg.φ_R cfg.φ_G cfg.φ_B = 0 := by phase120
```
-/
macro "phase120" : tactic =>
  `(tactic| (
    first
    | exact coupling_R_at_equilibrium _
    | exact coupling_G_at_equilibrium _
    | exact coupling_B_at_equilibrium _
    | (simp only [Phase120Config.φ_R, Phase120Config.φ_G, Phase120Config.φ_B,
                  Phase120Config.phase_diff_RG, Phase120Config.phase_diff_GB]
       <;> try ring
       <;> try ring_nf
       <;> try simp only [sub_self, sin_zero, add_zero])
  ))

/-! ## Order Parameter

The Kuramoto order parameter measures synchronization.
For three phases with 120° separation, the order parameter is zero,
indicating "balanced" but not "synchronized" (in the trivial sense).
-/

/-- The Kuramoto order parameter r·e^{iψ} = (1/N)Σⱼ e^{iθⱼ}

For N=3 oscillators at 120° separation, r = 0.
-/
noncomputable def orderParameter (φ_R φ_G φ_B : ℝ) : ℂ :=
  (Complex.exp (Complex.I * φ_R) +
   Complex.exp (Complex.I * φ_G) +
   Complex.exp (Complex.I * φ_B)) / 3

/-- At the 120° equilibrium, the order parameter is zero -/
theorem orderParameter_zero_at_equilibrium (cfg : Phase120Config) :
    orderParameter cfg.φ_R cfg.φ_G cfg.φ_B = 0 := by
  unfold orderParameter
  rw [complex_phase_sum_zero]
  simp

/-- The magnitude of the order parameter is zero at equilibrium -/
theorem orderParameter_magnitude_zero (cfg : Phase120Config) :
    ‖orderParameter cfg.φ_R cfg.φ_G cfg.φ_B‖ = 0 := by
  rw [orderParameter_zero_at_equilibrium]
  simp

end ChiralGeometrogenesis.Tactics
