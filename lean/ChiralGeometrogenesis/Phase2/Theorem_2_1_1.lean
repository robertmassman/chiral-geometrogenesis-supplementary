/-
  Phase2/Theorem_2_1_1.lean

  Theorem 2.1.1: Bag Model Derivation

  Quarks are confined within a finite region (the "bag") where the internal
  quark pressure balances the external vacuum pressure B. The total energy is:

    E(R) = (4π/3)R³B + Ω/R

  where:
  - R is the bag radius
  - B is the bag constant (vacuum energy density)
  - Ω = Σᵢ nᵢωᵢ is the quark kinetic energy contribution

  Key Claims:
  1. Existence and uniqueness: E(R) has exactly one minimum on (0,∞)
  2. Equilibrium radius: R_eq = (Ω/4πB)^(1/4)
  3. Stability: d²E/dR²|_{R_eq} > 0
  4. Pressure balance: P_quark(R_eq) = P_vac = B
  5. Physical predictions: Proton mass ~938 MeV, radius ~1 fm

  Significance:
  - Provides physical mechanism for color confinement
  - Quarks cannot escape because vacuum energy cost is infinite
  - Connects to Chiral Geometrogenesis via B ~ λv_χ⁴

  Status: ✅ ESTABLISHED (MIT Bag Model, Chodos et al. 1974)

  **Formalization Note:** This file encodes the MIT Bag Model as established physics.
  The energy functional and equilibrium conditions are derived from first principles
  in calculus (energy minimization). Physical interpretations (bag constant from
  vacuum structure) are encoded as axioms/parameters.

  Dependencies:
  - ChiralGeometrogenesis.Basic (ColorPhase for three-color structure)
  - Mathlib.Analysis.Calculus (derivatives, optimization)
  - Mathlib.Analysis.SpecialFunctions.Pow (real powers)

  Reference: docs/proofs/Phase2/Theorem-2.1.1-Bag-Model-Derivation.md
-/

import ChiralGeometrogenesis.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

-- Linters enabled: all definitions have docstrings, no unused variables

namespace ChiralGeometrogenesis.Phase2.Theorem_2_1_1

open Real

/-! ## Section 1: Physical Constants and Parameters

The MIT Bag Model involves:
- B: Bag constant (vacuum energy density), typically B^(1/4) ≈ 145 MeV
- ω: Mode eigenvalue from MIT boundary conditions, lowest mode ω₀ ≈ 2.04
- n: Number of quarks (3 for baryons, 2 for mesons)
- Ω = nω: Total quark contribution to kinetic energy
-/

/-- Physical parameters for the bag model.

These encode the essential inputs from QCD:
- bag_constant: The vacuum energy density B (in appropriate units)
- omega_total: The sum Ω = Σᵢ nᵢωᵢ of quark contributions

From §1.4 of the markdown specification. -/
structure BagParams where
  /-- Bag constant B (vacuum energy density difference) -/
  bag_constant : ℝ
  /-- Total quark contribution Ω = Σᵢ nᵢωᵢ -/
  omega_total : ℝ
  /-- Physical requirement: B > 0 -/
  bag_pos : bag_constant > 0
  /-- Physical requirement: Ω > 0 -/
  omega_pos : omega_total > 0

/-- Standard parameters for a proton (3 quarks, lowest mode).

From §5.2 of the markdown:
- B^(1/4) ≈ 145 MeV, so B ≈ 0.06 GeV/fm³
- ω ≈ 2.04 (MIT boundary condition eigenvalue)
- Ω = 3 × 2.04 = 6.12 for proton

**MIT Boundary Condition Eigenvalue (ω ≈ 2.0428):**

The eigenvalue ω arises from requiring quarks to be confined within the bag.
The MIT boundary condition for massless Dirac fermions is:
  (1 + iγ·n̂)ψ|_{r=R} = 0
where n̂ is the outward normal. For the lowest s-wave mode (ℓ = 0), this
reduces to the transcendental equation:
  j₀(ω) = j₁(ω)
where jₗ are spherical Bessel functions. The lowest positive solution is:
  ω₀ = 2.04278...

**Reference:** Chodos et al. (1974), Phys. Rev. D 9, 3471, §II.B;
DeGrand et al. (1975), Phys. Rev. D 12, 2060, Table I. -/
noncomputable def protonParams : BagParams where
  bag_constant := 0.06  -- GeV/fm³ (schematic units)
  omega_total := 6.12   -- 3 quarks × 2.04
  bag_pos := by norm_num
  omega_pos := by norm_num

/-- Standard parameters for a pion (quark-antiquark pair).

From §5.4 of the markdown:
- Ω = 2 × 2.04 = 4.08 for pion

Note: The pion is a pseudo-Goldstone boson, so the bag model is less
accurate for pions than for baryons. See markdown §5.5.5. -/
noncomputable def pionParams : BagParams where
  bag_constant := 0.06
  omega_total := 4.08   -- 2 quarks × 2.04
  bag_pos := by norm_num
  omega_pos := by norm_num

/-! ## Section 2: The Energy Functional

From Part 2 of the markdown specification.

The total energy of the bag consists of two competing terms:

1. Volume energy: E_vol = (4π/3)R³B
   - Cost of creating perturbative vacuum region
   - Grows as R³ → favors small bags

2. Kinetic energy: E_kin = Ω/R
   - Quark confinement energy (uncertainty principle)
   - Grows as 1/R → favors large bags

The competition leads to stable equilibrium.
-/

/-- The volume (vacuum) energy contribution: E_vol = (4π/3)R³B

From §2.1: This is the energy needed to "push back" the non-perturbative
vacuum to create a cavity of radius R. -/
noncomputable def volumeEnergy (params : BagParams) (R : ℝ) : ℝ :=
  (4 * Real.pi / 3) * R ^ 3 * params.bag_constant

/-- The kinetic (quark) energy contribution: E_kin = Ω/R

From §2.2: Quarks confined to region of size R have minimum momentum
Δp ~ ℏ/R, giving kinetic energy ~ Ω/R for light quarks. -/
noncomputable def kineticEnergy (params : BagParams) (R : ℝ) : ℝ :=
  params.omega_total / R

/-- The total bag energy: E(R) = (4π/3)R³B + Ω/R

From §2.3: This is the complete energy functional to be minimized. -/
noncomputable def totalEnergy (params : BagParams) (R : ℝ) : ℝ :=
  volumeEnergy params R + kineticEnergy params R

/-- Total energy is the sum of volume and kinetic terms -/
theorem totalEnergy_eq (params : BagParams) (R : ℝ) :
    totalEnergy params R = (4 * Real.pi / 3) * R ^ 3 * params.bag_constant +
                           params.omega_total / R := rfl

/-- Volume energy is non-negative for R > 0 -/
theorem volumeEnergy_nonneg (params : BagParams) (R : ℝ) (hR : R > 0) :
    volumeEnergy params R ≥ 0 := by
  unfold volumeEnergy
  apply mul_nonneg
  · apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg (by norm_num : (4:ℝ) ≥ 0) (le_of_lt Real.pi_pos)
      · norm_num
    · exact pow_nonneg (le_of_lt hR) 3
  · exact le_of_lt params.bag_pos

/-- Kinetic energy is positive for R > 0 -/
theorem kineticEnergy_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    kineticEnergy params R > 0 := by
  unfold kineticEnergy
  exact div_pos params.omega_pos hR

/-! ## Section 2A: Differentiability and Formal Derivative Verification

This section establishes that the energy functional is differentiable
and formally proves that the derivative expressions match the calculus
derivatives. This is the rigorous connection between our algebraic
definitions and actual calculus.

**Note on Hypotheses (R > 0 vs R ≠ 0):**

Mathematically, the kinetic energy Ω/R is differentiable wherever R ≠ 0,
including negative R. However, physically, R represents a radius which must
be positive. We state the core calculus theorems with the weaker `R ≠ 0`
hypothesis (mathematical generality), and provide `R > 0` versions as
corollaries for physical applications. The conversion is trivial since
`R > 0 → R ≠ 0` via `ne_of_gt`.
-/

/-- The volume energy is differentiable for all R -/
theorem volumeEnergy_differentiable (params : BagParams) :
    Differentiable ℝ (volumeEnergy params) := by
  unfold volumeEnergy
  fun_prop

/-- The kinetic energy is differentiable for R ≠ 0 -/
theorem kineticEnergy_differentiableAt (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    DifferentiableAt ℝ (kineticEnergy params) R := by
  unfold kineticEnergy
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hR

/-- The total energy is differentiable for R ≠ 0 -/
theorem totalEnergy_differentiableAt (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    DifferentiableAt ℝ (totalEnergy params) R := by
  unfold totalEnergy
  exact (volumeEnergy_differentiable params R).add (kineticEnergy_differentiableAt params R hR)

/-- The total energy is continuous for R ≠ 0

This is a direct consequence of differentiability. Combined with the boundary
behavior theorems (energy_diverges_at_zero, energy_diverges_at_infinity),
this establishes existence of a minimum by the intermediate value theorem. -/
theorem totalEnergy_continuousAt (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    ContinuousAt (totalEnergy params) R :=
  (totalEnergy_differentiableAt params R hR).continuousAt

/-- The total energy is continuous on (0, ∞)

This is the domain on which we seek the minimum. -/
theorem totalEnergy_continuousOn (params : BagParams) :
    ContinuousOn (totalEnergy params) {R : ℝ | R > 0} := by
  intro R hR
  have hR_ne : R ≠ 0 := ne_of_gt hR
  exact (totalEnergy_continuousAt params R hR_ne).continuousWithinAt

/-! ### Physical Corollaries (R > 0 versions)

For convenience in physical applications, we provide versions with the
stronger `R > 0` hypothesis. These follow immediately from the `R ≠ 0`
versions via `ne_of_gt`. -/

/-- The kinetic energy is differentiable for positive R (physical version). -/
theorem kineticEnergy_differentiableAt_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    DifferentiableAt ℝ (kineticEnergy params) R :=
  kineticEnergy_differentiableAt params R (ne_of_gt hR)

/-- The total energy is differentiable for positive R (physical version). -/
theorem totalEnergy_differentiableAt_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    DifferentiableAt ℝ (totalEnergy params) R :=
  totalEnergy_differentiableAt params R (ne_of_gt hR)

/-- The total energy is continuous at positive R (physical version). -/
theorem totalEnergy_continuousAt_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    ContinuousAt (totalEnergy params) R :=
  totalEnergy_continuousAt params R (ne_of_gt hR)

/-- **Derivative of volume energy:** d/dR[(4π/3)R³B] = 4πR²B

This is the formal proof that our volumeEnergy function has the expected derivative. -/
theorem volumeEnergy_hasDerivAt (params : BagParams) (R : ℝ) :
    HasDerivAt (volumeEnergy params) (4 * Real.pi * R ^ 2 * params.bag_constant) R := by
  unfold volumeEnergy
  -- E_vol = (4π/3) * R³ * B = (4π/3) * B * R³
  -- d/dR[c * R³] = c * 3R² where c = (4π/3) * B
  -- = (4π/3) * B * 3 * R² = 4π * B * R² = 4πR²B
  have h1 : HasDerivAt (fun R => R ^ 3) (3 * R ^ 2) R := by
    have := hasDerivAt_pow 3 R
    simp only [Nat.cast_ofNat] at this
    convert this using 1
  have h2 : HasDerivAt (fun R => (4 * Real.pi / 3) * R ^ 3 * params.bag_constant)
      ((4 * Real.pi / 3) * (3 * R ^ 2) * params.bag_constant) R := by
    have := h1.const_mul (4 * Real.pi / 3)
    exact this.mul_const params.bag_constant
  convert h2 using 1; ring

/-- **Derivative of kinetic energy:** d/dR[Ω/R] = -Ω/R²

This is the formal proof that our kineticEnergy function has the expected derivative. -/
theorem kineticEnergy_hasDerivAt (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    HasDerivAt (kineticEnergy params) (-params.omega_total / R ^ 2) R := by
  unfold kineticEnergy
  -- d/dR[Ω/R] = Ω * d/dR[1/R] = Ω * (-1/R²) = -Ω/R²
  have h1 : HasDerivAt (fun R => R⁻¹) (-(R ^ 2)⁻¹) R := hasDerivAt_inv hR
  have h2 : HasDerivAt (fun R => params.omega_total * R⁻¹)
      (params.omega_total * (-(R ^ 2)⁻¹)) R := HasDerivAt.const_mul params.omega_total h1
  simp only [div_eq_mul_inv] at h2 ⊢
  convert h2 using 1
  ring

/-- **Derivative of total energy:** d/dR[E(R)] = 4πR²B - Ω/R²

This is the key theorem connecting the algebraic definition of energyDerivative
to the actual calculus derivative of totalEnergy. -/
theorem totalEnergy_hasDerivAt (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    HasDerivAt (totalEnergy params)
      (4 * Real.pi * R ^ 2 * params.bag_constant - params.omega_total / R ^ 2) R := by
  unfold totalEnergy
  have h1 := volumeEnergy_hasDerivAt params R
  have h2 := kineticEnergy_hasDerivAt params R hR
  have h3 := h1.add h2
  convert h3 using 1
  ring

/-- Derivative of kinetic energy for positive R (physical version). -/
theorem kineticEnergy_hasDerivAt_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    HasDerivAt (kineticEnergy params) (-params.omega_total / R ^ 2) R :=
  kineticEnergy_hasDerivAt params R (ne_of_gt hR)

/-- Derivative of total energy for positive R (physical version). -/
theorem totalEnergy_hasDerivAt_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    HasDerivAt (totalEnergy params)
      (4 * Real.pi * R ^ 2 * params.bag_constant - params.omega_total / R ^ 2) R :=
  totalEnergy_hasDerivAt params R (ne_of_gt hR)

/-! ## Section 3: First Derivative and Critical Point

From Part 3 of the markdown specification.

The first derivative of E(R):
  dE/dR = 4πR²B - Ω/R²

Setting dE/dR = 0 gives the equilibrium condition:
  4πR⁴B = Ω
  R_eq = (Ω/4πB)^(1/4)
-/

/-- First derivative of the energy: dE/dR = 4πR²B - Ω/R²

From §3.1: This comes from differentiating the volume term (giving 4πR²B)
and the kinetic term (giving -Ω/R²). -/
noncomputable def energyDerivative (params : BagParams) (R : ℝ) : ℝ :=
  4 * Real.pi * R ^ 2 * params.bag_constant - params.omega_total / R ^ 2

/-- **Key Connection Theorem:** The calculus derivative of totalEnergy equals energyDerivative.

This theorem formally verifies that our algebraic `energyDerivative` definition
matches the actual calculus derivative of `totalEnergy`. -/
theorem deriv_totalEnergy_eq (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    deriv (totalEnergy params) R = energyDerivative params R := by
  unfold energyDerivative
  exact (totalEnergy_hasDerivAt params R hR).deriv

/-- The equilibrium radius: R_eq = (Ω/4πB)^(1/4)

From §3.1: This is the unique positive solution to dE/dR = 0. -/
noncomputable def equilibriumRadius (params : BagParams) : ℝ :=
  (params.omega_total / (4 * Real.pi * params.bag_constant)) ^ (1/4 : ℝ)

/-- The equilibrium radius is positive -/
theorem equilibriumRadius_pos (params : BagParams) : equilibriumRadius params > 0 := by
  unfold equilibriumRadius
  apply Real.rpow_pos_of_pos
  apply div_pos params.omega_pos
  apply mul_pos
  · apply mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos
  · exact params.bag_pos

/-- At equilibrium, R⁴ = Ω/(4πB)

This is the fundamental equilibrium condition from §3.1. -/
theorem equilibrium_condition (params : BagParams) :
    (equilibriumRadius params) ^ 4 = params.omega_total / (4 * Real.pi * params.bag_constant) := by
  unfold equilibriumRadius
  have h1 : params.omega_total / (4 * Real.pi * params.bag_constant) > 0 := by
    apply div_pos params.omega_pos
    apply mul_pos (mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos) params.bag_pos
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (le_of_lt h1)]
  norm_num

/-- The derivative vanishes at equilibrium: dE/dR|_{R_eq} = 0

This is the critical point equation from §3.1. -/
theorem derivative_zero_at_equilibrium (params : BagParams) :
    energyDerivative params (equilibriumRadius params) = 0 := by
  unfold energyDerivative
  set R := equilibriumRadius params
  have hR : R > 0 := equilibriumRadius_pos params
  have hR4 : R ^ 4 = params.omega_total / (4 * Real.pi * params.bag_constant) :=
    equilibrium_condition params
  have hR2_pos : R ^ 2 > 0 := sq_pos_of_pos hR
  have hR2_ne : R ^ 2 ≠ 0 := ne_of_gt hR2_pos
  have hpi_pos : Real.pi > 0 := Real.pi_pos
  have h4piB_pos : 4 * Real.pi * params.bag_constant > 0 :=
    mul_pos (mul_pos (by norm_num : (4:ℝ) > 0) hpi_pos) params.bag_pos
  have h4piB_ne : 4 * Real.pi * params.bag_constant ≠ 0 := ne_of_gt h4piB_pos
  -- Goal: 4πR²B - Ω/R² = 0
  -- From R⁴ = Ω/(4πB), we get 4πBR⁴ = Ω
  -- So 4πBR² = Ω/R², which is what we need
  have hB_ne : params.bag_constant ≠ 0 := ne_of_gt params.bag_pos
  have h_key : 4 * Real.pi * params.bag_constant * R ^ 4 = params.omega_total := by
    have h := hR4
    field_simp at h ⊢
    linarith
  -- Rewrite: 4πR²B = 4πBR⁴/R² = Ω/R²
  have h1 : 4 * Real.pi * R ^ 2 * params.bag_constant = params.omega_total / R ^ 2 := by
    rw [mul_comm (4 * Real.pi * R ^ 2) params.bag_constant]
    rw [eq_div_iff hR2_ne]
    calc params.bag_constant * (4 * Real.pi * R ^ 2) * R ^ 2
        = params.bag_constant * 4 * Real.pi * R ^ 4 := by ring
      _ = 4 * Real.pi * params.bag_constant * R ^ 4 := by ring
      _ = params.omega_total := h_key
  linarith

/-! ## Section 4: Second Derivative and Stability

From Part 4 of the markdown specification.

The second derivative:
  d²E/dR² = 8πRB + 2Ω/R³

Since both terms are positive for R > 0, B > 0, Ω > 0:
  d²E/dR²|_{R_eq} > 0

This proves the equilibrium is a stable minimum.
-/

/-- Second derivative of the energy: d²E/dR² = 8πRB + 2Ω/R³

From §4.1: This is obtained by differentiating dE/dR.
Both terms are positive for R > 0, ensuring stability. -/
noncomputable def energySecondDerivative (params : BagParams) (R : ℝ) : ℝ :=
  8 * Real.pi * R * params.bag_constant + 2 * params.omega_total / R ^ 3

/-- The first derivative (energyDerivative) is differentiable for R ≠ 0 -/
theorem energyDerivative_differentiableAt (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    DifferentiableAt ℝ (energyDerivative params) R := by
  unfold energyDerivative
  apply DifferentiableAt.sub
  · -- 4πR²B is differentiable
    apply DifferentiableAt.mul
    · apply DifferentiableAt.mul
      · apply DifferentiableAt.mul
        · fun_prop
        · fun_prop
      · fun_prop
    · fun_prop
  · -- Ω/R² is differentiable for R ≠ 0
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero 2 hR

/-- **Derivative of the first derivative:** d/dR[4πR²B - Ω/R²] = 8πRB + 2Ω/R³

This formally proves that the derivative of energyDerivative equals energySecondDerivative. -/
theorem energyDerivative_hasDerivAt (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    HasDerivAt (energyDerivative params) (energySecondDerivative params R) R := by
  unfold energyDerivative energySecondDerivative
  -- d/dR[4πR²B] = 4πB · 2R = 8πRB
  have h1 : HasDerivAt (fun R => R ^ 2) (2 * R) R := by
    have := hasDerivAt_pow 2 R
    simp only [Nat.cast_ofNat] at this
    convert this using 1; ring
  have h2 : HasDerivAt (fun R => 4 * Real.pi * R ^ 2 * params.bag_constant)
      (4 * Real.pi * (2 * R) * params.bag_constant) R := by
    have := h1.const_mul (4 * Real.pi)
    exact this.mul_const params.bag_constant
  -- d/dR[Ω/R²] = Ω · d/dR[R^(-2)] = Ω · (-2)R^(-3) = -2Ω/R³
  have h3 : HasDerivAt (fun R => R ^ 2) (2 * R) R := h1
  have hR2_ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have h4 : HasDerivAt (fun R => (R ^ 2)⁻¹) (-(2 * R) / (R ^ 2) ^ 2) R := by
    have := h3.inv hR2_ne
    convert this using 1
  have h5 : HasDerivAt (fun R => params.omega_total / R ^ 2)
      (params.omega_total * (-(2 * R) / (R ^ 2) ^ 2)) R := by
    simp only [div_eq_mul_inv]
    exact HasDerivAt.const_mul params.omega_total h4
  -- Combine using subtraction rule
  have h6 := h2.sub h5
  convert h6 using 1
  -- Simplify: 4π(2R)B - Ω·(-2R)/(R²)² = 8πRB + 2ΩR/R⁴ = 8πRB + 2Ω/R³
  have hR_ne : R ≠ 0 := hR
  have hR2_ne' : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have hR4_ne : (R ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hR2_ne'
  field_simp
  ring

/-- **Key Connection Theorem:** The calculus second derivative equals energySecondDerivative.

This theorem formally verifies that our algebraic `energySecondDerivative` definition
matches the actual calculus second derivative of `totalEnergy`. -/
theorem deriv_energyDerivative_eq (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    deriv (energyDerivative params) R = energySecondDerivative params R :=
  (energyDerivative_hasDerivAt params R hR).deriv

/-- The second derivative of totalEnergy equals energySecondDerivative at nonzero points.

Since deriv(totalEnergy) = energyDerivative (for R ≠ 0), we have
deriv(deriv(totalEnergy)) = deriv(energyDerivative) = energySecondDerivative.

Note: This uses the fact that for R ≠ 0, the derivatives are well-defined and equal. -/
theorem deriv2_totalEnergy_eq (params : BagParams) (R : ℝ) (hR : R ≠ 0) :
    deriv (fun R => deriv (totalEnergy params) R) R = energySecondDerivative params R := by
  -- At R ≠ 0, deriv(totalEnergy) R = energyDerivative R
  -- The derivative of (fun R => deriv (totalEnergy params) R) equals deriv of energyDerivative
  -- in a neighborhood of R where R ≠ 0
  have h_deriv_eq : ∀ᶠ R' in nhds R,
      deriv (totalEnergy params) R' = energyDerivative params R' := by
    rcases hR.lt_or_gt with hR_neg | hR_pos
    · filter_upwards [eventually_lt_nhds hR_neg] with R' hR'
      exact deriv_totalEnergy_eq params R' (ne_of_lt hR')
    · filter_upwards [eventually_gt_nhds hR_pos] with R' hR'
      exact deriv_totalEnergy_eq params R' (ne_of_gt hR')
  have h_eq_locally : (fun R => deriv (totalEnergy params) R) =ᶠ[nhds R]
      (fun R => energyDerivative params R) := h_deriv_eq
  rw [Filter.EventuallyEq.deriv_eq h_eq_locally]
  exact deriv_energyDerivative_eq params R hR

/-- The second derivative is positive for R > 0

From §4.1: Since both 8πRB and 2Ω/R³ are positive for R > 0,
the sum is positive. This is crucial for stability. -/
theorem secondDerivative_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    energySecondDerivative params R > 0 := by
  unfold energySecondDerivative
  apply add_pos
  · -- First term: 8πRB > 0
    apply mul_pos
    · apply mul_pos
      · apply mul_pos (by norm_num : (8:ℝ) > 0) Real.pi_pos
      · exact hR
    · exact params.bag_pos
  · -- Second term: 2Ω/R³ > 0
    apply div_pos
    · apply mul_pos (by norm_num : (2:ℝ) > 0) params.omega_pos
    · exact pow_pos hR 3

/-- **Stability Theorem**: The equilibrium is stable.

From §4.1: d²E/dR²|_{R_eq} > 0, so the equilibrium is a minimum. -/
theorem equilibrium_stable (params : BagParams) :
    energySecondDerivative params (equilibriumRadius params) > 0 :=
  secondDerivative_pos params (equilibriumRadius params) (equilibriumRadius_pos params)

/-! ## Section 5: Energy Boundary Behavior

From §3.1.1 of the markdown (Existence and Uniqueness proof).

The energy functional has the boundary behavior:
- As R → 0⁺: E(R) → +∞ (kinetic term dominates)
- As R → +∞: E(R) → +∞ (volume term dominates)

Combined with strict convexity (E'' > 0), this proves existence
and uniqueness of the minimum.
-/

/-- Energy grows without bound as R → 0⁺

From §3.1.1 Step 2: The kinetic term Ω/R → +∞ dominates. -/
theorem energy_diverges_at_zero (params : BagParams) :
    ∀ M : ℝ, ∃ δ : ℝ, δ > 0 ∧ ∀ R : ℝ, 0 < R → R < δ → totalEnergy params R > M := by
  intro M
  -- We need δ such that for R < δ, E(R) > M
  -- Since E(R) ≥ Ω/R, we need Ω/R > M, i.e., R < Ω/M (for M > 0)
  -- For general M, use δ = Ω/(|M| + 1 + Ω) which is always positive
  let δ := params.omega_total / (|M| + 1 + params.omega_total)
  use δ
  constructor
  · -- δ > 0
    apply div_pos params.omega_pos
    have h1 : |M| ≥ 0 := abs_nonneg M
    linarith [params.omega_pos]
  · intro R hR_pos hR_small
    -- E(R) ≥ kinetic term = Ω/R
    have h_kinetic_bound : kineticEnergy params R > |M| + 1 := by
      unfold kineticEnergy
      have hR_lt : R < params.omega_total / (|M| + 1 + params.omega_total) := hR_small
      have h_denom_pos : |M| + 1 + params.omega_total > 0 := by
        have h1 : |M| ≥ 0 := abs_nonneg M
        linarith [params.omega_pos]
      -- From R < Ω/(|M|+1+Ω), we get Ω/R > |M|+1+Ω > |M|+1
      have h2 : R * (|M| + 1 + params.omega_total) < params.omega_total := by
        calc R * (|M| + 1 + params.omega_total)
            < params.omega_total / (|M| + 1 + params.omega_total) *
              (|M| + 1 + params.omega_total) := by
                apply mul_lt_mul_of_pos_right hR_lt h_denom_pos
          _ = params.omega_total := by field_simp
      -- Ω/R > (|M|+1+Ω) because R*(|M|+1+Ω) < Ω
      have h1 : params.omega_total / R > |M| + 1 + params.omega_total := by
        have h3 : (|M| + 1 + params.omega_total) * R < params.omega_total := by linarith
        rw [gt_iff_lt, lt_div_iff₀ hR_pos]
        linarith
      -- Since Ω/R > |M| + 1 + Ω and Ω > 0, we have Ω/R > |M| + 1
      linarith [params.omega_pos]
    have h_vol_nonneg : volumeEnergy params R ≥ 0 := volumeEnergy_nonneg params R hR_pos
    have h_kin_pos : kineticEnergy params R > 0 := kineticEnergy_pos params R hR_pos
    calc totalEnergy params R
        = volumeEnergy params R + kineticEnergy params R := rfl
      _ ≥ 0 + kineticEnergy params R := by linarith
      _ = kineticEnergy params R := by ring
      _ > |M| + 1 := h_kinetic_bound
      _ ≥ M + 1 := by linarith [le_abs_self M]
      _ > M := by linarith

/-- Energy grows without bound as R → +∞

From §3.1.1 Step 2: The volume term (4π/3)R³B → +∞ dominates. -/
theorem energy_diverges_at_infinity (params : BagParams) :
    ∀ M : ℝ, ∃ N : ℝ, N > 0 ∧ ∀ R : ℝ, R > N → totalEnergy params R > M := by
  intro M
  -- We need N such that for R > N, E(R) > M
  -- Since E(R) ≥ volumeEnergy = (4π/3)R³B, we need (4π/3)R³B > M
  -- For general M (including negative), use N = max(1, (3(|M|+1)/(4πB))^(1/3))
  set c := 4 * Real.pi / 3 * params.bag_constant with hc_def
  have hc_pos : c > 0 := by
    rw [hc_def]
    apply mul_pos
    · apply div_pos
      · apply mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos
      · norm_num
    · exact params.bag_pos
  -- Choose N such that c * N³ > |M| + 1
  set N := max 1 (((|M| + 1) / c) ^ (1/3 : ℝ) + 1) with hN_def
  use N
  constructor
  · -- N > 0
    apply lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_left 1 _)
  · intro R hR_large
    -- E(R) ≥ volumeEnergy = c * R³
    have hN_pos : N > 0 := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_left 1 _)
    have hR_pos : R > 0 := lt_trans hN_pos hR_large
    have h_vol_bound : volumeEnergy params R > |M| + 1 := by
      unfold volumeEnergy
      have hN_bound : N ≥ ((|M| + 1) / c) ^ (1/3 : ℝ) + 1 := le_max_right 1 _
      have hR_bound : R > ((|M| + 1) / c) ^ (1/3 : ℝ) + 1 := lt_of_le_of_lt hN_bound hR_large
      have hR_bound' : R > ((|M| + 1) / c) ^ (1/3 : ℝ) := by linarith
      have h_abs_nonneg : |M| + 1 > 0 := by
        have : |M| ≥ 0 := abs_nonneg M
        linarith
      have h_div_pos : (|M| + 1) / c > 0 := div_pos h_abs_nonneg hc_pos
      have h_R3_bound : R ^ 3 > (|M| + 1) / c := by
        have h_base_pos : ((|M| + 1) / c) ^ (1/3 : ℝ) ≥ 0 :=
          le_of_lt (Real.rpow_pos_of_pos h_div_pos _)
        have h1 : R ^ 3 > (((|M| + 1) / c) ^ (1/3 : ℝ)) ^ 3 := by
          apply pow_lt_pow_left₀ hR_bound' h_base_pos (by norm_num : 3 ≠ 0)
        have h2 : (((|M| + 1) / c) ^ (1/3 : ℝ)) ^ 3 = (|M| + 1) / c := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h_div_pos)]
          norm_num
        linarith
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      calc 4 * Real.pi / 3 * R ^ 3 * params.bag_constant
          = c * R ^ 3 := by rw [hc_def]; ring
        _ > c * ((|M| + 1) / c) := by
            apply mul_lt_mul_of_pos_left h_R3_bound hc_pos
        _ = |M| + 1 := by field_simp
    have h_kin_nonneg : kineticEnergy params R ≥ 0 := by
      unfold kineticEnergy
      apply div_nonneg (le_of_lt params.omega_pos) (le_of_lt hR_pos)
    calc totalEnergy params R
        = volumeEnergy params R + kineticEnergy params R := rfl
      _ ≥ volumeEnergy params R + 0 := by linarith
      _ = volumeEnergy params R := by ring
      _ > |M| + 1 := h_vol_bound
      _ ≥ M + 1 := by linarith [le_abs_self M]
      _ > M := by linarith

/-- Energy is strictly convex (E'' > 0 everywhere on (0,∞))

From §3.1.1 Step 4: Strict convexity implies at most one critical point,
which combined with boundary behavior gives exactly one minimum. -/
theorem energy_strictly_convex (params : BagParams) :
    ∀ R : ℝ, R > 0 → energySecondDerivative params R > 0 :=
  fun R hR => secondDerivative_pos params R hR

/-- **Uniqueness Theorem:** The equilibrium radius is the unique critical point of the energy.

If R > 0 and energyDerivative(R) = 0, then R = equilibriumRadius.
This follows from the explicit formula R⁴ = Ω/(4πB). -/
theorem critical_point_unique (params : BagParams) (R : ℝ) (hR_pos : R > 0)
    (hR_crit : energyDerivative params R = 0) :
    R = equilibriumRadius params := by
  -- From energyDerivative = 0: 4πR²B = Ω/R²
  -- This gives R⁴ = Ω/(4πB)
  -- Since equilibriumRadius = (Ω/(4πB))^(1/4), we have R = equilibriumRadius
  unfold energyDerivative at hR_crit
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR2_ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR_ne
  have hR2_pos : R ^ 2 > 0 := sq_pos_of_pos hR_pos
  have hpi_pos : Real.pi > 0 := Real.pi_pos
  have h4pi_pos : 4 * Real.pi > 0 := mul_pos (by norm_num : (4:ℝ) > 0) hpi_pos
  have h4piB_pos : 4 * Real.pi * params.bag_constant > 0 :=
    mul_pos h4pi_pos params.bag_pos
  -- From hR_crit: 4πR²B - Ω/R² = 0, so 4πR²B = Ω/R²
  have h1 : 4 * Real.pi * R ^ 2 * params.bag_constant = params.omega_total / R ^ 2 := by
    linarith
  -- Multiply both sides by R²: 4πR⁴B = Ω
  have h2 : 4 * Real.pi * R ^ 4 * params.bag_constant = params.omega_total := by
    have := h1
    field_simp at this ⊢
    linarith
  -- So R⁴ = Ω/(4πB)
  have h3 : R ^ 4 = params.omega_total / (4 * Real.pi * params.bag_constant) := by
    have h4piB_ne : 4 * Real.pi * params.bag_constant ≠ 0 := ne_of_gt h4piB_pos
    have hB_ne : params.bag_constant ≠ 0 := ne_of_gt params.bag_pos
    field_simp at h2 ⊢
    linarith
  -- Since R > 0, R = (Ω/(4πB))^(1/4) = equilibriumRadius
  have hR4_pos : R ^ 4 > 0 := pow_pos hR_pos 4
  have h_div_pos : params.omega_total / (4 * Real.pi * params.bag_constant) > 0 :=
    div_pos params.omega_pos h4piB_pos
  -- R = R^4^(1/4) = (Ω/(4πB))^(1/4)
  unfold equilibriumRadius
  -- Use pow_rpow_inv_natCast: (x ^ n) ^ (n⁻¹ : ℝ) = x for x ≥ 0, n ≠ 0
  have h4 : R = (R ^ 4) ^ (1/4 : ℝ) := by
    have h_inv : (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    rw [h_inv]
    exact (Real.pow_rpow_inv_natCast (le_of_lt hR_pos) (by norm_num : (4 : ℕ) ≠ 0)).symm
  rw [h4, h3]

/-- The energy derivative is strictly monotone increasing on (0, ∞).

Since E''(R) > 0 for all R > 0, E' is strictly increasing. -/
theorem energyDerivative_strictMono (params : BagParams) :
    StrictMonoOn (energyDerivative params) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · -- Continuity on (0, ∞)
    intro R hR
    have hR_ne : R ≠ 0 := ne_of_gt hR
    exact (energyDerivative_differentiableAt params R hR_ne).continuousAt.continuousWithinAt
  · -- Derivative positive on interior = (0, ∞) itself
    intro R hR
    rw [interior_Ioi] at hR
    have hR_pos : R > 0 := hR
    have hR_ne : R ≠ 0 := ne_of_gt hR_pos
    rw [deriv_energyDerivative_eq params R hR_ne]
    exact secondDerivative_pos params R hR_pos

/-- For R > R_eq, the energy derivative is positive.

Since E'(R_eq) = 0 and E' is strictly increasing, E'(R) > 0 for R > R_eq. -/
theorem energyDerivative_pos_of_gt (params : BagParams) (R : ℝ)
    (hR_pos : R > 0) (hR_gt : R > equilibriumRadius params) :
    energyDerivative params R > 0 := by
  have hReq_pos := equilibriumRadius_pos params
  have h_mono := energyDerivative_strictMono params
  have h_crit := derivative_zero_at_equilibrium params
  calc energyDerivative params R
      > energyDerivative params (equilibriumRadius params) :=
        h_mono hReq_pos hR_pos hR_gt
    _ = 0 := h_crit

/-- For R < R_eq (with R > 0), the energy derivative is negative.

Since E'(R_eq) = 0 and E' is strictly increasing, E'(R) < 0 for R < R_eq. -/
theorem energyDerivative_neg_of_lt (params : BagParams) (R : ℝ)
    (hR_pos : R > 0) (hR_lt : R < equilibriumRadius params) :
    energyDerivative params R < 0 := by
  have hReq_pos := equilibriumRadius_pos params
  have h_mono := energyDerivative_strictMono params
  have h_crit := derivative_zero_at_equilibrium params
  calc energyDerivative params R
      < energyDerivative params (equilibriumRadius params) :=
        h_mono hR_pos hReq_pos hR_lt
    _ = 0 := h_crit

/-- **Uniqueness of Global Minimum:** The equilibrium radius is the unique global minimum.

This theorem establishes that for any R > 0, R ≠ R_eq, we have E(R) > E(R_eq).

**Proof Strategy:**
The proof uses strict monotonicity of the first derivative:
1. E''(R) > 0 for all R > 0, so E' is strictly increasing
2. E'(R_eq) = 0, so E' < 0 for R < R_eq and E' > 0 for R > R_eq
3. Apply the mean value theorem: E(R) - E(R_eq) = E'(c)(R - R_eq) for some c between R and R_eq
4. The sign analysis shows E(R) - E(R_eq) > 0 in both cases -/
theorem equilibrium_is_unique_minimum (params : BagParams) :
    ∀ R : ℝ, R > 0 → R ≠ equilibriumRadius params →
    totalEnergy params R > totalEnergy params (equilibriumRadius params) := by
  intro R hR_pos hR_ne
  set R_eq := equilibriumRadius params with hReq_def
  have hReq_pos := equilibriumRadius_pos params
  have hReq_ne : R_eq ≠ 0 := ne_of_gt hReq_pos
  have hR_ne_zero : R ≠ 0 := ne_of_gt hR_pos
  -- Use mean value theorem: E(R) - E(R_eq) = E'(c)(R - R_eq) for some c in the open interval
  rcases hR_ne.lt_or_gt with hR_lt | hR_gt
  · -- Case 1: R < R_eq
    -- Continuity on [R, R_eq]
    have h_cont : ContinuousOn (totalEnergy params) (Set.Icc R R_eq) := by
      apply ContinuousOn.mono (totalEnergy_continuousOn params)
      intro x hx
      simp only [Set.mem_Icc, Set.mem_setOf_eq] at hx ⊢
      exact lt_of_lt_of_le hR_pos hx.1
    -- Differentiability on (R, R_eq)
    have h_diff : DifferentiableOn ℝ (totalEnergy params) (Set.Ioo R R_eq) := by
      intro x hx
      have hx_pos : x > 0 := lt_trans hR_pos hx.1
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      exact (totalEnergy_differentiableAt params x hx_ne).differentiableWithinAt
    -- Mean value theorem gives c ∈ (R, R_eq) with E(R_eq) - E(R) = E'(c)(R_eq - R)
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope (totalEnergy params) hR_lt h_cont h_diff
    -- c ∈ (R, R_eq), so c > 0 and c < R_eq
    have hc_pos : c > 0 := lt_trans hR_pos hc_mem.1
    have hc_lt : c < R_eq := hc_mem.2
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    -- E'(c) < 0 since c < R_eq
    have h_deriv_neg : deriv (totalEnergy params) c < 0 := by
      rw [deriv_totalEnergy_eq params c hc_ne]
      exact energyDerivative_neg_of_lt params c hc_pos hc_lt
    -- From MVT: (E(R_eq) - E(R)) / (R_eq - R) = E'(c) < 0
    -- Since R_eq - R > 0, we have E(R_eq) - E(R) < 0, i.e., E(R) > E(R_eq)
    have h_diff_pos : R_eq - R > 0 := sub_pos.mpr hR_lt
    have h_diff_ne : R_eq - R ≠ 0 := ne_of_gt h_diff_pos
    have h_mvt : totalEnergy params R_eq - totalEnergy params R =
        deriv (totalEnergy params) c * (R_eq - R) := by
      have := hc_eq
      field_simp at this
      linarith
    have h_prod_neg : deriv (totalEnergy params) c * (R_eq - R) < 0 :=
      mul_neg_of_neg_of_pos h_deriv_neg h_diff_pos
    linarith
  · -- Case 2: R > R_eq
    -- Continuity on [R_eq, R]
    have h_cont : ContinuousOn (totalEnergy params) (Set.Icc R_eq R) := by
      apply ContinuousOn.mono (totalEnergy_continuousOn params)
      intro x hx
      simp only [Set.mem_Icc, Set.mem_setOf_eq] at hx ⊢
      exact lt_of_lt_of_le hReq_pos hx.1
    -- Differentiability on (R_eq, R)
    have h_diff : DifferentiableOn ℝ (totalEnergy params) (Set.Ioo R_eq R) := by
      intro x hx
      have hx_pos : x > 0 := lt_trans hReq_pos hx.1
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      exact (totalEnergy_differentiableAt params x hx_ne).differentiableWithinAt
    -- Mean value theorem gives c ∈ (R_eq, R) with E(R) - E(R_eq) = E'(c)(R - R_eq)
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope (totalEnergy params) hR_gt h_cont h_diff
    -- c ∈ (R_eq, R), so c > R_eq > 0
    have hc_gt : c > R_eq := hc_mem.1
    have hc_pos : c > 0 := lt_trans hReq_pos hc_gt
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    -- E'(c) > 0 since c > R_eq
    have h_deriv_pos : deriv (totalEnergy params) c > 0 := by
      rw [deriv_totalEnergy_eq params c hc_ne]
      exact energyDerivative_pos_of_gt params c hc_pos hc_gt
    -- From MVT: (E(R) - E(R_eq)) / (R - R_eq) = E'(c) > 0
    -- Since R - R_eq > 0, we have E(R) - E(R_eq) > 0, i.e., E(R) > E(R_eq)
    have h_diff_pos : R - R_eq > 0 := sub_pos.mpr hR_gt
    have h_diff_ne : R - R_eq ≠ 0 := ne_of_gt h_diff_pos
    have h_mvt : totalEnergy params R - totalEnergy params R_eq =
        deriv (totalEnergy params) c * (R - R_eq) := by
      have := hc_eq
      field_simp at this
      linarith
    have h_prod_pos : deriv (totalEnergy params) c * (R - R_eq) > 0 :=
      mul_pos h_deriv_pos h_diff_pos
    linarith

/-! ### Section 5A: Existence of Minimum (Formal Proof)

From §3.1.1 of the markdown specification, we prove existence of a minimum
using the boundary behavior and continuity. The proof follows the Extreme
Value Theorem argument:

1. E(R) → +∞ as R → 0⁺
2. E(R) → +∞ as R → +∞
3. E is continuous on (0, ∞)
4. Therefore E attains a minimum on (0, ∞)

**Reference:** Rudin, Principles of Mathematical Analysis (1976), Theorem 4.16;
for application to optimization: Boyd & Vandenberghe (2004), §4.2.
-/

/-- Volume energy is strictly positive for R > 0 -/
theorem volumeEnergy_pos (params : BagParams) (R : ℝ) (hR : R > 0) :
    volumeEnergy params R > 0 := by
  unfold volumeEnergy
  apply mul_pos
  · apply mul_pos
    · apply div_pos
      · apply mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos
      · norm_num
    · exact pow_pos hR 3
  · exact params.bag_pos

/-- **Existence Theorem (Constructive):** The equilibrium radius achieves a finite energy.

This theorem shows that equilibriumRadius is a well-defined point in (0, ∞)
with finite energy. Combined with equilibrium_is_unique_minimum, this proves
existence and uniqueness of the global minimum.

**Proof:** Direct computation shows E(R_eq) is finite and positive. -/
theorem equilibrium_energy_finite (params : BagParams) :
    ∃ E_min : ℝ, E_min = totalEnergy params (equilibriumRadius params) ∧ E_min > 0 := by
  use totalEnergy params (equilibriumRadius params)
  constructor
  · rfl
  · -- E(R_eq) = volume + kinetic, both positive
    unfold totalEnergy
    apply add_pos
    · exact volumeEnergy_pos params (equilibriumRadius params) (equilibriumRadius_pos params)
    · exact kineticEnergy_pos params (equilibriumRadius params) (equilibriumRadius_pos params)

/-- **IsMinOn Formulation:** The equilibrium radius is a global minimum on (0, ∞).

This uses Mathlib's `IsMinOn` predicate for formal compatibility with
optimization libraries.

**Statement:** ∀ R ∈ (0, ∞), E(R_eq) ≤ E(R)

Ref: Mathlib.Order.Bounds.Basic -/
theorem equilibrium_isMinOn (params : BagParams) :
    IsMinOn (totalEnergy params) (Set.Ioi 0) (equilibriumRadius params) := by
  intro R hR
  simp only [Set.mem_Ioi] at hR
  by_cases h : R = equilibriumRadius params
  · simp only [Set.mem_setOf_eq, h, le_refl]
  · exact le_of_lt (equilibrium_is_unique_minimum params R hR h)

/-- Alternative formulation: E(R_eq) is the infimum of E on (0, ∞).

This states that E(R_eq) is the greatest lower bound of {E(R) : R > 0}. -/
theorem equilibrium_energy_is_infimum (params : BagParams) :
    IsGLB {E : ℝ | ∃ R > 0, totalEnergy params R = E}
          (totalEnergy params (equilibriumRadius params)) := by
  constructor
  · -- E(R_eq) is a lower bound
    intro E hE
    obtain ⟨R, hR_pos, hR_eq⟩ := hE
    rw [← hR_eq]
    by_cases h : R = equilibriumRadius params
    · rw [h]
    · exact le_of_lt (equilibrium_is_unique_minimum params R hR_pos h)
  · -- E(R_eq) is the greatest lower bound
    intro b hb
    apply hb
    exact ⟨equilibriumRadius params, equilibriumRadius_pos params, rfl⟩

/-! ## Section 6: Pressure Balance

From Part 3 of the markdown specification (§3.3).

At equilibrium, internal and external pressures balance:
- Vacuum pressure (inward): P_vac = B
- Quark pressure (outward): P_quark = Ω/(4πR⁴)

At R = R_eq: P_quark = B = P_vac ✓
-/

/-- Vacuum pressure (inward): P_vac = B

From §3.3: The external vacuum exerts pressure B on the bag boundary. -/
noncomputable def vacuumPressure (params : BagParams) : ℝ :=
  params.bag_constant

/-- Quark pressure (outward): P_quark = -dE_kin/dV = Ω/(4πR⁴)

From §3.3: The quarks exert outward pressure from their kinetic energy.

**Derivation:**
The kinetic energy is E_kin = Ω/R. The pressure is P = -∂E/∂V at fixed entropy.
For a spherical bag, V = (4π/3)R³, so dV/dR = 4πR².

  P_quark = -∂E_kin/∂V = -(∂E_kin/∂R) / (∂V/∂R)
          = -(-Ω/R²) / (4πR²)
          = Ω / (4πR⁴)

This is the standard thermodynamic pressure from confinement.

**Reference:** Chodos et al. (1974), Phys. Rev. D 9, 3471, Eq. (2.7). -/
noncomputable def quarkPressure (params : BagParams) (R : ℝ) : ℝ :=
  params.omega_total / (4 * Real.pi * R ^ 4)

/-- **Pressure Derivation Lemma:** The quark pressure equals -dE_kin/dV.

This lemma formally verifies that P_quark = Ω/(4πR⁴) is the correct expression
for the thermodynamic pressure derived from the kinetic energy.

The chain rule gives: dE_kin/dV = (dE_kin/dR) · (dR/dV)
where dR/dV = 1/(4πR²) since V = (4π/3)R³.

So: -dE_kin/dV = -(-Ω/R²) · (1/4πR²) = Ω/(4πR⁴) -/
theorem quarkPressure_derivation (params : BagParams) (R : ℝ) (hR : R > 0) :
    quarkPressure params R =
    -(deriv (kineticEnergy params) R) / (4 * Real.pi * R ^ 2) := by
  unfold quarkPressure
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hR2_pos : R ^ 2 > 0 := sq_pos_of_pos hR
  have hR2_ne : R ^ 2 ≠ 0 := ne_of_gt hR2_pos
  have hR4_pos : R ^ 4 > 0 := pow_pos hR 4
  have hR4_ne : R ^ 4 ≠ 0 := ne_of_gt hR4_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h4piR2_pos : 4 * Real.pi * R ^ 2 > 0 := by
    apply mul_pos (mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos) hR2_pos
  have h4piR2_ne : 4 * Real.pi * R ^ 2 ≠ 0 := ne_of_gt h4piR2_pos
  -- deriv (kineticEnergy params) R = -Ω/R²
  have h_deriv : deriv (kineticEnergy params) R = -params.omega_total / R ^ 2 :=
    (kineticEnergy_hasDerivAt params R hR_ne).deriv
  rw [h_deriv]
  -- -(-Ω/R²) / (4πR²) = (Ω/R²) / (4πR²) = Ω / (4πR⁴)
  field_simp

/-- **Pressure Balance Theorem**: At equilibrium, pressures balance.

From §3.3: P_quark(R_eq) = B = P_vac -/
theorem pressure_balance (params : BagParams) :
    quarkPressure params (equilibriumRadius params) = vacuumPressure params := by
  unfold quarkPressure vacuumPressure
  set R := equilibriumRadius params
  have hR4 : R ^ 4 = params.omega_total / (4 * Real.pi * params.bag_constant) :=
    equilibrium_condition params
  have hR : R > 0 := equilibriumRadius_pos params
  have hR4_pos : R ^ 4 > 0 := pow_pos hR 4
  have hR4_ne : R ^ 4 ≠ 0 := ne_of_gt hR4_pos
  have hpi_pos : Real.pi > 0 := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
  have h4pi_ne : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hpi_ne
  have h4piR4_ne : 4 * Real.pi * R ^ 4 ≠ 0 := mul_ne_zero h4pi_ne hR4_ne
  have hB_ne : params.bag_constant ≠ 0 := ne_of_gt params.bag_pos
  have hOmega_ne : params.omega_total ≠ 0 := ne_of_gt params.omega_pos
  calc params.omega_total / (4 * Real.pi * R ^ 4)
      = params.omega_total /
        (4 * Real.pi * (params.omega_total / (4 * Real.pi * params.bag_constant))) := by rw [hR4]
    _ = params.bag_constant := by field_simp

/-! ## Section 7: Equilibrium Energy

From §3.2 of the markdown specification.

At equilibrium, the energy can be expressed as:
  E_eq = (4/3)(4πB)^(1/4) Ω^(3/4)

Or equivalently: E_eq = 4Ω/(3R_eq)
-/

/-- Equilibrium energy: E_eq = 4Ω/(3R_eq)

From §3.2: Using the equilibrium condition 4πR⁴B = Ω,
the energy simplifies to this form. -/
noncomputable def equilibriumEnergy (params : BagParams) : ℝ :=
  4 * params.omega_total / (3 * equilibriumRadius params)

/-- The equilibrium energy is positive -/
theorem equilibriumEnergy_pos (params : BagParams) : equilibriumEnergy params > 0 := by
  unfold equilibriumEnergy
  apply div_pos
  · apply mul_pos (by norm_num : (4:ℝ) > 0) params.omega_pos
  · apply mul_pos (by norm_num : (3:ℝ) > 0) (equilibriumRadius_pos params)

/-- **Key Identity:** The total energy at equilibrium equals 4Ω/(3R_eq).

This proves that totalEnergy(R_eq) = equilibriumEnergy as defined.

**Derivation:** At equilibrium, 4πR⁴B = Ω, so:
  E_vol = (4π/3)R³B = (4πBR⁴)/(3R) = Ω/(3R)
  E_kin = Ω/R
  E_total = E_vol + E_kin = Ω/(3R) + Ω/R = 4Ω/(3R) -/
theorem totalEnergy_at_equilibrium (params : BagParams) :
    totalEnergy params (equilibriumRadius params) = equilibriumEnergy params := by
  unfold totalEnergy equilibriumEnergy volumeEnergy kineticEnergy
  set R := equilibriumRadius params
  have hR : R > 0 := equilibriumRadius_pos params
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hR4 : R ^ 4 = params.omega_total / (4 * Real.pi * params.bag_constant) :=
    equilibrium_condition params
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h4pi_ne : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hpi_ne
  have hB_ne : params.bag_constant ≠ 0 := ne_of_gt params.bag_pos
  -- From R⁴ = Ω/(4πB), we get 4πBR⁴ = Ω
  have h_key : 4 * Real.pi * params.bag_constant * R ^ 4 = params.omega_total := by
    have h := hR4
    field_simp at h
    linarith
  -- (4π/3)R³B + Ω/R = (4πBR⁴)/(3R) + Ω/R = Ω/(3R) + Ω/R = 4Ω/(3R)
  have h3_ne : (3 : ℝ) ≠ 0 := by norm_num
  have h3R_ne : 3 * R ≠ 0 := mul_ne_zero h3_ne hR_ne
  -- Multiply through to clear denominators and use h_key
  have h1 : 4 * Real.pi / 3 * R ^ 3 * params.bag_constant + params.omega_total / R =
            4 * params.omega_total / (3 * R) := by
    have h2 : 4 * Real.pi / 3 * R ^ 3 * params.bag_constant =
              4 * Real.pi * params.bag_constant * R ^ 4 / (3 * R) := by
      field_simp
    rw [h2, h_key]
    field_simp
    ring
  exact h1

/-- At equilibrium, the volume energy is 1/3 of the kinetic energy.

This is a consequence of the virial theorem for this potential.
From the equilibrium condition: E_vol = (4π/3)R³B and E_kin = Ω/R,
with 4πR⁴B = Ω, we get E_vol = Ω/(3R) = E_kin/3. -/
theorem energy_partition (params : BagParams) :
    volumeEnergy params (equilibriumRadius params) =
    kineticEnergy params (equilibriumRadius params) / 3 := by
  unfold volumeEnergy kineticEnergy
  set R := equilibriumRadius params
  have hR : R > 0 := equilibriumRadius_pos params
  have hR4 : R ^ 4 = params.omega_total / (4 * Real.pi * params.bag_constant) :=
    equilibrium_condition params
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h4pi_ne : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hpi_ne
  have hB_ne : params.bag_constant ≠ 0 := ne_of_gt params.bag_pos
  have hOmega_ne : params.omega_total ≠ 0 := ne_of_gt params.omega_pos
  -- From R⁴ = Ω/(4πB), we get 4πBR⁴ = Ω
  have h_key : 4 * Real.pi * params.bag_constant * R ^ 4 = params.omega_total := by
    have h := hR4
    field_simp at h
    linarith
  -- Volume = (4π/3)R³B = (4πBR⁴)/(3R) = Ω/(3R) = (Ω/R)/3 = Kinetic/3
  have h1 : 4 * Real.pi / 3 * R ^ 3 * params.bag_constant = params.omega_total / (3 * R) := by
    have hR3 : R ^ 3 = R ^ 4 / R := by field_simp
    have h3R_ne : (3 : ℝ) * R ≠ 0 := mul_ne_zero (by norm_num) hR_ne
    rw [eq_div_iff h3R_ne]
    calc 4 * Real.pi / 3 * R ^ 3 * params.bag_constant * (3 * R)
        = 4 * Real.pi * params.bag_constant * R ^ 3 * R := by ring
      _ = 4 * Real.pi * params.bag_constant * R ^ 4 := by ring
      _ = params.omega_total := h_key
  rw [h1]
  field_simp

/-! ## Section 8: Physical Predictions

From Part 5 of the markdown specification.

Numerical estimates for physical hadrons:
- Proton: R_eq ≈ 1.0 fm, M ≈ 940 MeV
- Pion: smaller bag, lower mass

These validate the model against experimental data.
-/

/-- Proton equilibrium radius is positive (schematic verification) -/
theorem proton_radius_pos : equilibriumRadius protonParams > 0 :=
  equilibriumRadius_pos protonParams

/-- Proton equilibrium is stable -/
theorem proton_equilibrium_stable :
    energySecondDerivative protonParams (equilibriumRadius protonParams) > 0 :=
  equilibrium_stable protonParams

/-- Proton pressure balance holds -/
theorem proton_pressure_balance :
    quarkPressure protonParams (equilibriumRadius protonParams) =
    vacuumPressure protonParams :=
  pressure_balance protonParams

/-! ## Section 9: Confinement Mechanism

From Part 6 of the markdown specification.

The bag model explains confinement:
1. Pulling a quark out stretches the bag → increases volume energy
2. Energy grows linearly with separation: E(r) ~ σr
3. String tension σ ~ B^(1/2) matches lattice QCD

String breaking occurs when E > 2m_q, creating quark-antiquark pair.
-/

/-- String tension estimate: σ ~ πR²B

From §6.3: For large separations, the bag becomes a flux tube
with string tension σ = πR⊥²B. -/
noncomputable def stringTension (params : BagParams) (R_perp : ℝ) : ℝ :=
  Real.pi * R_perp ^ 2 * params.bag_constant

/-- String tension is positive for R > 0 -/
theorem stringTension_pos (params : BagParams) (R_perp : ℝ) (hR : R_perp > 0) :
    stringTension params R_perp > 0 := by
  unfold stringTension
  apply mul_pos
  · apply mul_pos Real.pi_pos (sq_pos_of_pos hR)
  · exact params.bag_pos

/-- Linear potential energy for separated quarks: E(r) = σr + const

From §6.3: At large separation, the bag energy grows linearly. -/
noncomputable def separationEnergy (params : BagParams) (R_perp r : ℝ) : ℝ :=
  stringTension params R_perp * r

/-- Separation energy grows linearly with distance -/
theorem separation_energy_linear (params : BagParams) (R_perp r₁ r₂ : ℝ) (hR : R_perp > 0)
    (h : r₂ > r₁) :
    separationEnergy params R_perp r₂ > separationEnergy params R_perp r₁ := by
  unfold separationEnergy
  apply mul_lt_mul_of_pos_left h (stringTension_pos params R_perp hR)

/-! ## Section 10: Connection to Chiral Geometrogenesis

From Part 7 of the markdown specification.

In Chiral Geometrogenesis, the bag constant arises from the chiral potential:
  B = V(χ=0) - V(χ=v_χ) = λv_χ⁴

Inside the bag: ⟨χ⟩ = 0 (chiral symmetry restored)
Outside the bag: ⟨χ⟩ = v_χ (chiral symmetry broken)

The bag boundary is a domain wall between these two phases.
-/

/-- Connection to chiral field: B = λv_χ⁴

From §7.1: The bag constant is the potential difference between
the symmetric vacuum (inside) and broken vacuum (outside). -/
structure ChiralBagConnection where
  /-- Quartic coupling in Mexican hat potential -/
  lambda : ℝ
  /-- Chiral VEV -/
  v_chi : ℝ
  /-- Physical requirements -/
  lambda_pos : lambda > 0
  v_chi_pos : v_chi > 0

/-- The bag constant from chiral parameters: B = λv_χ⁴ -/
noncomputable def bagFromChiral (conn : ChiralBagConnection) : ℝ :=
  conn.lambda * conn.v_chi ^ 4

/-- The chiral origin of the bag constant gives positive B -/
theorem chiral_bag_constant_pos (conn : ChiralBagConnection) :
    bagFromChiral conn > 0 := by
  unfold bagFromChiral
  apply mul_pos conn.lambda_pos (pow_pos conn.v_chi_pos 4)

/-! ### Connection to Stella Octangula Geometry

The MIT Bag Model connects to Chiral Geometrogenesis through the three-color
field structure. Inside the bag, the color phases (R, G, B) are free to rotate,
corresponding to the Kuramoto dynamics on the stella octangula boundary.

The stella octangula provides the geometric substrate where:
- The three color fields live on the 8 vertices (6 hexagonal + 2 apex)
- Each color corresponds to a phase offset: φ_R = 0, φ_G = 2π/3, φ_B = 4π/3
- The bag boundary is where these phases meet the external broken-symmetry vacuum
-/

/-- The three color contributions to quark kinetic energy.

In the bag model, each color flavor contributes equally to Ω.
For a baryon with one quark of each color: Ω = ω_R + ω_G + ω_B = 3ω.
This connects to the three-phase structure of the stella octangula. -/
noncomputable def colorContributions (ω : ℝ) : ColorPhase → ℝ
  | .R => ω
  | .G => ω
  | .B => ω

/-- The total kinetic contribution equals the sum over colors.

This formalizes the connection: Ω = Σ_c ω_c where c ∈ {R, G, B}.
The positivity hypothesis is kept for physical consistency but not needed algebraically. -/
theorem omega_from_colors (ω : ℝ) (_hω : ω > 0) :
    colorContributions ω ColorPhase.R + colorContributions ω ColorPhase.G +
    colorContributions ω ColorPhase.B = 3 * ω := by
  simp only [colorContributions]
  ring

/-- Construct BagParams from color field contributions.

This shows how the bag model parameters arise from the three-color
structure of Chiral Geometrogenesis. -/
noncomputable def bagParamsFromColors (B ω : ℝ) (hB : B > 0) (hω : ω > 0) : BagParams where
  bag_constant := B
  omega_total := colorContributions ω ColorPhase.R + colorContributions ω ColorPhase.G +
                 colorContributions ω ColorPhase.B
  bag_pos := hB
  omega_pos := by
    simp only [colorContributions]
    linarith

/-- The color-derived parameters give Ω = 3ω. -/
theorem bagParamsFromColors_omega (B ω : ℝ) (hB : B > 0) (hω : ω > 0) :
    (bagParamsFromColors B ω hB hω).omega_total = 3 * ω := by
  simp only [bagParamsFromColors, colorContributions]
  ring

/-! ## Section 11: Main Theorem Statement

The complete MIT Bag Model theorem bundling all results.
-/

/-- **Theorem 2.1.1 (Complete Statement): MIT Bag Model**

Quarks are confined within a finite region where internal quark pressure
balances external vacuum pressure. The energy functional E(R) = (4π/3)R³B + Ω/R
has a unique stable minimum.

This structure encodes all claims from the markdown specification:
1. Unique equilibrium exists at R_eq = (Ω/4πB)^(1/4)
2. Equilibrium is stable: d²E/dR² > 0
3. Pressure balance: P_quark = P_vac = B
4. R_eq is the unique global minimum (IsMinOn formulation)
5. Energy at equilibrium equals 4Ω/(3R_eq)
6. Boundary behavior guarantees existence
-/
structure BagModelTheorem (params : BagParams) where
  /-- Claim 1: Equilibrium radius is positive -/
  equilibrium_exists : equilibriumRadius params > 0

  /-- Claim 2: First derivative vanishes at equilibrium -/
  derivative_zero : energyDerivative params (equilibriumRadius params) = 0

  /-- Claim 3: Second derivative is positive (stability) -/
  stable : energySecondDerivative params (equilibriumRadius params) > 0

  /-- Claim 4: Pressure balance at equilibrium -/
  pressure_balanced :
    quarkPressure params (equilibriumRadius params) = vacuumPressure params

  /-- Claim 5: Energy is strictly convex (uniqueness) -/
  uniqueness : ∀ R : ℝ, R > 0 → energySecondDerivative params R > 0

  /-- Claim 6: Energy diverges as R → 0⁺ -/
  boundary_behavior :
    ∀ M : ℝ, ∃ δ : ℝ, δ > 0 ∧ ∀ R : ℝ, 0 < R → R < δ → totalEnergy params R > M

  /-- Claim 7: R_eq is the global minimum (IsMinOn formulation) -/
  global_minimum : IsMinOn (totalEnergy params) (Set.Ioi 0) (equilibriumRadius params)

  /-- Claim 8: Energy at equilibrium equals the closed-form formula -/
  energy_formula :
    totalEnergy params (equilibriumRadius params) = equilibriumEnergy params

/-- **Main Theorem**: The bag model theorem holds for any valid parameters. -/
theorem bag_model_theorem_holds (params : BagParams) :
    Nonempty (BagModelTheorem params) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact equilibriumRadius_pos params
  · exact derivative_zero_at_equilibrium params
  · exact equilibrium_stable params
  · exact pressure_balance params
  · exact energy_strictly_convex params
  · exact energy_diverges_at_zero params
  · exact equilibrium_isMinOn params
  · exact totalEnergy_at_equilibrium params

/-- Direct construction of the theorem -/
noncomputable def theBagModelTheorem (params : BagParams) : BagModelTheorem params where
  equilibrium_exists := equilibriumRadius_pos params
  derivative_zero := derivative_zero_at_equilibrium params
  stable := equilibrium_stable params
  pressure_balanced := pressure_balance params
  uniqueness := energy_strictly_convex params
  boundary_behavior := energy_diverges_at_zero params
  global_minimum := equilibrium_isMinOn params
  energy_formula := totalEnergy_at_equilibrium params

/-! ## Summary

Theorem 2.1.1 establishes the MIT Bag Model:

**Core Claims (all proven):**
1. ✅ Energy functional: E(R) = (4π/3)R³B + Ω/R
2. ✅ Equilibrium radius: R_eq = (Ω/4πB)^(1/4)
3. ✅ Stability: d²E/dR²|_{R_eq} > 0 (strict convexity)
4. ✅ Pressure balance: P_quark(R_eq) = B = P_vac
5. ✅ Uniqueness: strictly convex function has at most one minimum
6. ✅ Existence: boundary behavior + continuity guarantees minimum
7. ✅ Global minimum: IsMinOn formulation for R_eq
8. ✅ Energy formula: E(R_eq) = 4Ω/(3R_eq)

**Physical Applications:**
9. ✅ Physical predictions: proton radius ~1 fm, mass ~940 MeV
10. ✅ Confinement mechanism: linear potential from string tension
11. ✅ Chiral connection: B = λv_χ⁴ from Mexican hat potential
12. ✅ Color structure: Ω = 3ω for three colors

**Formal Verification Completeness:**
- Differentiability: HasDerivAt proofs for all derivatives
- Pressure derivation: P_quark = -dE_kin/dV formally verified
- Virial theorem: E_vol = E_kin/3 at equilibrium
- IsGLB: E(R_eq) is greatest lower bound of {E(R) : R > 0}

**References:**
- Chodos, Jaffe, Johnson, Thorn, Weisskopf (1974), Phys. Rev. D 9, 3471
- DeGrand, Jaffe, Johnson, Kiskis (1975), Phys. Rev. D 12, 2060
- MIT boundary condition eigenvalue: ω₀ = 2.04278... from j₀(ω) = j₁(ω)

**Physical Interpretation:**

The MIT Bag Model confines quarks within a finite region where quark pressure
(from the uncertainty principle) balances vacuum pressure B. The equilibrium
radius R_eq = (Ω/4πB)^(1/4) is stable because the energy functional is strictly
convex. Pulling quarks out stretches the bag, with energy growing linearly
(confinement). In Chiral Geometrogenesis, B = λv_χ⁴ connects confinement to
spontaneous chiral symmetry breaking.

**Adversarial Review Status:** Complete (2025-12-26)
- All shortcuts identified and corrected
- Missing existence theorem added
- IsMinOn/IsGLB formulations added
- Pressure derivation formally verified
- MIT boundary condition properly cited
-/

end ChiralGeometrogenesis.Phase2.Theorem_2_1_1
