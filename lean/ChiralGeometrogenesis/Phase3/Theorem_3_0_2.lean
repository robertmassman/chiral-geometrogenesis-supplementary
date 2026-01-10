/-
  Phase3/Theorem_3_0_2.lean

  Theorem 3.0.2: Non-Zero Phase Gradient
  "CRITICAL - ENABLES PHASE-GRADIENT MASS GENERATION MECHANISM"

  This theorem establishes that the phase gradient of the chiral field with
  respect to the internal parameter λ is non-zero, providing the "time derivative"
  needed for the phase-gradient mass generation mass mechanism without requiring external time.

  Key Results:
  1. The λ-derivative exists and satisfies: ∂_λχ = iχ (eigenvalue equation)
  2. The expectation value satisfies: |⟨∂_λχ⟩| = v_χ(x)
  3. At the center: |⟨∂_λχ⟩|_{x=0} = 0 (since v_χ(0) = 0)
  4. Away from center: |⟨∂_λχ⟩| > 0
  5. Physical time conversion: ∂_tχ = ω₀∂_λχ = iω₀χ

  Physical Significance:
  - The non-zero gradient provides the "oscillating VEV" needed for phase-gradient mass generation
  - No bootstrap circularity: uses only internal parameter λ, no external time
  - Enables Theorem 3.1.1 (Phase-Gradient Mass Generation Mass Formula)

  Dependencies:
  - ✅ Definition 0.1.3 (Pressure Functions from Geometric Opposition)
  - ✅ Theorem 0.2.1 (Total Field from Superposition)
  - ✅ Theorem 0.2.2 (Internal Time Parameter Emergence)
  - ✅ Theorem 3.0.1 (Pressure-Modulated Superposition)

  Reference: docs/proofs/Phase3/Theorem-3.0.2-Non-Zero-Phase-Gradient.md
-/

import ChiralGeometrogenesis.Phase3.Theorem_3_0_1
import ChiralGeometrogenesis.Phase0.Theorem_0_2_2
import ChiralGeometrogenesis.Foundations.DynamicsFoundation
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

-- Linter settings: Use project-standard suppressions only
-- docString: Allow flexible docstring formatting for mathematical documentation
-- unusedVariables: Some proof witnesses are not explicitly used
-- longLine: Mathematical expressions and formulas can exceed 100 chars
set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Phase3

open ChiralGeometrogenesis
open ChiralGeometrogenesis.Phase0
open ChiralGeometrogenesis.Phase0.Theorem_0_2_1
open ChiralGeometrogenesis.Phase0.Definition_0_1_3
open ChiralGeometrogenesis.Foundations
open ChiralGeometrogenesis.ColorFields
open ChiralGeometrogenesis.PureMath.Polyhedra
open Complex Real

/-! ## Section 1: The Chiral Field with Internal Parameter

The chiral field χ(x, λ) depends on:
- Position x ∈ ∂S (boundary of stella octangula)
- Internal parameter λ (dimensionless, in radians)

The fundamental form is:
  χ(x, λ) = v_χ(x) · e^{i(Φ_{spatial}(x) + λ)}

where:
- v_χ(x) is the VEV magnitude (from Theorem 3.0.1)
- Φ_{spatial}(x) is the position-dependent spatial phase
- λ is the rescaled internal parameter (dimensionless)
-/

/-! ### 1.1 Units and Dimensions

**CRITICAL**: In natural units (ℏ = c = 1), we use the rescaled λ parameter:

| Symbol         | Dimension | Notes                                    |
|----------------|-----------|------------------------------------------|
| λ              | [1]       | Dimensionless (radians)                  |
| ω₀             | [M]       | Energy scale, ω₀ = E_total/I_total       |
| t              | [M⁻¹]     | Physical time, t = λ/ω₀                  |
| v_χ(x)         | [M]       | VEV magnitude, ~ f_π ≈ 93 MeV            |
| ∂_λ            | [1]       | Dimensionless derivative                 |
| ∂_λχ           | [M]       | Same dimension as χ                      |

**Key dimensional relations:**
- ∂_λχ = iχ : [M]/[1] = [M] ✓
- ∂_tχ = iω₀χ : [M]/[M⁻¹] = [M²] ✓
-/

/-- The stella octangula center point (0, 0, 0).

This is imported from Theorem_0_2_1.Core. Note that within Phase3:
- `stellaCenterPoint` (this abbrev) = `Theorem_0_2_1.stellaCenter`
- `vevStellaCenter` (from Theorem 3.0.1) = `stellaCenter` = same point

All these refer to the same geometric point: the origin (0, 0, 0).
-/
noncomputable abbrev stellaCenterPoint : Point3D := Theorem_0_2_1.stellaCenter

/-- The VEV function v_χ(x) representing the position-dependent vacuum expectation value.

From Theorem 3.0.1 (Pressure-Modulated Superposition), the VEV magnitude is:
  v_χ(x) = f_π · √(1 - 3·Σ_c P_c²(x) / (Σ_c P_c(x))²)

This structure axiomatizes the key properties:
- Non-negative everywhere
- Zero at the center (x = 0)
- Positive away from center

**Bridge to Theorem 3.0.1:** Use `VEVFunction.fromPressureModulated` to construct
a VEVFunction from a `PressureModulatedVEVConfig`, deriving these properties from
the proven theorems rather than axioms. See Section 1.2.
-/
structure VEVFunction where
  /-- The VEV magnitude at each point -/
  magnitude : Point3D → ℝ
  /-- VEV is non-negative everywhere -/
  nonneg : ∀ x, 0 ≤ magnitude x
  /-- VEV vanishes at the center -/
  zero_at_center : magnitude stellaCenterPoint = 0

/-- Extended VEV function with positivity away from the nodal line (W-axis).

**Important geometric clarification:**
The VEV v_χ(x) vanishes on the entire W-axis (the line through origin in direction (1,1,1)),
not just at the center. This is because:
- The W-axis is where all three pressure functions are equal: P_R = P_G = P_B
- Equal pressures cause exact phase cancellation: Σ_c P_c · e^{iφ_c} = 0
- This is proven in `nodal_line_iff_w_axis` from Theorem 3.0.1

For `VEVFunctionPositive`, we require positivity away from the center, which is
a stronger condition. This is appropriate when working with generic field configurations
where we don't track the full W-axis structure.

For the full physical picture where VEV vanishes on the W-axis, use
`VEVFunctionNodalLine` below.
-/
structure VEVFunctionPositive extends VEVFunction where
  /-- VEV is strictly positive away from center -/
  pos_away_from_center : ∀ x, x ≠ stellaCenterPoint → 0 < toVEVFunction.magnitude x

/-- VEV function with the physically accurate nodal line structure.

This captures the actual physics: the VEV vanishes on the entire W-axis (nodal line),
not just at the center. This is the correct structure for the pressure-modulated VEV.
-/
structure VEVFunctionNodalLine extends VEVFunction where
  /-- The regularization parameter (needed to define nodal line) -/
  reg : RegularizationParam
  /-- VEV vanishes on the nodal line (W-axis) -/
  zero_on_nodal_line : ∀ x, OnNodalLine reg x → toVEVFunction.magnitude x = 0
  /-- VEV is strictly positive off the nodal line -/
  pos_off_nodal_line : ∀ x, ¬OnNodalLine reg x → 0 < toVEVFunction.magnitude x

/-! ### Smoothness Properties (Documentation)

The VEV magnitude v_χ(x) from the pressure-modulated construction is smooth
(infinitely differentiable) on ℝ³ because:
1. The pressure functions P_c(x) = 1/(ε² + |x - x_c|²) are smooth for ε > 0
2. The chiralVEV is a smooth combination of pressures and exponentials
3. Complex.normSq and Real.sqrt are smooth where normSq > 0

**Note on the nodal line:** At points where normSq = 0 (on the W-axis),
the VEV magnitude is smooth but the VEV phase may not be defined.
The magnitude function itself is smooth everywhere because √(normSq) = 0
is a smooth function when normSq approaches 0.

**Why we don't formalize smoothness here:**
- Point3D currently lacks TopologicalSpace/NormedSpace instances
- The eigenvalue equation only requires smoothness in λ, not in x
- Spatial smoothness will be relevant for Theorem 5.2.1 (Emergent Metric)
- When needed, Point3D should be equipped with the standard ℝ³ topology
-/

namespace VEVFunction

/-- The VEV magnitude squared -/
noncomputable def magnitudeSq (v : VEVFunction) (x : Point3D) : ℝ :=
  (v.magnitude x) ^ 2

/-- VEV magnitude squared is non-negative -/
theorem magnitudeSq_nonneg (v : VEVFunction) (x : Point3D) :
    0 ≤ v.magnitudeSq x := sq_nonneg _

end VEVFunction

/-! ### Smoothness of the Pressure-Modulated VEV

The VEV from Theorem 3.0.1 is smooth (differentiable) because:
1. **Pressure functions are smooth:** P_c(x) = 1/(ε² + |x - x_c|²) is C^∞ for ε > 0
2. **Exponentials are smooth:** e^{iφ_c} are constant (smooth)
3. **chiralVEV is smooth:** A linear combination of smooth functions
4. **normSq is smooth:** Complex.normSq : ℂ → ℝ is smooth
5. **sqrt is smooth where positive:** Real.sqrt is smooth on (0, ∞)

The only potential issue is at zeros of normSq (the nodal line), but:
- The magnitude v_χ = √(normSq(chiralVEV)) is still smooth at zeros
- This is because √(t) = t/√(t) extends smoothly to t = 0 when
  the zero is approached from a smooth path with vanishing derivative

For the purposes of Theorem 3.0.2, the key point is:
- The eigenvalue equation ∂_λχ = iχ only involves derivatives in λ
- The spatial smoothness of v_χ(x) is not required for this theorem
- Spatial smoothness becomes relevant in Theorem 5.2.1 (Emergent Metric)
-/

/-! ### 1.2 Bridge to Theorem 3.0.1

The VEVFunction structure axiomatizes properties that are proven in Theorem 3.0.1.
Here we provide constructors that build VEVFunction instances from the actual
pressure-modulated VEV construction.

Since both files are in the `ChiralGeometrogenesis.Phase3` namespace, the
definitions from Theorem_3_0_1 are directly accessible.
-/

/-- Construct a VEVFunction from a PressureModulatedVEVConfig.

This bridges the abstract VEVFunction interface to the concrete construction
from Theorem 3.0.1. The properties are derived from proven theorems, not axioms.
-/
noncomputable def VEVFunction.fromPressureModulated
    (cfg : PressureModulatedVEVConfig) : VEVFunction where
  magnitude := vevMagnitude cfg
  nonneg := vevMagnitude_nonneg cfg
  zero_at_center := vev_zero_at_center cfg

/-- **DEPRECATED - DO NOT USE**

This constructor requires an impossible hypothesis `h_off_axis`.

The hypothesis `∀ x, x ≠ stellaCenterPoint → ¬OnWAxis x` is FALSE because
the W-axis contains infinitely many points besides the center: any point
of the form `t·(-1,-1,1)` for `t ≠ 0` is on the W-axis but not at the center.

**Use `VEVFunctionNodalLine.fromPressureModulated` instead**, which correctly
captures the physics: VEV vanishes on the entire nodal line (W-axis), not just
at the center.

The `VEVFunctionPositive` structure itself is useful for idealized configurations
where VEV is positive everywhere except at a single point, but such configurations
do NOT arise from the physical pressure-modulated construction.
-/
noncomputable def VEVFunctionPositive.fromPressureModulated
    (cfg : PressureModulatedVEVConfig)
    (h_off_axis : ∀ x, x ≠ stellaCenterPoint → ¬OnWAxis x) :
    VEVFunctionPositive where
  toVEVFunction := VEVFunction.fromPressureModulated cfg
  pos_away_from_center := fun x hx => by
    have h_not_nodal : ¬OnNodalLine cfg.reg x := by
      rw [nodal_line_iff_w_axis]
      exact h_off_axis x hx
    exact vev_pos_off_nodal_line cfg x h_not_nodal

/-- The stellaCenterPoint equals vevStellaCenter from Theorem 3.0.1 -/
theorem stellaCenterPoint_eq_vevStellaCenter :
    stellaCenterPoint = vevStellaCenter := rfl

/-- VEV vanishes on the nodal line (W-axis).

When all three pressures are equal (P_R = P_G = P_B), the three phase contributions
cancel exactly: a·(e^{i·0} + e^{i·2π/3} + e^{i·4π/3}) = a·0 = 0.

This uses `phase_sum_zero` from Theorem 3.0.1.
-/
theorem vev_zero_on_nodal_line (cfg : PressureModulatedVEVConfig) (x : Point3D)
    (h : OnNodalLine cfg.reg x) : vevMagnitude cfg x = 0 := by
  -- Strategy: Show chiralVEV = 0 when pressures are equal (on nodal line)
  -- Then normSq = 0, so vevMagnitude = sqrt(0) = 0
  have h_chiral_zero : chiralVEV cfg x = 0 := by
    unfold chiralVEV PressureModulatedVEVConfig.amplitudeR
      PressureModulatedVEVConfig.amplitudeG PressureModulatedVEVConfig.amplitudeB
    unfold OnNodalLine at h
    obtain ⟨h_RG, h_GB⟩ := h
    -- When P_R = P_G = P_B, all amplitudes are equal: a₀ · P_R = a₀ · P_G = a₀ · P_B
    have h_G_eq_R : pressureG cfg.reg x = pressureR cfg.reg x := h_RG.symm
    have h_B_eq_R : pressureB cfg.reg x = pressureR cfg.reg x := by rw [← h_GB, ← h_RG]
    -- Factor out the common amplitude
    calc (↑(cfg.a₀ * pressureR cfg.reg x) : ℂ) * phaseR +
         (↑(cfg.a₀ * pressureG cfg.reg x) : ℂ) * phaseG +
         (↑(cfg.a₀ * pressureB cfg.reg x) : ℂ) * phaseB
        = (↑(cfg.a₀ * pressureR cfg.reg x) : ℂ) * phaseR +
          (↑(cfg.a₀ * pressureR cfg.reg x) : ℂ) * phaseG +
          (↑(cfg.a₀ * pressureR cfg.reg x) : ℂ) * phaseB := by rw [h_G_eq_R, h_B_eq_R]
      _ = (↑(cfg.a₀ * pressureR cfg.reg x) : ℂ) * (phaseR + phaseG + phaseB) := by ring
      _ = (↑(cfg.a₀ * pressureR cfg.reg x) : ℂ) * 0 := by rw [phase_sum_zero]
      _ = 0 := by ring
  -- chiralVEV = 0 implies normSq = 0 implies vevMagnitude = 0
  unfold vevMagnitude
  rw [h_chiral_zero]
  simp

/-- Construct a VEVFunctionNodalLine from a PressureModulatedVEVConfig.

This is the physically accurate construction that captures the full nodal line
structure of the VEV.
-/
noncomputable def VEVFunctionNodalLine.fromPressureModulated
    (cfg : PressureModulatedVEVConfig) : VEVFunctionNodalLine where
  toVEVFunction := VEVFunction.fromPressureModulated cfg
  reg := cfg.reg
  zero_on_nodal_line := fun x h => vev_zero_on_nodal_line cfg x h
  pos_off_nodal_line := fun x h => vev_pos_off_nodal_line cfg x h

/-! ## Section 2: The Eigenvalue Equation ∂_λχ = iχ

The fundamental equation of Theorem 3.0.2 is the eigenvalue equation:
  ∂_λχ = iχ

This states that differentiation with respect to the internal parameter λ
is equivalent to multiplication by i.

**Physical interpretation:**
- χ(x, λ) = v_χ(x) · e^{i(Φ_spatial + λ)}
- ∂_λχ = v_χ(x) · i · e^{i(Φ_spatial + λ)} = i · χ

The eigenvalue is exactly i (not iω) because we use the rescaled λ parameter
where λ itself is the phase (in radians).
-/

/-- The chiral field as a function of position and internal parameter.

χ(x, λ) = v_χ(x) · e^{i(Φ_spatial(x) + λ)}

where:
- v_χ(x) is the VEV magnitude (from VEVFunction)
- Φ_spatial(x) is the spatial phase (constant in x for fixed position)
- λ is the internal parameter (radians)
-/
structure ChiralFieldLambda where
  /-- The VEV function -/
  vev : VEVFunction
  /-- The spatial phase function -/
  spatialPhase : Point3D → ℝ

namespace ChiralFieldLambda

/-- The complex value of the chiral field at (x, lam) -/
noncomputable def value (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) : ℂ :=
  χ.vev.magnitude x * Complex.exp (Complex.I * (χ.spatialPhase x + lam))

/-- The total phase at (x, lam) -/
noncomputable def totalPhase (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) : ℝ :=
  χ.spatialPhase x + lam

/-- The norm squared of the chiral field equals the VEV squared -/
theorem normSq_value_eq_vev_sq (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) :
    Complex.normSq (χ.value x lam) = (χ.vev.magnitude x) ^ 2 := by
  unfold value
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  -- |exp(I * θ)|² = 1 for real θ
  -- Use the existing lemma from DynamicsFoundation
  have h : Complex.normSq (Complex.exp (Complex.I * (↑(χ.spatialPhase x) + ↑lam))) = 1 := by
    -- Rewrite (↑φ + ↑λ) as ↑(φ + λ) using the explicit ofReal_add lemma
    rw [← Complex.ofReal_add]
    exact ChiralFieldValue.normSq_exp_I_mul_real (χ.spatialPhase x + lam)
  rw [h, mul_one]
  ring

/-- The magnitude of the chiral field equals the VEV (using √normSq) -/
theorem abs_value_eq_vev (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) :
    Real.sqrt (Complex.normSq (χ.value x lam)) = χ.vev.magnitude x := by
  rw [normSq_value_eq_vev_sq]
  rw [Real.sqrt_sq (χ.vev.nonneg x)]

/-- **Main Theorem 3.0.2a**: The eigenvalue equation ∂_λχ = iχ.

The derivative of χ with respect to λ equals i times χ.

**Proof sketch (from markdown §3.1-3.3):**
Given χ(x, λ) = v_χ(x) · e^{i(Φ_spatial + λ)}, we compute:
  ∂_λχ = v_χ(x) · ∂_λ[e^{i(Φ_spatial + λ)}]
       = v_χ(x) · i · e^{i(Φ_spatial + λ)}
       = i · χ

This uses the chain rule: d/dλ[e^{iλ}] = i · e^{iλ}.
-/
theorem eigenvalue_equation (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) :
    HasDerivAt (fun lam' => χ.value x lam') (Complex.I * χ.value x lam) lam := by
  unfold value
  -- χ(lam) = v · exp(I · (φ + lam))
  -- We need: HasDerivAt (lam' ↦ v * exp(I * (φ + lam'))) (I * v * exp(I * (φ + lam))) lam
  -- Set abbreviations
  set v : ℝ := χ.vev.magnitude x with hv_def
  set φ : ℝ := χ.spatialPhase x with hφ_def
  -- The goal: HasDerivAt (lam' ↦ ↑v * exp(I * (↑φ + ↑lam'))) (I * (↑v * exp(I * (↑φ + ↑lam)))) lam
  -- Step 1: d/dlam' (φ + lam') = 1
  have h_linear : HasDerivAt (fun lam' : ℝ => (φ + lam' : ℂ)) 1 lam := by
    have h1 : HasDerivAt (fun _ : ℝ => (φ : ℂ)) 0 lam := hasDerivAt_const lam (φ : ℂ)
    have h2 : HasDerivAt (fun lam' : ℝ => (lam' : ℂ)) 1 lam := Complex.ofRealCLM.hasDerivAt
    convert h1.add h2 using 1
    simp
  -- Step 2: d/dlam' (I * (φ + lam')) = I · 1 = I
  have h_imag_linear : HasDerivAt (fun lam' : ℝ => Complex.I * (φ + lam' : ℂ)) Complex.I lam := by
    have := h_linear.const_mul Complex.I
    convert this using 1
    ring
  -- Step 3: d/dlam' exp(I * (φ + lam')) = exp(I * (φ + lam)) · I by chain rule
  have h_exp : HasDerivAt (fun lam' : ℝ => Complex.exp (Complex.I * (φ + lam' : ℂ)))
                          (Complex.exp (Complex.I * (φ + lam : ℂ)) * Complex.I) lam := by
    have h_exp_base : HasDerivAt Complex.exp (Complex.exp (Complex.I * (φ + lam : ℂ)))
                                  (Complex.I * (φ + lam : ℂ)) := Complex.hasDerivAt_exp _
    exact HasDerivAt.comp lam h_exp_base h_imag_linear
  -- Step 4: d/dlam' (v * exp(...)) = v * exp(I * (φ + lam)) * I
  have h_scaled : HasDerivAt (fun lam' : ℝ => (v : ℂ) * Complex.exp (Complex.I * (φ + lam' : ℂ)))
                             ((v : ℂ) * (Complex.exp (Complex.I * (φ + lam : ℂ)) * Complex.I)) lam := by
    exact h_exp.const_mul (v : ℂ)
  -- Rearrange: v * (exp(...) * I) = I * (v * exp(...))
  convert h_scaled using 1
  ring

/-- Corollary: The derivative exists and equals iχ -/
theorem deriv_eq_i_times_self (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) :
    deriv (fun lam' => χ.value x lam') lam = Complex.I * χ.value x lam :=
  (eigenvalue_equation χ x lam).deriv

/-- **Theorem 3.0.2b**: The norm squared of the λ-derivative equals the VEV squared.

|∂_λχ|² = |iχ|² = |χ|² = v_χ(x)²

This shows the derivative is non-zero wherever the VEV is non-zero.
-/
theorem deriv_normSq_eq_vev_sq (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) :
    Complex.normSq (deriv (fun lam' => χ.value x lam') lam) = (χ.vev.magnitude x)^2 := by
  rw [deriv_eq_i_times_self]
  rw [Complex.normSq_mul, Complex.normSq_I, one_mul]
  exact normSq_value_eq_vev_sq χ x lam

/-- The magnitude of the derivative equals the VEV -/
theorem deriv_magnitude_eq_vev (χ : ChiralFieldLambda) (x : Point3D) (lam : ℝ) :
    Real.sqrt (Complex.normSq (deriv (fun lam' => χ.value x lam') lam)) = χ.vev.magnitude x := by
  rw [deriv_normSq_eq_vev_sq]
  exact Real.sqrt_sq (χ.vev.nonneg x)

/-- **Theorem 3.0.2c**: The derivative vanishes at the center.

At x = 0 (stella center), |∂_λχ|² = v_χ(0)² = 0.
-/
theorem deriv_zero_at_center (χ : ChiralFieldLambda) (lam : ℝ) :
    Complex.normSq (deriv (fun lam' => χ.value stellaCenterPoint lam') lam) = 0 := by
  rw [deriv_normSq_eq_vev_sq]
  rw [χ.vev.zero_at_center]
  ring

/-- Field value is zero at the center -/
theorem value_zero_at_center (χ : ChiralFieldLambda) (lam : ℝ) :
    χ.value stellaCenterPoint lam = 0 := by
  unfold value
  rw [χ.vev.zero_at_center]
  simp

end ChiralFieldLambda

/-! ## Section 3: Physical Time Conversion

When converting from the internal parameter λ to physical time t = λ/ω₀,
the eigenvalue equation becomes:
  ∂_tχ = ω₀ · ∂_λχ = ω₀ · iχ = iω₀χ

This is the standard form used in QFT.
-/

/-- Configuration for physical time emergence -/
structure PhysicalTimeConfig where
  /-- The chiral field -/
  chiralField : ChiralFieldLambda
  /-- The fundamental frequency ω₀ (energy scale) -/
  omega0 : ℝ
  /-- Frequency is positive -/
  omega0_pos : 0 < omega0

namespace PhysicalTimeConfig

/-- Convert internal parameter λ to physical time t -/
noncomputable def toPhysicalTime (cfg : PhysicalTimeConfig) (lam : ℝ) : ℝ :=
  lam / cfg.omega0

/-- Convert physical time t to internal parameter λ -/
noncomputable def fromPhysicalTime (cfg : PhysicalTimeConfig) (t : ℝ) : ℝ :=
  t * cfg.omega0

/-- Round-trip conversion -/
theorem time_conversion_roundtrip (cfg : PhysicalTimeConfig) (lam : ℝ) :
    cfg.fromPhysicalTime (cfg.toPhysicalTime lam) = lam := by
  unfold toPhysicalTime fromPhysicalTime
  have : cfg.omega0 ≠ 0 := ne_of_gt cfg.omega0_pos
  field_simp

/-- The field as a function of physical time -/
noncomputable def fieldAtTime (cfg : PhysicalTimeConfig) (x : Point3D) (t : ℝ) : ℂ :=
  cfg.chiralField.value x (cfg.fromPhysicalTime t)

/-- **Theorem 3.0.2d**: Physical time derivative equation.

∂_tχ = iω₀χ

The derivative with respect to physical time t = λ/ω₀ is iω₀ times the field.
-/
theorem physical_time_derivative (cfg : PhysicalTimeConfig) (x : Point3D) (t : ℝ) :
    HasDerivAt (cfg.fieldAtTime x) (Complex.I * cfg.omega0 * cfg.fieldAtTime x t) t := by
  -- χ(t) = value(x, ω₀ * t) = v · exp(I * (φ + ω₀ * t))
  -- dχ/dt = v · I · ω₀ · exp(I * (φ + ω₀ * t)) = I · ω₀ · χ(t)
  unfold fieldAtTime fromPhysicalTime ChiralFieldLambda.value
  -- Set abbreviations for clarity
  set v : ℝ := cfg.chiralField.vev.magnitude x with hv_def
  set φ : ℝ := cfg.chiralField.spatialPhase x with hφ_def
  set ω : ℝ := cfg.omega0 with hω_def
  -- Goal: HasDerivAt (t' ↦ v * exp(I * (φ + t' * ω))) (I * ω * (v * exp(I * (φ + t * ω)))) t
  -- First, normalize the coercions: ↑(t' * ω) = ↑t' * ↑ω
  have h_cast : ∀ t' : ℝ, (↑(t' * ω) : ℂ) = ↑t' * ↑ω := fun t' => by push_cast; rfl
  simp_rw [h_cast]
  -- Step 1: d/dt' (φ + t' * ω) = ω
  have h_inner : HasDerivAt (fun t' : ℝ => (φ : ℂ) + (t' : ℂ) * (ω : ℂ)) (ω : ℂ) t := by
    have h_const : HasDerivAt (fun _ : ℝ => (φ : ℂ)) 0 t := hasDerivAt_const t (φ : ℂ)
    have h_lin : HasDerivAt (fun t' : ℝ => (t' : ℂ) * (ω : ℂ)) (ω : ℂ) t := by
      have h1 : HasDerivAt (fun t' : ℝ => (t' : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h2 := h1.mul_const (ω : ℂ)
      convert h2 using 1
      ring
    convert h_const.add h_lin using 1
    ring
  -- Step 2: d/dt' (I * (φ + t' * ω)) = I * ω
  have h_phase : HasDerivAt (fun t' : ℝ => Complex.I * ((φ : ℂ) + (t' : ℂ) * (ω : ℂ)))
                            (Complex.I * (ω : ℂ)) t := by
    exact h_inner.const_mul Complex.I
  -- Step 3: d/dt' exp(I * (φ + t' * ω)) = exp(I * (φ + t * ω)) * (I * ω)
  have h_exp : HasDerivAt (fun t' : ℝ => Complex.exp (Complex.I * ((φ : ℂ) + (t' : ℂ) * (ω : ℂ))))
                          (Complex.exp (Complex.I * ((φ : ℂ) + (t : ℂ) * (ω : ℂ))) * (Complex.I * (ω : ℂ))) t := by
    have h_exp_base : HasDerivAt Complex.exp (Complex.exp (Complex.I * ((φ : ℂ) + (t : ℂ) * (ω : ℂ))))
                                  (Complex.I * ((φ : ℂ) + (t : ℂ) * (ω : ℂ))) := Complex.hasDerivAt_exp _
    exact HasDerivAt.comp t h_exp_base h_phase
  -- Step 4: d/dt' (v * exp(...)) = v * exp(I * (φ + t * ω)) * (I * ω)
  have h_scaled : HasDerivAt (fun t' : ℝ => (v : ℂ) * Complex.exp (Complex.I * ((φ : ℂ) + (t' : ℂ) * (ω : ℂ))))
                             ((v : ℂ) * (Complex.exp (Complex.I * ((φ : ℂ) + (t : ℂ) * (ω : ℂ))) * (Complex.I * (ω : ℂ)))) t := by
    exact h_exp.const_mul (v : ℂ)
  -- Rearrange: v * (exp(...) * (I * ω)) = I * ω * (v * exp(...))
  convert h_scaled using 1
  ring

/-- Corollary: deriv form of physical time derivative -/
theorem physical_time_deriv (cfg : PhysicalTimeConfig) (x : Point3D) (t : ℝ) :
    deriv (cfg.fieldAtTime x) t = Complex.I * cfg.omega0 * cfg.fieldAtTime x t :=
  (physical_time_derivative cfg x t).deriv

end PhysicalTimeConfig

/-! ## Section 4: Non-Zero Phase Gradient Away from Center

The key physical result: the phase gradient is non-zero away from the center,
enabling the phase-gradient mass generation mass mechanism.
-/

/-- **Theorem 3.0.2e**: Non-zero derivative away from center.

For x ≠ stellaCenter, |∂_λχ|² = v_χ(x)² > 0.

This is the critical result that enables phase-gradient mass generation.
-/
theorem deriv_nonzero_away_from_center
    (χ : ChiralFieldLambda) (v_pos : VEVFunctionPositive)
    (hv : χ.vev = v_pos.toVEVFunction)
    (x : Point3D) (hx : x ≠ stellaCenterPoint) (lam : ℝ) :
    0 < Complex.normSq (deriv (fun lam' => χ.value x lam') lam) := by
  rw [χ.deriv_normSq_eq_vev_sq]
  rw [hv]
  have h := v_pos.pos_away_from_center x hx
  exact sq_pos_of_pos h

/-- The derivative is non-zero iff position is away from center -/
theorem deriv_nonzero_iff_away_from_center
    (χ : ChiralFieldLambda) (v_pos : VEVFunctionPositive)
    (hv : χ.vev = v_pos.toVEVFunction) (x : Point3D) (lam : ℝ) :
    0 < Complex.normSq (deriv (fun lam' => χ.value x lam') lam) ↔ x ≠ stellaCenterPoint := by
  constructor
  · intro h
    by_contra heq
    rw [heq] at h
    rw [χ.deriv_zero_at_center] at h
    exact lt_irrefl 0 h
  · intro hx
    exact deriv_nonzero_away_from_center χ v_pos hv x hx lam

/-! ### Section 4.1: Physically Correct Nodal Line Theorems

The above theorems using `VEVFunctionPositive` are for idealized configurations.
The physically correct statements use `VEVFunctionNodalLine`, which captures that
the VEV vanishes on the entire W-axis (nodal line), not just at the center.

These are the theorems that should be used for physical applications.
-/

/-- **Theorem 3.0.2e' (PHYSICALLY CORRECT)**: Non-zero derivative off the nodal line.

For points x NOT on the nodal line (W-axis), |∂_λχ|² = v_χ(x)² > 0.

This is the physically correct version of `deriv_nonzero_away_from_center`.
The VEV vanishes on the entire W-axis, so positivity only holds OFF the axis.
-/
theorem deriv_nonzero_off_nodal_line
    (χ : ChiralFieldLambda) (v_nodal : VEVFunctionNodalLine)
    (hv : χ.vev = v_nodal.toVEVFunction)
    (x : Point3D) (hx : ¬OnNodalLine v_nodal.reg x) (lam : ℝ) :
    0 < Complex.normSq (deriv (fun lam' => χ.value x lam') lam) := by
  rw [χ.deriv_normSq_eq_vev_sq]
  rw [hv]
  have h := v_nodal.pos_off_nodal_line x hx
  exact sq_pos_of_pos h

/-- The derivative vanishes on the nodal line -/
theorem deriv_zero_on_nodal_line
    (χ : ChiralFieldLambda) (v_nodal : VEVFunctionNodalLine)
    (hv : χ.vev = v_nodal.toVEVFunction)
    (x : Point3D) (hx : OnNodalLine v_nodal.reg x) (lam : ℝ) :
    Complex.normSq (deriv (fun lam' => χ.value x lam') lam) = 0 := by
  rw [χ.deriv_normSq_eq_vev_sq]
  rw [hv]
  have h := v_nodal.zero_on_nodal_line x hx
  simp [h]

/-- **The derivative is non-zero iff position is off the nodal line** (PHYSICALLY CORRECT)

This is the complete characterization: the λ-derivative of the chiral field
is non-zero precisely when the point is off the W-axis (nodal line).
-/
theorem deriv_nonzero_iff_off_nodal_line
    (χ : ChiralFieldLambda) (v_nodal : VEVFunctionNodalLine)
    (hv : χ.vev = v_nodal.toVEVFunction) (x : Point3D) (lam : ℝ) :
    0 < Complex.normSq (deriv (fun lam' => χ.value x lam') lam) ↔ ¬OnNodalLine v_nodal.reg x := by
  constructor
  · intro h
    by_contra heq
    have h_zero := deriv_zero_on_nodal_line χ v_nodal hv x heq lam
    rw [h_zero] at h
    exact lt_irrefl 0 h
  · intro hx
    exact deriv_nonzero_off_nodal_line χ v_nodal hv x hx lam

/-! ## Section 5: Connection to Phase-Gradient Mass Generation (Forward Reference)

This section documents how Theorem 3.0.2 connects to Theorem 3.1.1 (Phase-Gradient Mass Generation Mass).

The phase-gradient mass generation Lagrangian is:
  L_drag = -(g_χ/Λ) · ψ̄_L γ^μ (∂_μ χ) ψ_R + h.c.

For mass generation, we need ∂_μ χ ≠ 0. Theorem 3.0.2 provides this via:
  ∂_λ χ = iχ ≠ 0 (away from center)

When converting to physical time:
  ∂_t χ = iω₀χ

This gives the fermion mass (from Theorem 3.1.1):
  m_f = (g_χ · ω₀ / Λ) · v_χ
-/

/-- Structure representing the connection to phase-gradient mass generation mass mechanism -/
structure ChiralDragConnection where
  /-- Physical time configuration -/
  physicalTime : PhysicalTimeConfig
  /-- Yukawa coupling g_χ -/
  coupling : ℝ
  /-- Cutoff scale Λ -/
  cutoff : ℝ
  /-- Coupling is positive -/
  coupling_pos : 0 < coupling
  /-- Cutoff is positive -/
  cutoff_pos : 0 < cutoff

namespace ChiralDragConnection

/-- The mass scale from phase-gradient mass generation (without geometric factor η_f) -/
noncomputable def massScale (cfg : ChiralDragConnection) : ℝ :=
  cfg.coupling * cfg.physicalTime.omega0 / cfg.cutoff

/-- The position-dependent mass contribution -/
noncomputable def positionDependentMass (cfg : ChiralDragConnection) (x : Point3D) : ℝ :=
  cfg.massScale * cfg.physicalTime.chiralField.vev.magnitude x

/-- Mass scale is positive -/
theorem massScale_pos (cfg : ChiralDragConnection) : 0 < cfg.massScale := by
  unfold massScale
  exact div_pos (mul_pos cfg.coupling_pos cfg.physicalTime.omega0_pos) cfg.cutoff_pos

/-- Mass is zero at center (where v_χ = 0) -/
theorem mass_zero_at_center (cfg : ChiralDragConnection) :
    cfg.positionDependentMass stellaCenterPoint = 0 := by
  unfold positionDependentMass
  rw [cfg.physicalTime.chiralField.vev.zero_at_center]
  ring

/-- Mass is positive away from center -/
theorem mass_pos_away_from_center (cfg : ChiralDragConnection)
    (v_pos : VEVFunctionPositive)
    (hv : cfg.physicalTime.chiralField.vev = v_pos.toVEVFunction)
    (x : Point3D) (hx : x ≠ stellaCenterPoint) :
    0 < cfg.positionDependentMass x := by
  unfold positionDependentMass
  apply mul_pos cfg.massScale_pos
  rw [hv]
  exact v_pos.pos_away_from_center x hx

/-- **Mass is positive off the nodal line** (PHYSICALLY CORRECT)

This is the physically accurate version: mass is positive precisely when
the point is off the W-axis (nodal line), not just away from the center.
-/
theorem mass_pos_off_nodal_line (cfg : ChiralDragConnection)
    (v_nodal : VEVFunctionNodalLine)
    (hv : cfg.physicalTime.chiralField.vev = v_nodal.toVEVFunction)
    (x : Point3D) (hx : ¬OnNodalLine v_nodal.reg x) :
    0 < cfg.positionDependentMass x := by
  unfold positionDependentMass
  apply mul_pos cfg.massScale_pos
  rw [hv]
  exact v_nodal.pos_off_nodal_line x hx

/-- Mass vanishes on the nodal line -/
theorem mass_zero_on_nodal_line (cfg : ChiralDragConnection)
    (v_nodal : VEVFunctionNodalLine)
    (hv : cfg.physicalTime.chiralField.vev = v_nodal.toVEVFunction)
    (x : Point3D) (hx : OnNodalLine v_nodal.reg x) :
    cfg.positionDependentMass x = 0 := by
  unfold positionDependentMass
  rw [hv]
  rw [v_nodal.zero_on_nodal_line x hx]
  ring

end ChiralDragConnection

/-! ## Section 6: Summary - Theorem 3.0.2 Complete

**Theorem 3.0.2 (Non-Zero Phase Gradient)** establishes:

1. ✅ **Eigenvalue equation:** ∂_λχ = iχ
   - Proven in `ChiralFieldLambda.eigenvalue_equation`
   - Uses chain rule for complex exponential differentiation

2. ✅ **Non-zero magnitude:** |∂_λχ|² = v_χ(x)²
   - Proven in `ChiralFieldLambda.deriv_normSq_eq_vev_sq`

3. ✅ **Zero on nodal line:** |∂_λχ|² = 0 on the W-axis
   - Proven in `ChiralFieldLambda.deriv_zero_at_center` (at center)
   - Proven in `deriv_zero_on_nodal_line` (on entire W-axis)

4. ✅ **Positive off nodal line:** |∂_λχ|² > 0 for x off W-axis
   - Proven in `deriv_nonzero_off_nodal_line` (PHYSICALLY CORRECT)
   - Also `deriv_nonzero_away_from_center` (idealized case)

5. ✅ **Physical time conversion:** ∂_tχ = iω₀χ
   - Proven in `PhysicalTimeConfig.physical_time_derivative`
   - Uses chain rule composition with time scaling

**Key formulas (from markdown §11):**
- λ-frame: ∂_λχ = iχ
- Physical time: ∂_tχ = iω₀χ
- Mass formula: m_f = (g_χ · ω₀ / Λ) · v_χ (→ Theorem 3.1.1)

This theorem completes the bootstrap resolution for phase-gradient mass generation:
- Theorem 3.0.1 gives the VEV v_χ(x)
- Theorem 3.0.2 gives the phase gradient ∂_λχ
- Together they enable Theorem 3.1.1 (Phase-Gradient Mass Generation Mass Formula)

**IMPORTANT (Peer Review Note):**
The physically correct theorems use `VEVFunctionNodalLine` and `deriv_nonzero_off_nodal_line`.
The VEV vanishes on the entire W-axis (nodal line), not just at the center.
The `VEVFunctionPositive` structure is for idealized configurations only.
-/

/-- Summary structure bundling all main claims of Theorem 3.0.2.

This includes all 5 claims from the markdown specification:
1. Eigenvalue equation: ∂_λχ = iχ
2. Magnitude equality: |∂_λχ| = v_χ(x)
3. Zero at center: |∂_λχ|_{x=0} = 0
4. Positive away from center: |∂_λχ| > 0 for x ≠ center (off nodal line)
5. Physical time conversion: ∂_tχ = iω₀χ
-/
structure Theorem_3_0_2_Complete where
  /-- The chiral field configuration -/
  chiralField : ChiralFieldLambda
  /-- Physical time configuration -/
  physicalTime : PhysicalTimeConfig
  /-- The physical time uses this chiral field -/
  physicalTime_field : physicalTime.chiralField = chiralField
  /-- Claim 1: Eigenvalue equation holds -/
  eigenvalue_eq : ∀ x lam, HasDerivAt (fun lam' => chiralField.value x lam')
                                     (Complex.I * chiralField.value x lam) lam
  /-- Claim 2: Norm squared of derivative equals VEV squared -/
  normSq_eq_vev_sq : ∀ x lam, Complex.normSq (deriv (fun lam' => chiralField.value x lam') lam) =
                              (chiralField.vev.magnitude x)^2
  /-- Claim 3: Zero at center -/
  zero_at_center : ∀ lam, Complex.normSq (deriv (fun lam' => chiralField.value stellaCenterPoint lam') lam) = 0
  /-- Claim 5: Physical time derivative -/
  physical_time_eq : ∀ x t, HasDerivAt (physicalTime.fieldAtTime x)
                                       (Complex.I * physicalTime.omega0 * physicalTime.fieldAtTime x t) t

/-- Extended summary structure that also includes Claim 4 (positivity away from center).

This requires a VEVFunctionPositive to guarantee positivity away from the center.
-/
structure Theorem_3_0_2_CompleteWithPositivity extends Theorem_3_0_2_Complete where
  /-- The VEV function with positivity guarantee -/
  vev_positive : VEVFunctionPositive
  /-- The chiral field uses this VEV -/
  chiralField_vev : chiralField.vev = vev_positive.toVEVFunction
  /-- Claim 4: Positive away from center -/
  pos_away_from_center : ∀ x lam, x ≠ stellaCenterPoint →
    0 < Complex.normSq (deriv (fun lam' => chiralField.value x lam') lam)

/-- Construct the complete theorem from a chiral field and frequency -/
noncomputable def theorem_3_0_2_complete
    (χ : ChiralFieldLambda) (ω₀ : ℝ) (hω : 0 < ω₀) : Theorem_3_0_2_Complete where
  chiralField := χ
  physicalTime := ⟨χ, ω₀, hω⟩
  physicalTime_field := rfl
  eigenvalue_eq := χ.eigenvalue_equation
  normSq_eq_vev_sq := χ.deriv_normSq_eq_vev_sq
  zero_at_center := χ.deriv_zero_at_center
  physical_time_eq := fun x t => PhysicalTimeConfig.physical_time_derivative ⟨χ, ω₀, hω⟩ x t

/-- Construct the complete theorem with positivity from a chiral field, VEV, and frequency -/
noncomputable def theorem_3_0_2_complete_with_positivity
    (χ : ChiralFieldLambda) (v_pos : VEVFunctionPositive) (hv : χ.vev = v_pos.toVEVFunction)
    (ω₀ : ℝ) (hω : 0 < ω₀) : Theorem_3_0_2_CompleteWithPositivity where
  toTheorem_3_0_2_Complete := theorem_3_0_2_complete χ ω₀ hω
  vev_positive := v_pos
  chiralField_vev := hv
  pos_away_from_center := fun x lam hx => deriv_nonzero_away_from_center χ v_pos hv x hx lam

/-- **PHYSICALLY CORRECT** summary structure using nodal line (W-axis) characterization.

This is the preferred structure for physical applications. It correctly captures that:
- The VEV vanishes on the entire W-axis (nodal line), not just at the center
- The derivative is non-zero precisely off the nodal line
- This structure can be instantiated from the actual pressure-modulated VEV

Use this instead of `Theorem_3_0_2_CompleteWithPositivity` for physical applications.
-/
structure Theorem_3_0_2_CompleteWithNodalLine extends Theorem_3_0_2_Complete where
  /-- The VEV function with nodal line structure -/
  vev_nodal : VEVFunctionNodalLine
  /-- The chiral field uses this VEV -/
  chiralField_vev : chiralField.vev = vev_nodal.toVEVFunction
  /-- Claim 4a: Zero on nodal line -/
  zero_on_nodal_line : ∀ x lam, OnNodalLine vev_nodal.reg x →
    Complex.normSq (deriv (fun lam' => chiralField.value x lam') lam) = 0
  /-- Claim 4b: Positive off nodal line -/
  pos_off_nodal_line : ∀ x lam, ¬OnNodalLine vev_nodal.reg x →
    0 < Complex.normSq (deriv (fun lam' => chiralField.value x lam') lam)

/-- Construct the complete theorem with nodal line structure from a chiral field, VEV, and frequency.

This is the **preferred** constructor for physical applications.
-/
noncomputable def theorem_3_0_2_complete_with_nodal_line
    (χ : ChiralFieldLambda) (v_nodal : VEVFunctionNodalLine) (hv : χ.vev = v_nodal.toVEVFunction)
    (ω₀ : ℝ) (hω : 0 < ω₀) : Theorem_3_0_2_CompleteWithNodalLine where
  toTheorem_3_0_2_Complete := theorem_3_0_2_complete χ ω₀ hω
  vev_nodal := v_nodal
  chiralField_vev := hv
  zero_on_nodal_line := fun x lam hx => deriv_zero_on_nodal_line χ v_nodal hv x hx lam
  pos_off_nodal_line := fun x lam hx => deriv_nonzero_off_nodal_line χ v_nodal hv x hx lam

/-- Construct from a PressureModulatedVEVConfig - the most direct physical construction.

This shows how to go from the physical configuration (Theorem 3.0.1) to the complete
theorem (Theorem 3.0.2) with all claims bundled.
-/
noncomputable def theorem_3_0_2_from_pressure_modulated
    (cfg : PressureModulatedVEVConfig) (spatialPhase : Point3D → ℝ) (ω₀ : ℝ) (hω : 0 < ω₀) :
    Theorem_3_0_2_CompleteWithNodalLine :=
  let v_nodal := VEVFunctionNodalLine.fromPressureModulated cfg
  let χ : ChiralFieldLambda := ⟨v_nodal.toVEVFunction, spatialPhase⟩
  theorem_3_0_2_complete_with_nodal_line χ v_nodal rfl ω₀ hω

/-! ## Section 7: Additional Properties (Forward References)

These properties are mentioned in the markdown but are either:
- Asymptotic results that require more analysis infrastructure
- Properties that will be proven in downstream theorems
- Topological considerations that require homology machinery

### 7.1 Rate of Vanishing Near Center

From markdown §3.5.6: v_χ(x) = O(|x|) near the center.

This linear vanishing rate is proven in the markdown via Taylor expansion of the
pressure functions. The key insight is:
- P_c(x) = P₀[1 - 2P₀(x · x_c)] + O(|x|²) near x = 0
- The sum Σ_c P_c(x) e^{iφ_c} has leading term O(|x|) due to the asymmetric dot products

Formalizing this requires:
1. Differentiability of pressure functions (from Definition 0.1.3)
2. Taylor expansion machinery (from Mathlib)
3. Careful bookkeeping of the geometric constants

This is marked as a forward reference for Theorem 3.1.1 if needed.

### 7.2 Spatial Gradient ∇_x χ

From markdown §4: The spatial gradient has both amplitude and phase contributions:
  ∇_x χ = e^{iΦ}[∇v_χ + iv_χ∇Φ_{spatial}]

This is relevant for:
- Theorem 5.2.1 (Emergent Metric) which uses spatial gradients
- Understanding the full 4-gradient ∂_μ χ = (∇_x χ, ∂_λ χ)

The spatial gradient is well-defined wherever v_χ and Φ_{spatial} are differentiable,
which is everywhere except possibly on the nodal line.

### 7.3 Topological Winding Number

From markdown §18 (Appendix C): The phase Φ has winding number n = 1 around the
internal parameter circle S¹_λ. This topological protection ensures the phase
gradient cannot vanish everywhere.

Formalizing this requires homology/homotopy machinery beyond our current scope.
The physical content is captured by our eigenvalue equation ∂_λχ = iχ.
-/

end ChiralGeometrogenesis.Phase3
