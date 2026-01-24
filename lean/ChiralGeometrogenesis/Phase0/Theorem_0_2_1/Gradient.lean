/-
  Phase0/Theorem_0_2_1/Gradient.lean

  Gradient Structure for Theorem 0.2.1 (§5)

  The gradient of the total field is crucial for the phase-gradient mass generation mechanism.
  Even though χ_total(0) = 0 at the center, the gradient ∇χ_total|₀ ≠ 0.

  Contains:
  - ComplexVector3D type
  - Vertex positions (vertexR, vertexG, vertexB)
  - Pressure gradient definition
  - Total field gradient
  - gradientWeightedVertexSum and its non-zero proof
  - totalFieldGradient_at_center_nonzero (KEY result for phase-gradient mass generation)

  Reference: docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md §5
-/

import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.Core
import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.PhaseSum

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase0.Theorem_0_2_1

open ChiralGeometrogenesis
open ChiralGeometrogenesis.ColorFields
open ChiralGeometrogenesis.PureMath.Polyhedra
open Complex Real

/-! ## Section 5: Gradient of the Total Field (§5 of Theorem 0.2.1)

The gradient of the total field is crucial for the phase-gradient mass generation mechanism.
Even though χ_total(0) = 0 at the center, the gradient ∇χ_total|₀ ≠ 0.

From §5.1 of the markdown:
  ∇χ_total = Σ_c e^{iφ_c} ∇a_c(x)

where ∇a_c = a₀ · ∇P_c = a₀ · (-2(x - x_c)) / (|x - x_c|² + ε²)²

At the center x = 0:
  ∇χ_total|₀ = 2a₀P₀² Σ_c x_c e^{iφ_c}

This is non-zero because the vertex positions x_c don't share
the same cancellation property as the scalar phases.
-/

/-- A 3D complex vector (for gradient values) -/
structure ComplexVector3D where
  x : ℂ
  y : ℂ
  z : ℂ

/-- Extensionality for ComplexVector3D: two vectors are equal iff all components are equal -/
theorem ComplexVector3D.ext {v w : ComplexVector3D}
    (hx : v.x = w.x) (hy : v.y = w.y) (hz : v.z = w.z) : v = w := by
  cases v; cases w; simp_all

/-- Zero complex vector -/
def ComplexVector3D.zero : ComplexVector3D := ⟨0, 0, 0⟩

/-- Addition of complex vectors -/
def ComplexVector3D.add (v w : ComplexVector3D) : ComplexVector3D :=
  ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩

instance : Add ComplexVector3D := ⟨ComplexVector3D.add⟩

/-- Scalar multiplication of complex vector -/
def ComplexVector3D.smul (c : ℂ) (v : ComplexVector3D) : ComplexVector3D :=
  ⟨c * v.x, c * v.y, c * v.z⟩

instance : SMul ℂ ComplexVector3D := ⟨ComplexVector3D.smul⟩

/-- Convert Point3D to ComplexVector3D (real embedding) -/
def toComplexVec (p : Point3D) : ComplexVector3D :=
  ⟨↑p.x, ↑p.y, ↑p.z⟩

-- Simp lemmas for ComplexVector3D component access
@[simp] lemma ComplexVector3D.add_x (v w : ComplexVector3D) : (v + w).x = v.x + w.x := rfl
@[simp] lemma ComplexVector3D.add_y (v w : ComplexVector3D) : (v + w).y = v.y + w.y := rfl
@[simp] lemma ComplexVector3D.add_z (v w : ComplexVector3D) : (v + w).z = v.z + w.z := rfl
@[simp] lemma ComplexVector3D.smul_x (c : ℂ) (v : ComplexVector3D) : (c • v).x = c * v.x := rfl
@[simp] lemma ComplexVector3D.smul_y (c : ℂ) (v : ComplexVector3D) : (c • v).y = c * v.y := rfl
@[simp] lemma ComplexVector3D.smul_z (c : ℂ) (v : ComplexVector3D) : (c • v).z = c * v.z := rfl
@[simp] lemma toComplexVec_x (p : Point3D) : (toComplexVec p).x = ↑p.x := rfl
@[simp] lemma toComplexVec_y (p : Point3D) : (toComplexVec p).y = ↑p.y := rfl
@[simp] lemma toComplexVec_z (p : Point3D) : (toComplexVec p).z = ↑p.z := rfl

/-! ### Vertex Positions

The vertex positions `vertexR`, `vertexG`, `vertexB`, and `colorVertex` are
defined in `Core.lean` and imported here. They are the canonical source for
all vertex position calculations in Theorem 0.2.1.
-/

/-- Gradient of pressure function at a point
    ∇P_c(x) = -2(x - x_c) / (|x - x_c|² + ε²)²
    Returns a Point3D representing the gradient vector -/
noncomputable def pressureGradient (x_c : Point3D) (ε : ℝ) (x : Point3D) : Point3D :=
  let dx := x.x - x_c.x
  let dy := x.y - x_c.y
  let dz := x.z - x_c.z
  let r_sq := dx^2 + dy^2 + dz^2
  let denom := (r_sq + ε^2)^2
  ⟨-2 * dx / denom, -2 * dy / denom, -2 * dz / denom⟩

/-- Gradient of total chiral field at a point (§5.1)
    ∇χ_total = Σ_c e^{iφ_c} · a₀ · ∇P_c(x) -/
noncomputable def totalFieldGradient (a₀ ε : ℝ) (x : Point3D) : ComplexVector3D :=
  let gradR := pressureGradient vertexR ε x
  let gradG := pressureGradient vertexG ε x
  let gradB := pressureGradient vertexB ε x
  (↑a₀ * phaseR) • toComplexVec gradR +
  (↑a₀ * phaseG) • toComplexVec gradG +
  (↑a₀ * phaseB) • toComplexVec gradB

/-- At the center, the gradient involves the weighted sum of vertex positions
    ∇χ_total|₀ = 2a₀P₀² Σ_c x_c e^{iφ_c}

    This is non-zero because:
    x_R + x_G·ω + x_B·ω² ≠ 0 (vertices don't cancel like scalars)
-/
noncomputable def gradientWeightedVertexSum : ComplexVector3D :=
  phaseR • toComplexVec vertexR +
  phaseG • toComplexVec vertexG +
  phaseB • toComplexVec vertexB

/-- The x-component of the weighted vertex sum (from §5.2)
    x_R·1 + x_G·ω + x_B·ω² where x_R = x_G = 1/√3, x_B = -1/√3
    = (1/√3)[1 + ω - ω²] = (1/√3)[1 + (-1/2 + i√3/2) - (-1/2 - i√3/2)]
    = (1/√3)[1 + i√3] ≠ 0 -/
theorem gradient_x_component_explicit :
    gradientWeightedVertexSum.x =
    (1/Real.sqrt 3 : ℂ) * (1 + Complex.I * Real.sqrt 3) := by
  unfold gradientWeightedVertexSum
  rw [phaseR_eq_one, phaseG_explicit, phaseB_explicit]
  -- Use simp lemmas to access x-components through the structure operations
  simp only [ComplexVector3D.add_x, ComplexVector3D.smul_x, toComplexVec_x]
  unfold vertexR vertexG vertexB
  -- Now have: 1 * ↑(1/√3) + ⟨-1/2, √3/2⟩ * ↑(1/√3) + ⟨-1/2, -√3/2⟩ * ↑(-1/√3)
  -- Reduce to an equality of complex numbers
  apply Complex.ext
  · -- Real part
    simp only [Complex.mul_re, Complex.one_re, Complex.one_im,
               Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
               Complex.I_re, Complex.I_im, Complex.ofReal_div,
               Complex.div_re, Complex.div_im, Complex.ofReal_neg,
               Complex.neg_re, Complex.neg_im]
    ring
  · -- Imaginary part
    simp only [Complex.mul_im, Complex.one_re, Complex.one_im,
               Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
               Complex.I_re, Complex.I_im, Complex.ofReal_div,
               Complex.div_re, Complex.div_im, Complex.ofReal_neg,
               Complex.neg_re, Complex.neg_im]
    ring

/-- The weighted vertex sum is non-zero (gradient at center is non-zero)
    This is the KEY result enabling phase-gradient mass generation (Theorem 3.1.1) -/
theorem gradient_weighted_sum_nonzero :
    gradientWeightedVertexSum ≠ ComplexVector3D.zero := by
  intro h
  -- If the whole vector is zero, then x-component is zero
  have hx : gradientWeightedVertexSum.x = 0 := by
    simp only [ComplexVector3D.zero] at h
    exact congrArg ComplexVector3D.x h
  rw [gradient_x_component_explicit] at hx
  -- (1/√3)(1 + i√3) = 0 implies 1 + i√3 = 0 (since 1/√3 ≠ 0)
  have h_sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt3_ne : Real.sqrt 3 ≠ 0 := ne_of_gt h_sqrt3_pos
  have h_inv_ne : (1/Real.sqrt 3 : ℂ) ≠ 0 := by
    simp only [ne_eq, one_div, Complex.ofReal_eq_zero, inv_eq_zero]
    exact h_sqrt3_ne
  -- From (1/√3)(1 + i√3) = 0 and 1/√3 ≠ 0, we get 1 + i√3 = 0
  have h_sum_zero : (1 : ℂ) + Complex.I * Real.sqrt 3 = 0 := by
    have := mul_eq_zero.mp hx
    cases this with
    | inl h => exact absurd h h_inv_ne
    | inr h => exact h
  -- But 1 + i√3 ≠ 0 (real part is 1 ≠ 0)
  have h_re : (1 + Complex.I * Real.sqrt 3).re = 1 := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
               Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h_sum_zero] at h_re
  simp at h_re

/-- Physical interpretation: The gradient at center is non-zero
    This creates the "phase drag" that enables mass generation -/
theorem center_has_nonzero_gradient :
    gradientWeightedVertexSum ≠ ComplexVector3D.zero :=
  gradient_weighted_sum_nonzero

/-! ### Gradient Magnitude Equals 2

From §5.2 of the markdown, the gradient weighted vertex sum has exact magnitude 2:
|Σ x_c e^{iφ_c}|² = (1/3)[(1)² + (√3)² + (1)² + (√3)² + 4] = 4

This section proves this exact value, strengthening the non-zero proof above.
-/

/-- The y-component of the weighted vertex sum (from §5.2)
    y_R·1 + y_G·ω + y_B·ω² where y_R = 1/√3, y_G = -1/√3, y_B = 1/√3
    = (1/√3)[1 - ω + ω²] = (1/√3)[1 - i√3] -/
theorem gradient_y_component_explicit :
    gradientWeightedVertexSum.y =
    (1/Real.sqrt 3 : ℂ) * (1 - Complex.I * Real.sqrt 3) := by
  unfold gradientWeightedVertexSum
  rw [phaseR_eq_one, phaseG_explicit, phaseB_explicit]
  simp only [ComplexVector3D.add_y, ComplexVector3D.smul_y, toComplexVec_y]
  unfold vertexR vertexG vertexB
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.one_re, Complex.one_im,
               Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
               Complex.I_re, Complex.I_im, Complex.sub_re,
               Complex.ofReal_div, Complex.div_re, Complex.div_im]
    ring
  · simp only [Complex.mul_im, Complex.one_re, Complex.one_im,
               Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
               Complex.I_re, Complex.I_im, Complex.sub_im,
               Complex.ofReal_div, Complex.div_re, Complex.div_im]
    ring

/-- The z-component of the weighted vertex sum (from §5.2)
    z_R·1 + z_G·ω + z_B·ω² where z_R = 1/√3, z_G = -1/√3, z_B = -1/√3
    = (1/√3)[1 - ω - ω²] = (1/√3)[1 - (-1)] = 2/√3
    (using ω + ω² = -1) -/
theorem gradient_z_component_explicit :
    gradientWeightedVertexSum.z = (2/Real.sqrt 3 : ℂ) := by
  unfold gradientWeightedVertexSum
  rw [phaseR_eq_one, phaseG_explicit, phaseB_explicit]
  simp only [ComplexVector3D.add_z, ComplexVector3D.smul_z, toComplexVec_z]
  unfold vertexR vertexG vertexB
  -- The z-components are: R: 1/√3, G: -1/√3, B: -1/√3
  -- With phases: 1·(1/√3) + (-1/2 + i√3/2)·(-1/√3) + (-1/2 - i√3/2)·(-1/√3)
  -- = 1/√3 + (1/2 - i√3/2)/√3 + (1/2 + i√3/2)/√3 = 1/√3 + 1/√3 = 2/√3
  have h_sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt3_ne : Real.sqrt 3 ≠ 0 := ne_of_gt h_sqrt3_pos
  -- Simplify 2/√3 as a complex number
  have h_div : (2 / Real.sqrt 3 : ℂ) = ⟨2 / Real.sqrt 3, 0⟩ := by
    apply Complex.ext <;> simp
  rw [h_div]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.one_re, Complex.one_im,
               Complex.ofReal_re, Complex.ofReal_im, Complex.add_re]
    field_simp [h_sqrt3_ne]
    ring
  · simp only [Complex.mul_im, Complex.one_re, Complex.one_im,
               Complex.ofReal_re, Complex.ofReal_im, Complex.add_im]
    ring

/-- Helper: Complex norm squared of (1 + i√3) equals 4 -/
theorem normSq_one_plus_i_sqrt3 :
    Complex.normSq (1 + Complex.I * Real.sqrt 3) = 4 := by
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  -- normSq z = z.re^2 + z.im^2
  -- For z = 1 + i√3: re = 1, im = √3
  have hre : (1 + Complex.I * Real.sqrt 3).re = 1 := by simp
  have him : (1 + Complex.I * Real.sqrt 3).im = Real.sqrt 3 := by simp
  rw [Complex.normSq_apply, hre, him, hsq3]
  ring

/-- Helper: Complex norm squared of (1 - i√3) equals 4 -/
theorem normSq_one_minus_i_sqrt3 :
    Complex.normSq (1 - Complex.I * Real.sqrt 3) = 4 := by
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  -- For z = 1 - i√3: re = 1, im = -√3, so |z|² = 1 + (-√3)² = 1 + 3 = 4
  have hre : (1 - Complex.I * Real.sqrt 3).re = 1 := by simp
  have him : (1 - Complex.I * Real.sqrt 3).im = -Real.sqrt 3 := by simp
  have hneg : (-Real.sqrt 3) * (-Real.sqrt 3) = 3 := by rw [neg_mul_neg, hsq3]
  rw [Complex.normSq_apply, hre, him, hneg]
  ring

/-- Helper: Complex norm squared of 2 equals 4 -/
theorem normSq_two : Complex.normSq (2 : ℂ) = 4 := by
  simp only [Complex.normSq_ofNat]
  norm_num

/-- The squared magnitude of the gradient weighted vertex sum equals 4.

    From §5.2 of the markdown:
    |Σ x_c e^{iφ_c}|² = |x|² + |y|² + |z|²
    where:
      x = (1/√3)(1 + i√3), so |x|² = (1/3) · 4 = 4/3
      y = (1/√3)(1 - i√3), so |y|² = (1/3) · 4 = 4/3
      z = 2/√3,            so |z|² = 4/3

    Total: |Σ x_c e^{iφ_c}|² = 4/3 + 4/3 + 4/3 = 4 -/
theorem gradient_weighted_sum_normSq :
    Complex.normSq gradientWeightedVertexSum.x +
    Complex.normSq gradientWeightedVertexSum.y +
    Complex.normSq gradientWeightedVertexSum.z = 4 := by
  rw [gradient_x_component_explicit, gradient_y_component_explicit, gradient_z_component_explicit]
  -- Each component is (1/√3) × (some complex number with |·|² = 4)
  -- and |1/√3|² = 1/3, so each |component|² = 4/3
  have h_sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt3_ne : Real.sqrt 3 ≠ 0 := ne_of_gt h_sqrt3_pos
  have hsq3_mul : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  -- Calculate each term
  have hx : Complex.normSq ((1/Real.sqrt 3 : ℂ) * (1 + Complex.I * Real.sqrt 3)) = 4/3 := by
    rw [Complex.normSq_mul]
    simp only [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
    rw [normSq_one_plus_i_sqrt3, hsq3_mul]
    ring
  have hy : Complex.normSq ((1/Real.sqrt 3 : ℂ) * (1 - Complex.I * Real.sqrt 3)) = 4/3 := by
    rw [Complex.normSq_mul]
    simp only [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
    rw [normSq_one_minus_i_sqrt3, hsq3_mul]
    ring
  have hz : Complex.normSq (2/Real.sqrt 3 : ℂ) = 4/3 := by
    simp only [Complex.normSq_div, Complex.normSq_ofReal]
    rw [normSq_two, hsq3_mul]
  rw [hx, hy, hz]
  ring

/-- **KEY THEOREM:** The magnitude of the gradient weighted vertex sum equals 2.

    From Theorem 0.2.1 §5.2:
    |Σ_c x_c e^{iφ_c}| = 2

    This is stronger than the non-zero proof `gradient_weighted_sum_nonzero`
    and is used to compute the exact gradient magnitude at the center:
    |∇χ|₀ = 2a₀P₀² · 2 = 4a₀P₀²

    **Mathematical Citation:**
    This calculation appears explicitly in the markdown §5.2 with the component-wise
    breakdown showing the magnitude squared equals 4. -/
theorem gradient_weighted_sum_magnitude_eq_two :
    Real.sqrt (Complex.normSq gradientWeightedVertexSum.x +
               Complex.normSq gradientWeightedVertexSum.y +
               Complex.normSq gradientWeightedVertexSum.z) = 2 := by
  rw [gradient_weighted_sum_normSq]
  have h : (4 : ℝ) = 2^2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]

/-! ### Intermediate Lemmas for Gradient Proportionality

The following lemmas establish the key facts needed for
`totalFieldGradient_at_center_proportional`:

1. **Coordinate squares**: (1/√3)² = 1/3 and (-1/√3)² = 1/3
2. **Vertex distances**: Each vertex is at distance² = 1 from the center
3. **Denominator equality**: All three colors have the same denominator (1 + ε²)²
4. **Gradient simplification**: -2(0 - v)/denom² = 2v/denom² at center

These lemmas make the main proof's mathematical structure explicit.
-/

/-- Helper: (1/√3)² = 1/3 -/
theorem one_div_sqrt3_sq : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
  rw [div_pow, one_pow]
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
  rw [hsq3]

/-- Helper: (-1/√3)² = 1/3 -/
theorem neg_one_div_sqrt3_sq : (-1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
  rw [neg_div, neg_sq, one_div_sqrt3_sq]

/-- Vertex R is at distance² = 1 from the center.
    Calculation: (1/√3)² + (1/√3)² + (1/√3)² = 1/3 + 1/3 + 1/3 = 1 -/
theorem vertexR_distSq_from_center :
    (1/Real.sqrt 3)^2 + (1/Real.sqrt 3)^2 + (1/Real.sqrt 3)^2 = 1 := by
  rw [one_div_sqrt3_sq]; ring

/-- Vertex G is at distance² = 1 from the center.
    Calculation: (1/√3)² + (-1/√3)² + (-1/√3)² = 1/3 + 1/3 + 1/3 = 1 -/
theorem vertexG_distSq_from_center :
    (1/Real.sqrt 3)^2 + (-1/Real.sqrt 3)^2 + (-1/Real.sqrt 3)^2 = 1 := by
  rw [one_div_sqrt3_sq, neg_one_div_sqrt3_sq]; ring

/-- Vertex B is at distance² = 1 from the center.
    Calculation: (-1/√3)² + (1/√3)² + (-1/√3)² = 1/3 + 1/3 + 1/3 = 1 -/
theorem vertexB_distSq_from_center :
    (-1/Real.sqrt 3)^2 + (1/Real.sqrt 3)^2 + (-1/Real.sqrt 3)^2 = 1 := by
  rw [one_div_sqrt3_sq, neg_one_div_sqrt3_sq]; ring

/-- The denominator for vertex R at the center equals 1 + ε².
    At center (0,0,0), the distance² to vertex R is |0 - vertexR|² = |vertexR|² = 1. -/
theorem vertexR_denom_at_center (ε : ℝ) :
    (-(1/Real.sqrt 3))^2 + (-(1/Real.sqrt 3))^2 + (-(1/Real.sqrt 3))^2 + ε^2 = 1 + ε^2 := by
  simp only [neg_sq, one_div_sqrt3_sq]; ring

/-- The denominator for vertex G at the center equals 1 + ε². -/
theorem vertexG_denom_at_center (ε : ℝ) :
    (-(1/Real.sqrt 3))^2 + (-(-1/Real.sqrt 3))^2 + (-(-1/Real.sqrt 3))^2 + ε^2 = 1 + ε^2 := by
  simp only [neg_sq, one_div_sqrt3_sq, neg_one_div_sqrt3_sq]; ring

/-- The denominator for vertex B at the center equals 1 + ε². -/
theorem vertexB_denom_at_center (ε : ℝ) :
    (-(-1/Real.sqrt 3))^2 + (-(1/Real.sqrt 3))^2 + (-(-1/Real.sqrt 3))^2 + ε^2 = 1 + ε^2 := by
  simp only [neg_sq, one_div_sqrt3_sq, neg_one_div_sqrt3_sq]; ring

/-- The common denominator (1 + ε²)² is non-zero for positive ε. -/
theorem common_denom_ne_zero (ε : ℝ) (hε : 0 < ε) : (1 + ε^2)^2 ≠ 0 := by
  apply pow_ne_zero 2
  have h : 1 + ε^2 > 0 := by linarith [sq_nonneg ε]
  exact ne_of_gt h

/-- The proportionality constant k = 2a₀/(1 + ε²)² is positive for a₀ > 0, ε > 0. -/
theorem proportionality_constant_pos (a₀ ε : ℝ) (ha₀ : 0 < a₀) (hε : 0 < ε) :
    0 < 2 * a₀ / (1 + ε^2)^2 := by
  apply div_pos
  · linarith
  · apply pow_pos; linarith [sq_nonneg ε]

/-- The relationship between totalFieldGradient at center and gradientWeightedVertexSum

    At the center x = 0, the gradient of pressure function is:
      ∇P_c(0) = -2(0 - x_c) / (|0 - x_c|² + ε²)² = 2x_c / (|x_c|² + ε²)²

    Since all vertices are equidistant from center (|x_c|² = 1 for all c),
    the denominator is the same for all colors: (1 + ε²)²

    Therefore:
      ∇χ|₀ = Σ_c a₀ e^{iφ_c} · 2x_c / (1 + ε²)²
           = (2a₀/(1 + ε²)²) · Σ_c x_c e^{iφ_c}
           = (2a₀/(1 + ε²)²) · gradientWeightedVertexSum

    This proportionality constant is positive, so ∇χ|₀ ≠ 0 iff weighted sum ≠ 0.

    **Proof Structure:**
    1. Use `proportionality_constant_pos` for k > 0
    2. Apply `ComplexVector3D.ext` to prove component-by-component equality
    3. Use `vertexX_denom_at_center` to unify all denominators to (1 + ε²)²
    4. Use `field_simp` to clear denominators and verify algebraic equality -/
theorem totalFieldGradient_at_center_proportional (a₀ ε : ℝ) (ha₀ : 0 < a₀) (hε : 0 < ε) :
    ∃ (k : ℝ), 0 < k ∧
    totalFieldGradient a₀ ε stellaCenter =
      (k : ℂ) • gradientWeightedVertexSum := by
  -- The proportionality constant is 2a₀/(1 + ε²)²
  use 2 * a₀ / (1 + ε^2)^2
  constructor
  · -- k > 0: follows from intermediate lemma
    exact proportionality_constant_pos a₀ ε ha₀ hε
  · -- Equality of complex vectors: prove component-by-component
    unfold totalFieldGradient pressureGradient stellaCenter gradientWeightedVertexSum
    -- Get the common denominator fact
    have hdenom : (1 + ε^2)^2 ≠ 0 := common_denom_ne_zero ε hε
    -- Apply extensionality to prove each component matches
    apply ComplexVector3D.ext
    -- All three goals (x, y, z components) have the same structure:
    -- Expand, simplify with vertex_X_denom_at_center, then field_simp
    all_goals {
      simp only [ComplexVector3D.add_x, ComplexVector3D.add_y, ComplexVector3D.add_z,
                 ComplexVector3D.smul_x, ComplexVector3D.smul_y, ComplexVector3D.smul_z,
                 toComplexVec_x, toComplexVec_y, toComplexVec_z]
      unfold vertexR vertexG vertexB
      simp only [zero_sub]
      -- Apply the denominator lemmas to unify all three terms
      rw [vertexR_denom_at_center ε, vertexG_denom_at_center ε, vertexB_denom_at_center ε]
      -- Clear denominators and verify algebraic equality
      push_cast
      field_simp [hdenom]
    }

/-- The total field gradient at the center is explicitly non-zero.

    This follows from:
    1. totalFieldGradient a₀ ε stellaCenter = k • gradientWeightedVertexSum (proportionality)
    2. k > 0 (proportionality constant is positive)
    3. gradientWeightedVertexSum ≠ 0 (weighted sum is non-zero)

    Therefore: totalFieldGradient ≠ 0

    This is the KEY result for phase-gradient mass generation (Theorem 3.1.1): even at the node
    where χ_total = 0, the gradient ∇χ_total ≠ 0. -/
theorem totalFieldGradient_at_center_nonzero (a₀ ε : ℝ) (ha₀ : 0 < a₀) (hε : 0 < ε) :
    totalFieldGradient a₀ ε stellaCenter ≠ ComplexVector3D.zero := by
  -- Get the proportionality result
  obtain ⟨k, hk_pos, hk_eq⟩ := totalFieldGradient_at_center_proportional a₀ ε ha₀ hε
  -- Suppose the gradient were zero
  intro h_grad_zero
  -- Then (↑k : ℂ) • gradientWeightedVertexSum = 0
  rw [hk_eq] at h_grad_zero
  -- Since k > 0, (↑k : ℂ) ≠ 0
  have h_k_ne : (k : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hk_pos
  -- From (↑k : ℂ) • v = 0 and (↑k : ℂ) ≠ 0, we get v = 0
  have h_ws_zero : gradientWeightedVertexSum = ComplexVector3D.zero := by
    apply ComplexVector3D.ext
    · -- x-component: (↑k) * v.x = 0 with ↑k ≠ 0 implies v.x = 0
      have hx : ((k : ℂ) • gradientWeightedVertexSum).x = ComplexVector3D.zero.x :=
        congrArg ComplexVector3D.x h_grad_zero
      simp only [ComplexVector3D.smul_x, ComplexVector3D.zero] at hx
      exact (mul_eq_zero.mp hx).resolve_left h_k_ne
    · -- y-component
      have hy : ((k : ℂ) • gradientWeightedVertexSum).y = ComplexVector3D.zero.y :=
        congrArg ComplexVector3D.y h_grad_zero
      simp only [ComplexVector3D.smul_y, ComplexVector3D.zero] at hy
      exact (mul_eq_zero.mp hy).resolve_left h_k_ne
    · -- z-component
      have hz : ((k : ℂ) • gradientWeightedVertexSum).z = ComplexVector3D.zero.z :=
        congrArg ComplexVector3D.z h_grad_zero
      simp only [ComplexVector3D.smul_z, ComplexVector3D.zero] at hz
      exact (mul_eq_zero.mp hz).resolve_left h_k_ne
  -- But we proved gradientWeightedVertexSum ≠ 0
  exact gradient_weighted_sum_nonzero h_ws_zero

/-- At equal pressures at center, total field vanishes via equal_pressure_gives_zero -/
theorem equal_pressure_gives_zero (cfg : PressureModulatedConfig)
    (heq : ∀ c, cfg.pressure c stellaCenter = cfg.pressure ColorPhase.R stellaCenter) :
    pressureModulatedField cfg stellaCenter =
    (cfg.a₀ * cfg.pressure ColorPhase.R stellaCenter : ℂ) * (phaseR + phaseG + phaseB) := by
  -- All three terms have the same amplitude at center due to heq
  -- The result factors as (common amplitude) × (sum of phase exponentials)
  unfold pressureModulatedField totalChiralField colorContribution
  unfold PressureModulatedConfig.toAmplitudes
  simp only
  -- Use heq to show all three pressures are equal
  have hG : cfg.pressure ColorPhase.G stellaCenter = cfg.pressure ColorPhase.R stellaCenter :=
    heq ColorPhase.G
  have hB : cfg.pressure ColorPhase.B stellaCenter = cfg.pressure ColorPhase.R stellaCenter :=
    heq ColorPhase.B
  -- Rewrite using the common value
  rw [hG, hB]
  -- Now factor out the common amplitude and show it equals the goal
  -- phaseExp ColorPhase.X = phaseX by definition
  unfold phaseR phaseG phaseB
  -- The goal is now about the product of a real cast and a sum
  push_cast
  ring

/-- When pressures are equal at center, total field vanishes -/
theorem equal_pressure_field_zero (cfg : PressureModulatedConfig)
    (heq : ∀ c, cfg.pressure c stellaCenter = cfg.pressure ColorPhase.R stellaCenter) :
    pressureModulatedField cfg stellaCenter = 0 := by
  rw [equal_pressure_gives_zero cfg heq, phase_sum_zero, mul_zero]

end ChiralGeometrogenesis.Phase0.Theorem_0_2_1
