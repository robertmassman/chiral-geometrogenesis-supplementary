/-
  PureMath/LieAlgebra/Weights.lean

  SU(3) Weight Vectors and Weight Lattice

  This file defines the weight vectors of SU(3) representations using
  symbolic sqrt(3) handling (Option A).

  The fundamental representation has weights forming an equilateral triangle.
  Combined with anti-fundamental, we get 6 weights forming a regular hexagon.

  Reference: docs/proofs/Phase-Minus-1/Theorem-0.0.3.md
-/

import ChiralGeometrogenesis.PureMath.LieAlgebra.SU3
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.PureMath.LieAlgebra

/-! ## Sqrt(3) Properties (Option A: Symbolic Handling)

We use Real.sqrt 3 symbolically and prove its properties when needed.
-/

/-- √3 is positive -/
theorem sqrt_three_pos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)

/-- √3 squared equals 3 -/
theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)

/-- √3 is not zero -/
theorem sqrt_three_ne_zero : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt_three_pos

/-- 2√3 is not zero -/
theorem two_sqrt_three_ne_zero : 2 * Real.sqrt 3 ≠ 0 := by
  have : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  linarith [sqrt_three_pos]

/-! ## Weight Vectors

The weight vectors of SU(3) live in the 2D weight space (Cartan subalgebra dual).
They are the eigenvalues of T₃ and T₈ acting on representation states.

Fundamental representation (3): R, G, B quarks
Anti-fundamental representation (3̄): R̄, Ḡ, B̄ antiquarks
-/

/-- Weight vector as a structure (avoids instance issues with Fin 2 → ℝ) -/
structure WeightVector where
  t3 : ℝ   -- T₃ component (isospin)
  t8 : ℝ   -- T₈ component (hypercharge)

namespace WeightVector

/-! ### Basic Instances -/

/-- Addition of weight vectors -/
instance : Add WeightVector where
  add v w := ⟨v.t3 + w.t3, v.t8 + w.t8⟩

/-- Negation of weight vectors -/
instance : Neg WeightVector where
  neg v := ⟨-v.t3, -v.t8⟩

/-- Zero weight vector -/
instance : Zero WeightVector where
  zero := ⟨0, 0⟩

/-- Subtraction of weight vectors -/
instance : Sub WeightVector where
  sub v w := ⟨v.t3 - w.t3, v.t8 - w.t8⟩

/-- Scalar multiplication for weight vectors -/
noncomputable instance : SMul ℝ WeightVector where
  smul r v := ⟨r * v.t3, r * v.t8⟩

/-! ### DecidableEq and Repr Instances -/

/-- WeightVector extensionality lemma (component-wise) -/
@[ext]
theorem ext {v w : WeightVector} (h3 : v.t3 = w.t3) (h8 : v.t8 = w.t8) : v = w := by
  cases v; cases w; simp_all

/-- Decidable equality for weight vectors -/
noncomputable instance : DecidableEq WeightVector := fun v w =>
  if h : v.t3 = w.t3 ∧ v.t8 = w.t8 then
    isTrue (ext h.1 h.2)
  else
    isFalse (fun heq => h ⟨congrArg t3 heq, congrArg t8 heq⟩)

/-- Simp lemma for subtraction of weight vectors -/
@[simp]
theorem sub_mk (a b c d : ℝ) :
    WeightVector.mk a b - WeightVector.mk c d = WeightVector.mk (a - c) (b - d) := rfl

/-- Simp lemma for t3 component of subtraction -/
@[simp]
theorem sub_t3 (v w : WeightVector) : (v - w).t3 = v.t3 - w.t3 := rfl

/-- Simp lemma for t8 component of subtraction -/
@[simp]
theorem sub_t8 (v w : WeightVector) : (v - w).t8 = v.t8 - w.t8 := rfl

/-- Subtraction is consistent with addition and negation: v - w = v + (-w) -/
theorem sub_eq_add_neg (v w : WeightVector) : v - w = v + (-w) := rfl

/-- Simp lemma for addition of weight vectors -/
@[simp]
theorem add_mk (a b c d : ℝ) :
    WeightVector.mk a b + WeightVector.mk c d = WeightVector.mk (a + c) (b + d) := rfl

/-- Simp lemma for t3 component of addition -/
@[simp]
theorem add_t3 (v w : WeightVector) : (v + w).t3 = v.t3 + w.t3 := rfl

/-- Simp lemma for t8 component of addition -/
@[simp]
theorem add_t8 (v w : WeightVector) : (v + w).t8 = v.t8 + w.t8 := rfl

/-- Simp lemma for negation of weight vectors -/
@[simp]
theorem neg_mk (a b : ℝ) : -(WeightVector.mk a b) = WeightVector.mk (-a) (-b) := rfl

/-- Simp lemma for t3 component of negation -/
@[simp]
theorem neg_t3 (v : WeightVector) : (-v).t3 = -v.t3 := rfl

/-- Simp lemma for t8 component of negation -/
@[simp]
theorem neg_t8 (v : WeightVector) : (-v).t8 = -v.t8 := rfl

/-! ### Scalar Multiplication Simp Lemmas -/

/-- Simp lemma for scalar multiplication of weight vectors -/
@[simp]
theorem smul_mk (r : ℝ) (a b : ℝ) :
    r • WeightVector.mk a b = WeightVector.mk (r * a) (r * b) := rfl

/-- Simp lemma for t3 component of scalar multiplication -/
@[simp]
theorem smul_t3 (r : ℝ) (v : WeightVector) : (r • v).t3 = r * v.t3 := rfl

/-- Simp lemma for t8 component of scalar multiplication -/
@[simp]
theorem smul_t8 (r : ℝ) (v : WeightVector) : (r • v).t8 = r * v.t8 := rfl

/-- Simp lemma for zero weight t3 component -/
@[simp]
theorem zero_t3' : (0 : WeightVector).t3 = 0 := rfl

/-- Simp lemma for zero weight t8 component -/
@[simp]
theorem zero_t8' : (0 : WeightVector).t8 = 0 := rfl

/-! ### AddCommGroup Instance

Weight vectors form an abelian group under addition. This is essential for
working with root systems, as roots are defined as differences of weights.
-/

/-- Addition is associative -/
theorem add_assoc (u v w : WeightVector) : u + v + w = u + (v + w) := by
  apply ext <;> simp [_root_.add_assoc]

/-- Zero is a left identity for addition -/
theorem zero_add (v : WeightVector) : 0 + v = v := by
  ext <;> simp

/-- Zero is a right identity for addition -/
theorem add_zero (v : WeightVector) : v + 0 = v := by
  ext <;> simp

/-- Left negation gives zero -/
theorem neg_add_cancel (v : WeightVector) : -v + v = 0 := by
  apply ext <;> simp [_root_.add_comm]

/-- Addition is commutative -/
theorem add_comm' (v w : WeightVector) : v + w = w + v := by
  apply ext <;> simp [_root_.add_comm]

/-- WeightVector forms an AddCommGroup -/
instance : AddCommGroup WeightVector where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm'
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Module Instance

Weight vectors form a vector space over ℝ.
-/

/-- Scalar multiplication distributes over vector addition -/
theorem smul_add (r : ℝ) (v w : WeightVector) : r • (v + w) = r • v + r • w := by
  ext <;> simp [mul_add]

/-- Scalar addition distributes over scalar multiplication -/
theorem add_smul (r s : ℝ) (v : WeightVector) : (r + s) • v = r • v + s • v := by
  ext <;> simp [add_mul]

/-- Scalar multiplication is associative -/
theorem mul_smul (r s : ℝ) (v : WeightVector) : (r * s) • v = r • (s • v) := by
  ext <;> simp [mul_assoc]

/-- 1 acts as identity for scalar multiplication -/
theorem one_smul (v : WeightVector) : (1 : ℝ) • v = v := by
  ext <;> simp

/-- 0 scalar gives zero vector -/
theorem zero_smul (v : WeightVector) : (0 : ℝ) • v = 0 := by
  ext <;> simp

/-- Scalar times zero vector is zero -/
theorem smul_zero (r : ℝ) : r • (0 : WeightVector) = 0 := by
  ext <;> simp

/-- WeightVector forms a Module over ℝ -/
noncomputable instance : Module ℝ WeightVector where
  smul_add := smul_add
  add_smul := add_smul
  mul_smul := mul_smul
  one_smul := one_smul
  zero_smul := zero_smul
  smul_zero := smul_zero

end WeightVector

/-! ## Fundamental Representation Weights

The three weights of the fundamental representation form an equilateral triangle
centered at the origin.

In the (T₃, T₈) basis:
- w_R = (1/2, 1/(2√3))     -- Red quark
- w_G = (-1/2, 1/(2√3))    -- Green quark
- w_B = (0, -1/√3)         -- Blue quark
-/

/-- Weight of Red quark -/
noncomputable def w_R : WeightVector :=
  ⟨1/2, 1/(2 * Real.sqrt 3)⟩

/-- Weight of Green quark -/
noncomputable def w_G : WeightVector :=
  ⟨-1/2, 1/(2 * Real.sqrt 3)⟩

/-- Weight of Blue quark -/
noncomputable def w_B : WeightVector :=
  ⟨0, -1/Real.sqrt 3⟩

/-- The fundamental weights as a list -/
noncomputable def fundamentalWeights : List WeightVector := [w_R, w_G, w_B]

/-! ## Anti-Fundamental Representation Weights

The anti-fundamental weights are negatives of fundamental weights.
-/

/-- Weight of anti-Red antiquark -/
noncomputable def w_Rbar : WeightVector := -w_R

/-- Weight of anti-Green antiquark -/
noncomputable def w_Gbar : WeightVector := -w_G

/-- Weight of anti-Blue antiquark -/
noncomputable def w_Bbar : WeightVector := -w_B

/-- The anti-fundamental weights as a list -/
noncomputable def antiFundamentalWeights : List WeightVector := [w_Rbar, w_Gbar, w_Bbar]

/-- All 6 weight vertices form the hexagon -/
noncomputable def allWeightVertices : List WeightVector :=
  fundamentalWeights ++ antiFundamentalWeights

/-! ## Weight Vector Properties -/

/-- The T₃ components sum to zero -/
theorem fundamental_t3_sum_zero :
    w_R.t3 + w_G.t3 + w_B.t3 = 0 := by
  simp only [w_R, w_G, w_B]
  ring

/-- The T₈ components sum to zero -/
theorem fundamental_t8_sum_zero :
    w_R.t8 + w_G.t8 + w_B.t8 = 0 := by
  simp only [w_R, w_G, w_B]
  field_simp
  ring

/-! ## Squared Distances (avoiding sqrt in proofs)

We work with squared distances to avoid sqrt in proofs.
-/

/-- Squared Euclidean distance between weight vectors -/
noncomputable def weightDistSq (v w : WeightVector) : ℝ :=
  (v.t3 - w.t3)^2 + (v.t8 - w.t8)^2

/-- Squared distance between R and G weights -/
theorem dist_sq_R_G : weightDistSq w_R w_G = 1 := by
  simp only [weightDistSq, w_R, w_G]
  ring

/-- Squared distance between G and B weights (needs sqrt property) -/
theorem dist_sq_G_B : weightDistSq w_G w_B = 1 := by
  simp only [weightDistSq, w_G, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared distance between B and R weights -/
theorem dist_sq_B_R : weightDistSq w_B w_R = 1 := by
  simp only [weightDistSq, w_B, w_R]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- All fundamental weights are equidistant (equilateral triangle).
    Note: These are the DIAGONALS of the hexagon, not edges. -/
theorem fundamental_weights_equilateral :
    weightDistSq w_R w_G = 1 ∧
    weightDistSq w_G w_B = 1 ∧
    weightDistSq w_B w_R = 1 :=
  ⟨dist_sq_R_G, dist_sq_G_B, dist_sq_B_R⟩

/-! ## Squared Norm and Dot Product -/

/-- Squared norm of a weight vector from origin -/
noncomputable def weightNormSq (v : WeightVector) : ℝ :=
  v.t3^2 + v.t8^2

/-- Dot product of two weight vectors -/
noncomputable def weightDot (v w : WeightVector) : ℝ :=
  v.t3 * w.t3 + v.t8 * w.t8

/-- Dot product is commutative -/
theorem weightDot_comm (v w : WeightVector) : weightDot v w = weightDot w v := by
  simp only [weightDot]
  ring

/-- Distance is symmetric -/
theorem weightDistSq_comm (v w : WeightVector) : weightDistSq v w = weightDistSq w v := by
  simp only [weightDistSq]
  ring

/-- Distance from v to itself is zero -/
theorem weightDistSq_self (v : WeightVector) : weightDistSq v v = 0 := by
  simp only [weightDistSq]
  ring

/-- Squared distance is always non-negative -/
theorem weightDistSq_nonneg (v w : WeightVector) : 0 ≤ weightDistSq v w := by
  simp only [weightDistSq]
  apply add_nonneg <;> apply sq_nonneg

/-- Squared norm is always non-negative -/
theorem weightNormSq_nonneg (v : WeightVector) : 0 ≤ weightNormSq v := by
  simp only [weightNormSq]
  apply add_nonneg <;> apply sq_nonneg

/-- Squared norm is zero iff vector is zero -/
theorem weightNormSq_eq_zero_iff (v : WeightVector) : weightNormSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    simp only [weightNormSq] at h
    have h3 : v.t3^2 = 0 := by nlinarith [sq_nonneg v.t3, sq_nonneg v.t8]
    have h8 : v.t8^2 = 0 := by nlinarith [sq_nonneg v.t3, sq_nonneg v.t8]
    have ht3 : v.t3 = 0 := by nlinarith [sq_nonneg v.t3]
    have ht8 : v.t8 = 0 := by nlinarith [sq_nonneg v.t8]
    ext <;> simp_all
  · intro h
    simp [h, weightNormSq]

/-- Squared distance is zero iff vectors are equal -/
theorem weightDistSq_eq_zero_iff (v w : WeightVector) : weightDistSq v w = 0 ↔ v = w := by
  constructor
  · intro h
    simp only [weightDistSq] at h
    have h3 : (v.t3 - w.t3)^2 = 0 := by nlinarith [sq_nonneg (v.t3 - w.t3), sq_nonneg (v.t8 - w.t8)]
    have h8 : (v.t8 - w.t8)^2 = 0 := by nlinarith [sq_nonneg (v.t3 - w.t3), sq_nonneg (v.t8 - w.t8)]
    have ht3 : v.t3 = w.t3 := by nlinarith [sq_nonneg (v.t3 - w.t3)]
    have ht8 : v.t8 = w.t8 := by nlinarith [sq_nonneg (v.t8 - w.t8)]
    ext <;> assumption
  · intro h
    simp [h, weightDistSq]

/-- Squared norm equals dot product with self -/
theorem weightNormSq_eq_dot_self (v : WeightVector) : weightNormSq v = weightDot v v := by
  simp only [weightNormSq, weightDot]
  ring

/-! ## Hexagonal Arrangement

The 6 weight vertices (3 fundamental + 3 anti-fundamental) form a regular hexagon.
Going counterclockwise: R → Bbar → G → Rbar → B → Gbar → R

All hexagon edges have squared distance 1/3.
The fundamental triangle edges (R-G, G-B, B-R) are hexagon diagonals with distance² = 1.
-/

/-- Squared norm of the R weight is 1/3 (circumradius²).

This is a building block for `fundamental_weights_equal_norm` which proves all
three fundamental weights have the same squared norm. See also `norm_sq_R`. -/
theorem fundamental_weight_norm_sq : weightNormSq w_R = 1/3 := by
  simp only [weightNormSq, w_R]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Negation preserves squared norm -/
theorem neg_weight_norm_sq (v : WeightVector) : weightNormSq (-v) = weightNormSq v := by
  simp only [weightNormSq, WeightVector.neg_t3, WeightVector.neg_t8]
  ring

/-- Distance between v and -w equals distance between -v and w -/
theorem dist_neg_symm (v w : WeightVector) :
    weightDistSq v (-w) = weightDistSq (-v) w := by
  simp only [weightDistSq, WeightVector.neg_t3, WeightVector.neg_t8]
  ring

/-- Squared distance from R to Bbar (adjacent hexagon vertices) -/
theorem dist_sq_R_Bbar : weightDistSq w_R w_Bbar = 1/3 := by
  simp only [w_Bbar, w_B, w_R, weightDistSq, WeightVector.neg_t3, WeightVector.neg_t8]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared distance from Bbar to G (adjacent hexagon vertices) -/
theorem dist_sq_Bbar_G : weightDistSq w_Bbar w_G = 1/3 := by
  simp only [w_Bbar, w_B, w_G, weightDistSq, WeightVector.neg_t3, WeightVector.neg_t8]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared distance from G to Rbar (adjacent hexagon vertices) -/
theorem dist_sq_G_Rbar : weightDistSq w_G w_Rbar = 1/3 := by
  simp only [w_Rbar, w_R, w_G, weightDistSq, WeightVector.neg_t3, WeightVector.neg_t8]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared distance from Rbar to B (adjacent hexagon vertices) -/
theorem dist_sq_Rbar_B : weightDistSq w_Rbar w_B = 1/3 := by
  simp only [w_Rbar, w_R, w_B, weightDistSq, WeightVector.neg_t3, WeightVector.neg_t8]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared distance from B to Gbar (adjacent hexagon vertices) -/
theorem dist_sq_B_Gbar : weightDistSq w_B w_Gbar = 1/3 := by
  simp only [w_Gbar, w_G, w_B, weightDistSq, WeightVector.neg_t3, WeightVector.neg_t8]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared distance from Gbar to R (adjacent hexagon vertices) -/
theorem dist_sq_Gbar_R : weightDistSq w_Gbar w_R = 1/3 := by
  simp only [w_Gbar, w_G, w_R, weightDistSq, WeightVector.neg_t3, WeightVector.neg_t8]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- The 6 weights form a regular hexagon with edge length² = 1/3.

Going counterclockwise: R → Bbar → G → Rbar → B → Gbar → R
All 6 edges have squared distance 1/3.
-/
theorem weights_form_hexagon :
    weightDistSq w_R w_Bbar = 1/3 ∧
    weightDistSq w_Bbar w_G = 1/3 ∧
    weightDistSq w_G w_Rbar = 1/3 ∧
    weightDistSq w_Rbar w_B = 1/3 ∧
    weightDistSq w_B w_Gbar = 1/3 ∧
    weightDistSq w_Gbar w_R = 1/3 :=
  ⟨dist_sq_R_Bbar, dist_sq_Bbar_G, dist_sq_G_Rbar, dist_sq_Rbar_B, dist_sq_B_Gbar, dist_sq_Gbar_R⟩

/-! ## Connection to Color Phases

The three fundamental weights correspond to the three color phases R, G, B.
The angular separation in weight space is 2π/3.

For an equilateral triangle centered at origin with vertices at distance r,
the angle between any two vertices (as seen from origin) is 2π/3.

We verify this via dot products: cos(θ) = (v₁ · v₂)/(|v₁| |v₂|)
For equilateral triangle: cos(2π/3) = -1/2
-/

/-- Squared norm of R weight is 1/3 -/
theorem norm_sq_R : weightNormSq w_R = 1/3 := by
  simp only [weightNormSq, w_R]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared norm of G weight is 1/3 -/
theorem norm_sq_G : weightNormSq w_G = 1/3 := by
  simp only [weightNormSq, w_G]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared norm of B weight is 1/3 -/
theorem norm_sq_B : weightNormSq w_B = 1/3 := by
  simp only [weightNormSq, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  rw [h]
  ring

/-- All fundamental weights have equal norm (same distance from origin) -/
theorem fundamental_weights_equal_norm :
    weightNormSq w_R = 1/3 ∧ weightNormSq w_G = 1/3 ∧ weightNormSq w_B = 1/3 :=
  ⟨norm_sq_R, norm_sq_G, norm_sq_B⟩

/-- Squared norm of anti-R weight is 1/3 (same as R by negation symmetry) -/
theorem norm_sq_Rbar : weightNormSq w_Rbar = 1/3 := by
  rw [w_Rbar, neg_weight_norm_sq, norm_sq_R]

/-- Squared norm of anti-G weight is 1/3 -/
theorem norm_sq_Gbar : weightNormSq w_Gbar = 1/3 := by
  rw [w_Gbar, neg_weight_norm_sq, norm_sq_G]

/-- Squared norm of anti-B weight is 1/3 -/
theorem norm_sq_Bbar : weightNormSq w_Bbar = 1/3 := by
  rw [w_Bbar, neg_weight_norm_sq, norm_sq_B]

/-- All 6 weight vertices have the same squared norm 1/3 (lie on circle of radius 1/√3) -/
theorem all_weights_equal_norm :
    weightNormSq w_R = 1/3 ∧ weightNormSq w_G = 1/3 ∧ weightNormSq w_B = 1/3 ∧
    weightNormSq w_Rbar = 1/3 ∧ weightNormSq w_Gbar = 1/3 ∧ weightNormSq w_Bbar = 1/3 :=
  ⟨norm_sq_R, norm_sq_G, norm_sq_B, norm_sq_Rbar, norm_sq_Gbar, norm_sq_Bbar⟩

/-! ## Root Vectors — Complete A₂ Root System

The edges of the fundamental triangle encode root vectors of SU(3).
Root vectors are differences of weights: α = w_i - w_j.

**The A₂ root system has 6 roots:**
- Simple roots: α₁ = w_R - w_G, α₂ = w_G - w_B
- Third positive root: α₃ = α₁ + α₂ = w_R - w_B
- Negative roots: -α₁, -α₂, -α₃

**Key properties:**
- All roots have equal squared norm = 1
- Simple roots satisfy the Cartan matrix relation: 2(α₁·α₂)/(α₁·α₁) = -1
- The 6 roots form a regular hexagon in weight space
- Root sum: α₁ + α₂ + (-α₃) = 0 (color neutrality in root form)

**Physical interpretation:**
- α₁ = (1, 0): isospin transition (R ↔ G exchange)
- α₂ = (-1/2, √3/2): color transition involving B
- Root vectors are gluon color charges (adjoint representation)
-/

/-- Simple root α₁ = w_R - w_G = (1, 0) in (T₃, T₈) basis.

This is the "isospin" root connecting Red and Green quarks.
In the adjoint representation, it corresponds to the gluon (RḠ + GR̄)/√2. -/
noncomputable def root_alpha1 : WeightVector := w_R - w_G

/-- Simple root α₂ = w_G - w_B = (-1/2, √3/2) in (T₃, T₈) basis.

This root connects Green and Blue quarks. -/
noncomputable def root_alpha2 : WeightVector := w_G - w_B

/-- Third positive root α₃ = w_R - w_B = α₁ + α₂.

This is the highest root in the A₂ Dynkin diagram.
It connects Red and Blue directly. -/
noncomputable def root_alpha3 : WeightVector := w_R - w_B

/-- The T₃ component of α₁ is 1 -/
theorem root_alpha1_t3 : root_alpha1.t3 = 1 := by
  simp only [root_alpha1, WeightVector.sub_t3, w_R, w_G]
  ring

/-- The T₈ component of α₁ is 0 -/
theorem root_alpha1_t8 : root_alpha1.t8 = 0 := by
  simp only [root_alpha1, WeightVector.sub_t8, w_R, w_G]
  ring

/-- The T₃ component of α₂ is -1/2 -/
theorem root_alpha2_t3 : root_alpha2.t3 = -1/2 := by
  simp only [root_alpha2, WeightVector.sub_t3, w_G, w_B]
  ring

/-- The T₈ component of α₂ is √3/2.

Calculation: (1/(2√3)) - (-1/√3) = 1/(2√3) + 1/√3 = 1/(2√3) + 2/(2√3) = 3/(2√3) = √3/2 -/
theorem root_alpha2_t8 : root_alpha2.t8 = Real.sqrt 3 / 2 := by
  simp only [root_alpha2, WeightVector.sub_t8, w_G, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  -- 1/(2√3) - (-1/√3) = 1/(2√3) + 1/√3 = 3/(2√3) = √3/2
  field_simp
  ring_nf
  -- Goal: 3 = √3 * √3, which is √3^2 = 3
  linarith [sq_nonneg (Real.sqrt 3), h]

/-- The T₃ component of α₃ is 1/2 -/
theorem root_alpha3_t3 : root_alpha3.t3 = 1/2 := by
  simp only [root_alpha3, WeightVector.sub_t3, w_R, w_B]
  ring

/-- The T₈ component of α₃ is √3/2.

Calculation: (1/(2√3)) - (-1/√3) = 1/(2√3) + 2/(2√3) = 3/(2√3) = √3/2 -/
theorem root_alpha3_t8 : root_alpha3.t8 = Real.sqrt 3 / 2 := by
  simp only [root_alpha3, WeightVector.sub_t8, w_R, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  field_simp
  ring_nf
  -- Goal: 3 = √3 * √3
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    rw [← sq, h]
  linarith

/-- α₃ = α₁ + α₂ (additive closure of roots) -/
theorem root_alpha3_eq_sum : root_alpha3 = root_alpha1 + root_alpha2 := by
  apply WeightVector.ext
  · simp only [root_alpha3, root_alpha1, root_alpha2,
               WeightVector.sub_t3, WeightVector.add_t3, w_R, w_G, w_B]
    ring
  · simp only [root_alpha3, root_alpha1, root_alpha2,
               WeightVector.sub_t8, WeightVector.add_t8, w_R, w_G, w_B]
    ring

/-- Squared norm of α₁ is 1 (consistent with dist_sq_R_G) -/
theorem root_alpha1_norm_sq : weightNormSq root_alpha1 = 1 := by
  simp only [weightNormSq, root_alpha1, WeightVector.sub_t3, WeightVector.sub_t8, w_R, w_G]
  ring

/-- Squared norm of α₂ is 1 (consistent with dist_sq_G_B) -/
theorem root_alpha2_norm_sq : weightNormSq root_alpha2 = 1 := by
  simp only [weightNormSq, root_alpha2, WeightVector.sub_t3, WeightVector.sub_t8, w_G, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared norm of α₃ is 1 (consistent with dist_sq_B_R) -/
theorem root_alpha3_norm_sq : weightNormSq root_alpha3 = 1 := by
  simp only [weightNormSq, root_alpha3, WeightVector.sub_t3, WeightVector.sub_t8, w_R, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- All positive roots have equal squared norm 1 -/
theorem all_positive_roots_equal_norm :
    weightNormSq root_alpha1 = 1 ∧
    weightNormSq root_alpha2 = 1 ∧
    weightNormSq root_alpha3 = 1 :=
  ⟨root_alpha1_norm_sq, root_alpha2_norm_sq, root_alpha3_norm_sq⟩

/-- Dot product of simple roots α₁ · α₂ = -1/2.

This is the off-diagonal entry of the Cartan matrix (up to normalization).
The Cartan matrix entry A₁₂ = 2(α₁·α₂)/(α₁·α₁) = 2(-1/2)/1 = -1. -/
theorem root_dot_alpha1_alpha2 : weightDot root_alpha1 root_alpha2 = -1/2 := by
  simp only [weightDot, root_alpha1, root_alpha2,
             WeightVector.sub_t3, WeightVector.sub_t8, w_R, w_G, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, h]
  linarith

/-- Cartan matrix entry A₁₂ = 2(α₁·α₂)/(α₁·α₁) = -1.

The A₂ Cartan matrix is:
  ⎛  2  -1 ⎞
  ⎝ -1   2 ⎠

This encodes the angle between simple roots as cos(θ) = -1/2, i.e., θ = 2π/3. -/
theorem cartan_matrix_entry_12 :
    2 * weightDot root_alpha1 root_alpha2 / weightNormSq root_alpha1 = -1 := by
  rw [root_dot_alpha1_alpha2, root_alpha1_norm_sq]
  ring

/-- Cartan matrix entry A₂₁ = 2(α₂·α₁)/(α₂·α₂) = -1 (symmetric for A₂). -/
theorem cartan_matrix_entry_21 :
    2 * weightDot root_alpha2 root_alpha1 / weightNormSq root_alpha2 = -1 := by
  rw [weightDot_comm, root_dot_alpha1_alpha2, root_alpha2_norm_sq]
  ring

/-- Dot product α₁ · α₃ = 1/2 -/
theorem root_dot_alpha1_alpha3 : weightDot root_alpha1 root_alpha3 = 1/2 := by
  simp only [weightDot, root_alpha1, root_alpha3,
             WeightVector.sub_t3, WeightVector.sub_t8, w_R, w_G, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, h]
  linarith

/-- Dot product α₂ · α₃ = 1/2 -/
theorem root_dot_alpha2_alpha3 : weightDot root_alpha2 root_alpha3 = 1/2 := by
  simp only [weightDot, root_alpha2, root_alpha3,
             WeightVector.sub_t3, WeightVector.sub_t8, w_R, w_G, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, h]
  linarith

/-- t3 component of zero weight is 0 -/
@[simp] theorem WeightVector.zero_t3 : (0 : WeightVector).t3 = 0 := rfl

/-- t8 component of zero weight is 0 -/
@[simp] theorem WeightVector.zero_t8 : (0 : WeightVector).t8 = 0 := rfl

/-- Root sum closure: α₁ + α₂ - α₃ = 0 (equivalently, α₁ + α₂ = α₃).

This is the closure relation for the A₂ root system. -/
theorem root_sum_closure : root_alpha1 + root_alpha2 - root_alpha3 = 0 := by
  apply WeightVector.ext
  · simp only [root_alpha1, root_alpha2, root_alpha3,
               WeightVector.sub_t3, WeightVector.add_t3, WeightVector.zero_t3,
               w_R, w_G, w_B]
    ring
  · simp only [root_alpha1, root_alpha2, root_alpha3,
               WeightVector.sub_t8, WeightVector.add_t8, WeightVector.zero_t8,
               w_R, w_G, w_B]
    ring

/-- The 6 roots of SU(3) as a list: ±α₁, ±α₂, ±α₃ -/
noncomputable def su3_roots : List WeightVector :=
  [root_alpha1, root_alpha2, root_alpha3, -root_alpha1, -root_alpha2, -root_alpha3]

/-- SU(3) has exactly 6 roots (dimension of adjoint minus rank = 8 - 2 = 6) -/
theorem su3_root_count : su3_roots.length = 6 := rfl

/-- All 6 roots have equal squared norm 1 -/
theorem all_roots_equal_norm :
    ∀ α ∈ su3_roots, weightNormSq α = 1 := by
  intro α hα
  simp only [su3_roots, List.mem_cons, List.not_mem_nil, or_false] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact root_alpha1_norm_sq
  · exact root_alpha2_norm_sq
  · exact root_alpha3_norm_sq
  · rw [neg_weight_norm_sq]; exact root_alpha1_norm_sq
  · rw [neg_weight_norm_sq]; exact root_alpha2_norm_sq
  · rw [neg_weight_norm_sq]; exact root_alpha3_norm_sq

/-- The roots form a regular hexagon in weight space.

Going around: α₁ → α₃ → α₂ → -α₁ → -α₃ → -α₂ → α₁
Each step is a 60° rotation (π/3).
-/
theorem roots_form_hexagon :
    weightDistSq root_alpha1 root_alpha3 = 1 ∧
    weightDistSq root_alpha3 root_alpha2 = 1 ∧
    weightDistSq root_alpha2 (-root_alpha1) = 1 ∧
    weightDistSq (-root_alpha1) (-root_alpha3) = 1 ∧
    weightDistSq (-root_alpha3) (-root_alpha2) = 1 ∧
    weightDistSq (-root_alpha2) root_alpha1 = 1 := by
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [weightDistSq, root_alpha1, root_alpha2, root_alpha3,
               WeightVector.sub_t3, WeightVector.sub_t8, WeightVector.neg_t3, WeightVector.neg_t8,
               w_R, w_G, w_B]
    field_simp
    nlinarith [sq_nonneg (Real.sqrt 3), hsq]

/-- Dot product of R and G weights is -1/6 -/
theorem dot_R_G : weightDot w_R w_G = -1/6 := by
  simp only [weightDot, w_R, w_G]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Dot product of G and B weights is -1/6 -/
theorem dot_G_B : weightDot w_G w_B = -1/6 := by
  simp only [weightDot, w_G, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- Dot product of B and R weights is -1/6 -/
theorem dot_B_R : weightDot w_B w_R = -1/6 := by
  simp only [weightDot, w_B, w_R]
  have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp
  ring_nf
  rw [h]
  ring

/-- All pairs of distinct fundamental weights have dot product -1/6.

This confirms the equilateral triangle property: for an equilateral triangle
centered at origin with vertices at distance r, adjacent vertices have
dot product = r² cos(2π/3) = r² (-1/2) = (1/3)(-1/2) = -1/6.
-/
theorem fundamental_weights_dot_products :
    weightDot w_R w_G = -1/6 ∧ weightDot w_G w_B = -1/6 ∧ weightDot w_B w_R = -1/6 :=
  ⟨dot_R_G, dot_G_B, dot_B_R⟩

/--
The cosine of angle between R and G weights is -1/2.

**Standard formula:** For vectors v, w: cos(θ) = (v · w)/(|v| |w|)

**Squared form:** Since |v|² = weightNormSq v, we have:
  cos²(θ) = (v · w)² / (|v|² |w|²)

**Simplification for equal-norm vectors:** When |v| = |w| (as holds for all
fundamental weights by `fundamental_weights_equal_norm`), we can write:
  cos(θ) = (v · w) / |v|² = (v · w) / weightNormSq v

This is valid because |v|·|w| = |v|² when |v| = |w|.

**Calculation:**
  cos(θ) = (-1/6) / (1/3) = -1/2

This verifies the angular separation is 2π/3 (since cos(2π/3) = -1/2).
-/
theorem cosine_angle_R_G :
    weightDot w_R w_G / weightNormSq w_R = -1/2 := by
  rw [dot_R_G, norm_sq_R]
  ring

/--
Squared cosine formula using both norms (standard form).

This is equivalent to `cosine_angle_R_G` since `weightNormSq w_R = weightNormSq w_G = 1/3`.
The squared form avoids square roots while still capturing the angular relationship.

**Derivation:**
  cos²(θ) = (v · w)² / (|v|² |w|²)
          = (-1/6)² / ((1/3)(1/3))
          = (1/36) / (1/9)
          = 1/4

Since cos(2π/3) = -1/2, we have cos²(2π/3) = 1/4. ✓
-/
theorem cosine_sq_angle_R_G :
    (weightDot w_R w_G)^2 / (weightNormSq w_R * weightNormSq w_G) = 1/4 := by
  rw [dot_R_G, norm_sq_R, norm_sq_G]
  norm_num

/--
The angular separation between adjacent fundamental weights satisfies cos(θ) = -1/2,
which means θ = 2π/3. This is proven algebraically via dot products.
-/
theorem weight_angular_separation_cosine :
    ∀ (v w : WeightVector),
      (v = w_R ∧ w = w_G) ∨ (v = w_G ∧ w = w_B) ∨ (v = w_B ∧ w = w_R) →
      weightDot v w / weightNormSq v = -1/2 := by
  intro v w hvw
  rcases hvw with ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩
  · rw [hv, hw, dot_R_G, norm_sq_R]; ring
  · simp only [hv, hw, weightDot, weightNormSq, w_G, w_B]
    have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
    have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
    field_simp
    rw [h]
    ring
  · simp only [hv, hw, weightDot, weightNormSq, w_B, w_R]
    have h : Real.sqrt 3 ^ 2 = 3 := sqrt_three_sq
    have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
    field_simp
    rw [h]
    ring

/-! ## Weight Vector Distinctness

The six fundamental and anti-fundamental weights are all distinct.
This is needed for bijection proofs in Theorem 1.1.1.
-/

/-- w_R ≠ w_G: Red and Green weights are distinct (t3 components differ) -/
theorem w_R_ne_w_G : w_R ≠ w_G := by
  intro h
  have : w_R.t3 = w_G.t3 := congrArg WeightVector.t3 h
  simp only [w_R, w_G] at this
  linarith

/-- w_R ≠ w_B: Red and Blue weights are distinct (t3 components differ) -/
theorem w_R_ne_w_B : w_R ≠ w_B := by
  intro h
  have : w_R.t3 = w_B.t3 := congrArg WeightVector.t3 h
  simp only [w_R, w_B] at this
  linarith

/-- w_G ≠ w_B: Green and Blue weights are distinct (t3 components differ) -/
theorem w_G_ne_w_B : w_G ≠ w_B := by
  intro h
  have : w_G.t3 = w_B.t3 := congrArg WeightVector.t3 h
  simp only [w_G, w_B] at this
  linarith

/-- All fundamental weights are pairwise distinct -/
theorem fundamental_weights_distinct :
    w_R ≠ w_G ∧ w_R ≠ w_B ∧ w_G ≠ w_B :=
  ⟨w_R_ne_w_G, w_R_ne_w_B, w_G_ne_w_B⟩

/-- w_Rbar ≠ w_Gbar: follows from w_R ≠ w_G by negation -/
theorem w_Rbar_ne_w_Gbar : w_Rbar ≠ w_Gbar := by
  intro h
  have heq : w_Rbar.t3 = w_Gbar.t3 := congrArg WeightVector.t3 h
  simp only [w_Rbar, w_Gbar, w_R, w_G, WeightVector.neg_t3] at heq
  linarith

/-- w_Rbar ≠ w_Bbar: follows from w_R ≠ w_B by negation -/
theorem w_Rbar_ne_w_Bbar : w_Rbar ≠ w_Bbar := by
  intro h
  have heq : w_Rbar.t3 = w_Bbar.t3 := congrArg WeightVector.t3 h
  simp only [w_Rbar, w_Bbar, w_R, w_B, WeightVector.neg_t3] at heq
  linarith

/-- w_Gbar ≠ w_Bbar: follows from w_G ≠ w_B by negation -/
theorem w_Gbar_ne_w_Bbar : w_Gbar ≠ w_Bbar := by
  intro h
  have heq : w_Gbar.t3 = w_Bbar.t3 := congrArg WeightVector.t3 h
  simp only [w_Gbar, w_Bbar, w_G, w_B, WeightVector.neg_t3] at heq
  linarith

/-- All anti-fundamental weights are pairwise distinct -/
theorem antifundamental_weights_distinct :
    w_Rbar ≠ w_Gbar ∧ w_Rbar ≠ w_Bbar ∧ w_Gbar ≠ w_Bbar :=
  ⟨w_Rbar_ne_w_Gbar, w_Rbar_ne_w_Bbar, w_Gbar_ne_w_Bbar⟩

/-- Fundamental and anti-fundamental weights don't overlap -/
theorem w_R_ne_w_Rbar : w_R ≠ w_Rbar := by
  intro h
  have : w_R.t3 = w_Rbar.t3 := congrArg WeightVector.t3 h
  simp only [w_R, w_Rbar, WeightVector.neg_t3] at this
  linarith

theorem w_R_ne_w_Gbar : w_R ≠ w_Gbar := by
  intro h
  have : w_R.t8 = w_Gbar.t8 := congrArg WeightVector.t8 h
  simp only [w_R, w_Gbar, w_G, WeightVector.neg_t8] at this
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp at this
  linarith [sqrt_three_pos]

theorem w_R_ne_w_Bbar : w_R ≠ w_Bbar := by
  intro h
  have : w_R.t8 = w_Bbar.t8 := congrArg WeightVector.t8 h
  simp only [w_R, w_Bbar, w_B, WeightVector.neg_t8] at this
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp at this
  -- 1/(2*sqrt 3) ≠ 1/sqrt 3 since 1 ≠ 2
  have hsqrt : Real.sqrt 3 > 0 := sqrt_three_pos
  nlinarith

theorem w_G_ne_w_Rbar : w_G ≠ w_Rbar := by
  intro h
  have : w_G.t8 = w_Rbar.t8 := congrArg WeightVector.t8 h
  simp only [w_G, w_Rbar, w_R, WeightVector.neg_t8] at this
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp at this
  linarith [sqrt_three_pos]

theorem w_G_ne_w_Gbar : w_G ≠ w_Gbar := by
  intro h
  have : w_G.t3 = w_Gbar.t3 := congrArg WeightVector.t3 h
  simp only [w_G, w_Gbar, WeightVector.neg_t3] at this
  linarith

theorem w_G_ne_w_Bbar : w_G ≠ w_Bbar := by
  intro h
  have : w_G.t8 = w_Bbar.t8 := congrArg WeightVector.t8 h
  simp only [w_G, w_Bbar, w_B, WeightVector.neg_t8] at this
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp at this
  have hsqrt : Real.sqrt 3 > 0 := sqrt_three_pos
  nlinarith

theorem w_B_ne_w_Rbar : w_B ≠ w_Rbar := by
  intro h
  have : w_B.t8 = w_Rbar.t8 := congrArg WeightVector.t8 h
  simp only [w_B, w_Rbar, w_R, WeightVector.neg_t8] at this
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp at this
  have hsqrt : Real.sqrt 3 > 0 := sqrt_three_pos
  nlinarith

theorem w_B_ne_w_Gbar : w_B ≠ w_Gbar := by
  intro h
  have : w_B.t8 = w_Gbar.t8 := congrArg WeightVector.t8 h
  simp only [w_B, w_Gbar, w_G, WeightVector.neg_t8] at this
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp at this
  have hsqrt : Real.sqrt 3 > 0 := sqrt_three_pos
  nlinarith

theorem w_B_ne_w_Bbar : w_B ≠ w_Bbar := by
  intro h
  have : w_B.t8 = w_Bbar.t8 := congrArg WeightVector.t8 h
  simp only [w_B, w_Bbar, WeightVector.neg_t8] at this
  have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
  field_simp at this
  linarith [sqrt_three_pos]

/-- All 6 weights are pairwise distinct (15 pairs) -/
theorem all_weights_pairwise_distinct :
    -- Within fundamental
    w_R ≠ w_G ∧ w_R ≠ w_B ∧ w_G ≠ w_B ∧
    -- Within anti-fundamental
    w_Rbar ≠ w_Gbar ∧ w_Rbar ≠ w_Bbar ∧ w_Gbar ≠ w_Bbar ∧
    -- Cross (R with anti)
    w_R ≠ w_Rbar ∧ w_R ≠ w_Gbar ∧ w_R ≠ w_Bbar ∧
    -- Cross (G with anti)
    w_G ≠ w_Rbar ∧ w_G ≠ w_Gbar ∧ w_G ≠ w_Bbar ∧
    -- Cross (B with anti)
    w_B ≠ w_Rbar ∧ w_B ≠ w_Gbar ∧ w_B ≠ w_Bbar :=
  ⟨w_R_ne_w_G, w_R_ne_w_B, w_G_ne_w_B,
   w_Rbar_ne_w_Gbar, w_Rbar_ne_w_Bbar, w_Gbar_ne_w_Bbar,
   w_R_ne_w_Rbar, w_R_ne_w_Gbar, w_R_ne_w_Bbar,
   w_G_ne_w_Rbar, w_G_ne_w_Gbar, w_G_ne_w_Bbar,
   w_B_ne_w_Rbar, w_B_ne_w_Gbar, w_B_ne_w_Bbar⟩

/-! ## Root Vector Distinctness

The six roots ±α₁, ±α₂, ±α₃ are pairwise distinct.
This is required for the root system to be well-defined.
-/

/-- α₁ ≠ α₂ (different T₃ components) -/
theorem root_alpha1_ne_alpha2 : root_alpha1 ≠ root_alpha2 := by
  intro h
  have : root_alpha1.t3 = root_alpha2.t3 := congrArg WeightVector.t3 h
  rw [root_alpha1_t3, root_alpha2_t3] at this
  linarith

/-- α₁ ≠ α₃ (different T₈ components) -/
theorem root_alpha1_ne_alpha3 : root_alpha1 ≠ root_alpha3 := by
  intro h
  have : root_alpha1.t8 = root_alpha3.t8 := congrArg WeightVector.t8 h
  rw [root_alpha1_t8, root_alpha3_t8] at this
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  linarith

/-- α₂ ≠ α₃ (different T₃ components) -/
theorem root_alpha2_ne_alpha3 : root_alpha2 ≠ root_alpha3 := by
  intro h
  have : root_alpha2.t3 = root_alpha3.t3 := congrArg WeightVector.t3 h
  rw [root_alpha2_t3, root_alpha3_t3] at this
  linarith

/-- α₁ ≠ -α₁ (non-zero root) -/
theorem root_alpha1_ne_neg : root_alpha1 ≠ -root_alpha1 := by
  intro h
  have : root_alpha1.t3 = (-root_alpha1).t3 := congrArg WeightVector.t3 h
  simp only [WeightVector.neg_t3, root_alpha1_t3] at this
  linarith

/-- α₂ ≠ -α₂ (non-zero root) -/
theorem root_alpha2_ne_neg : root_alpha2 ≠ -root_alpha2 := by
  intro h
  have : root_alpha2.t8 = (-root_alpha2).t8 := congrArg WeightVector.t8 h
  simp only [WeightVector.neg_t8, root_alpha2_t8] at this
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  linarith

/-- α₃ ≠ -α₃ (non-zero root) -/
theorem root_alpha3_ne_neg : root_alpha3 ≠ -root_alpha3 := by
  intro h
  have : root_alpha3.t3 = (-root_alpha3).t3 := congrArg WeightVector.t3 h
  simp only [WeightVector.neg_t3, root_alpha3_t3] at this
  linarith

/-- α₁ ≠ -α₂ -/
theorem root_alpha1_ne_neg_alpha2 : root_alpha1 ≠ -root_alpha2 := by
  intro h
  have : root_alpha1.t8 = (-root_alpha2).t8 := congrArg WeightVector.t8 h
  simp only [WeightVector.neg_t8, root_alpha1_t8, root_alpha2_t8] at this
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  linarith

/-- α₁ ≠ -α₃ -/
theorem root_alpha1_ne_neg_alpha3 : root_alpha1 ≠ -root_alpha3 := by
  intro h
  have : root_alpha1.t3 = (-root_alpha3).t3 := congrArg WeightVector.t3 h
  simp only [WeightVector.neg_t3, root_alpha1_t3, root_alpha3_t3] at this
  linarith

/-- α₂ ≠ -α₁ -/
theorem root_alpha2_ne_neg_alpha1 : root_alpha2 ≠ -root_alpha1 := by
  intro h
  have : root_alpha2.t8 = (-root_alpha1).t8 := congrArg WeightVector.t8 h
  simp only [WeightVector.neg_t8, root_alpha1_t8, root_alpha2_t8] at this
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  linarith

/-- α₂ ≠ -α₃ (t3 components: -1/2 vs -1/2, so use t8: √3/2 vs -√3/2) -/
theorem root_alpha2_ne_neg_alpha3 : root_alpha2 ≠ -root_alpha3 := by
  intro h
  have : root_alpha2.t8 = (-root_alpha3).t8 := congrArg WeightVector.t8 h
  simp only [WeightVector.neg_t8, root_alpha2_t8, root_alpha3_t8] at this
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  linarith

/-- α₃ ≠ -α₁ -/
theorem root_alpha3_ne_neg_alpha1 : root_alpha3 ≠ -root_alpha1 := by
  intro h
  have : root_alpha3.t3 = (-root_alpha1).t3 := congrArg WeightVector.t3 h
  simp only [WeightVector.neg_t3, root_alpha1_t3, root_alpha3_t3] at this
  linarith

/-- α₃ ≠ -α₂ (t3 components: 1/2 vs 1/2, so use t8: √3/2 vs -√3/2) -/
theorem root_alpha3_ne_neg_alpha2 : root_alpha3 ≠ -root_alpha2 := by
  intro h
  have : root_alpha3.t8 = (-root_alpha2).t8 := congrArg WeightVector.t8 h
  simp only [WeightVector.neg_t8, root_alpha2_t8, root_alpha3_t8] at this
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  linarith

/-- -α₁ ≠ -α₂ -/
theorem neg_alpha1_ne_neg_alpha2 : -root_alpha1 ≠ -root_alpha2 := by
  intro h
  have : (-root_alpha1).t3 = (-root_alpha2).t3 := congrArg WeightVector.t3 h
  simp only [WeightVector.neg_t3, root_alpha1_t3, root_alpha2_t3] at this
  linarith

/-- -α₁ ≠ -α₃ -/
theorem neg_alpha1_ne_neg_alpha3 : -root_alpha1 ≠ -root_alpha3 := by
  intro h
  have : (-root_alpha1).t8 = (-root_alpha3).t8 := congrArg WeightVector.t8 h
  simp only [WeightVector.neg_t8, root_alpha1_t8, root_alpha3_t8] at this
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  linarith

/-- -α₂ ≠ -α₃ -/
theorem neg_alpha2_ne_neg_alpha3 : -root_alpha2 ≠ -root_alpha3 := by
  intro h
  have : (-root_alpha2).t3 = (-root_alpha3).t3 := congrArg WeightVector.t3 h
  simp only [WeightVector.neg_t3, root_alpha2_t3, root_alpha3_t3] at this
  linarith

/-- All 6 roots are pairwise distinct (15 pairs) -/
theorem all_roots_pairwise_distinct :
    -- Positive roots among themselves
    root_alpha1 ≠ root_alpha2 ∧ root_alpha1 ≠ root_alpha3 ∧ root_alpha2 ≠ root_alpha3 ∧
    -- Negative roots among themselves
    -root_alpha1 ≠ -root_alpha2 ∧ -root_alpha1 ≠ -root_alpha3 ∧ -root_alpha2 ≠ -root_alpha3 ∧
    -- Positive ≠ own negative
    root_alpha1 ≠ -root_alpha1 ∧ root_alpha2 ≠ -root_alpha2 ∧ root_alpha3 ≠ -root_alpha3 ∧
    -- Cross: α₁ with other negatives
    root_alpha1 ≠ -root_alpha2 ∧ root_alpha1 ≠ -root_alpha3 ∧
    -- Cross: α₂ with other negatives
    root_alpha2 ≠ -root_alpha1 ∧ root_alpha2 ≠ -root_alpha3 ∧
    -- Cross: α₃ with other negatives
    root_alpha3 ≠ -root_alpha1 ∧ root_alpha3 ≠ -root_alpha2 :=
  ⟨root_alpha1_ne_alpha2, root_alpha1_ne_alpha3, root_alpha2_ne_alpha3,
   neg_alpha1_ne_neg_alpha2, neg_alpha1_ne_neg_alpha3, neg_alpha2_ne_neg_alpha3,
   root_alpha1_ne_neg, root_alpha2_ne_neg, root_alpha3_ne_neg,
   root_alpha1_ne_neg_alpha2, root_alpha1_ne_neg_alpha3,
   root_alpha2_ne_neg_alpha1, root_alpha2_ne_neg_alpha3,
   root_alpha3_ne_neg_alpha1, root_alpha3_ne_neg_alpha2⟩

/-! ## A₂ Root System Axioms

The A₂ root system satisfies the standard axioms for a crystallographic root system:
1. Roots span the weight space
2. Reflection closure: reflecting any root across any other root stays in the system
3. Integrality: 2(α·β)/(α·α) ∈ ℤ for all roots α, β

We prove these properties, establishing that our weight vectors form a bona fide
A₂ root system isomorphic to the standard one.
-/

/-- Weyl reflection of v across root α.

The Weyl reflection formula is: s_α(v) = v - 2(v·α)/(α·α) α

For the A₂ root system, all roots have norm² = 1, so this simplifies to:
s_α(v) = v - 2(v·α)α -/
noncomputable def weylReflection (α v : WeightVector) : WeightVector :=
  v - (2 * weightDot v α / weightNormSq α) • α

/-- Weyl reflection formula simplifies when α has norm 1 -/
theorem weylReflection_unit_norm (α v : WeightVector) (hα : weightNormSq α = 1) :
    weylReflection α v = v - (2 * weightDot v α) • α := by
  simp only [weylReflection, hα, div_one]

/-- Simple roots span the weight space.

Any weight vector can be written as a linear combination of α₁ and α₂.
This is because α₁ = (1, 0) and α₂ = (-1/2, √3/2) form a basis for ℝ².

For any v = (t3, t8), we have:
  v = a·α₁ + b·α₂ where a = t3 + t8/√3, b = 2t8/√3

Proof: The determinant of [α₁ | α₂] = 1·(√3/2) - 0·(-1/2) = √3/2 ≠ 0
-/
theorem simple_roots_span (v : WeightVector) :
    ∃ a b : ℝ, v = a • root_alpha1 + b • root_alpha2 := by
  use v.t3 + v.t8 / Real.sqrt 3, 2 * v.t8 / Real.sqrt 3
  apply WeightVector.ext
  · simp only [WeightVector.add_t3, WeightVector.smul_t3,
               root_alpha1_t3, root_alpha2_t3]
    ring
  · simp only [WeightVector.add_t8, WeightVector.smul_t8,
               root_alpha1_t8, root_alpha2_t8]
    have hne : Real.sqrt 3 ≠ 0 := sqrt_three_ne_zero
    field_simp
    ring

/-- The determinant of the simple root matrix is √3/2 (non-zero, confirming basis).

Matrix: ⎛ α₁.t3  α₂.t3 ⎞ = ⎛  1    -1/2  ⎞
        ⎝ α₁.t8  α₂.t8 ⎠   ⎝  0    √3/2  ⎠

det = 1·(√3/2) - 0·(-1/2) = √3/2 -/
theorem simple_roots_determinant :
    root_alpha1.t3 * root_alpha2.t8 - root_alpha1.t8 * root_alpha2.t3 = Real.sqrt 3 / 2 := by
  rw [root_alpha1_t3, root_alpha1_t8, root_alpha2_t3, root_alpha2_t8]
  ring

/-- Simple roots are linearly independent -/
theorem simple_roots_lin_indep :
    ∀ a b : ℝ, a • root_alpha1 + b • root_alpha2 = 0 → a = 0 ∧ b = 0 := by
  intro a b h
  have h3 : (a • root_alpha1 + b • root_alpha2).t3 = 0 := by rw [h]; rfl
  have h8 : (a • root_alpha1 + b • root_alpha2).t8 = 0 := by rw [h]; rfl
  simp only [WeightVector.add_t3, WeightVector.add_t8, WeightVector.smul_t3, WeightVector.smul_t8,
             root_alpha1_t3, root_alpha1_t8, root_alpha2_t3, root_alpha2_t8] at h3 h8
  -- h3: a * 1 + b * (-1/2) = 0, i.e., a = b/2
  -- h8: a * 0 + b * (√3/2) = 0, i.e., b * √3/2 = 0
  have hpos : Real.sqrt 3 > 0 := sqrt_three_pos
  -- From h8: b * (√3/2) = 0, and √3 > 0, so b = 0
  have hb : b = 0 := by nlinarith
  -- From h3: a - b/2 = 0, and b = 0, so a = 0
  constructor
  · linarith
  · exact hb

/-- Cartan integer A₁₂ = 2(α₁·α₂)/(α₁·α₁) = -1 is an integer -/
theorem cartan_12_is_integer :
    ∃ n : ℤ, 2 * weightDot root_alpha1 root_alpha2 / weightNormSq root_alpha1 = n := by
  use -1
  simp only [Int.cast_neg, Int.cast_one]
  rw [cartan_matrix_entry_12]

/-- Cartan integer A₂₁ = 2(α₂·α₁)/(α₂·α₂) = -1 is an integer -/
theorem cartan_21_is_integer :
    ∃ n : ℤ, 2 * weightDot root_alpha2 root_alpha1 / weightNormSq root_alpha2 = n := by
  use -1
  simp only [Int.cast_neg, Int.cast_one]
  rw [cartan_matrix_entry_21]

/-- Cartan integer A₁₁ = 2(α₁·α₁)/(α₁·α₁) = 2 -/
theorem cartan_11 : 2 * weightDot root_alpha1 root_alpha1 / weightNormSq root_alpha1 = 2 := by
  rw [← weightNormSq_eq_dot_self, root_alpha1_norm_sq]
  ring

/-- Cartan integer A₂₂ = 2(α₂·α₂)/(α₂·α₂) = 2 -/
theorem cartan_22 : 2 * weightDot root_alpha2 root_alpha2 / weightNormSq root_alpha2 = 2 := by
  rw [← weightNormSq_eq_dot_self, root_alpha2_norm_sq]
  ring

/-- The A₂ Cartan matrix entries are all integers.

The Cartan matrix is:
  A = ⎛  2  -1 ⎞
      ⎝ -1   2 ⎠

This confirms the crystallographic property of the A₂ root system. -/
theorem cartan_matrix_integer_entries :
    (∃ n : ℤ, 2 * weightDot root_alpha1 root_alpha1 / weightNormSq root_alpha1 = n) ∧
    (∃ n : ℤ, 2 * weightDot root_alpha1 root_alpha2 / weightNormSq root_alpha1 = n) ∧
    (∃ n : ℤ, 2 * weightDot root_alpha2 root_alpha1 / weightNormSq root_alpha2 = n) ∧
    (∃ n : ℤ, 2 * weightDot root_alpha2 root_alpha2 / weightNormSq root_alpha2 = n) :=
  ⟨⟨2, cartan_11⟩, cartan_12_is_integer, cartan_21_is_integer, ⟨2, cartan_22⟩⟩

/-- Weyl reflection of α₂ across α₁ gives α₃.

s_{α₁}(α₂) = α₂ - 2(α₂·α₁)/(α₁·α₁) α₁ = α₂ - 2(-1/2)/1 · α₁ = α₂ + α₁ = α₃

Calculation:
- weightDot root_alpha2 root_alpha1 = weightDot root_alpha1 root_alpha2 = -1/2
- weightNormSq root_alpha1 = 1
- So coefficient = 2 * (-1/2) / 1 = -1
- weylReflection = α₂ - (-1) • α₁ = α₂ + α₁ = α₃ -/
theorem weyl_reflection_alpha1_alpha2 :
    weylReflection root_alpha1 root_alpha2 = root_alpha3 := by
  simp only [weylReflection, weightDot_comm, root_dot_alpha1_alpha2, root_alpha1_norm_sq]
  -- Goal: root_alpha2 - 2 * (-1/2) / 1 • root_alpha1 = root_alpha3
  have h : (2 : ℝ) * (-1/2) / 1 = -1 := by ring
  rw [h, neg_one_smul, sub_neg_eq_add, WeightVector.add_comm']
  exact root_alpha3_eq_sum.symm

/-- Weyl reflection of α₁ across α₂ gives α₃.

s_{α₂}(α₁) = α₁ - 2(α₁·α₂)/(α₂·α₂) α₂ = α₁ - 2(-1/2)/1 · α₂ = α₁ + α₂ = α₃ -/
theorem weyl_reflection_alpha2_alpha1 :
    weylReflection root_alpha2 root_alpha1 = root_alpha3 := by
  simp only [weylReflection, root_dot_alpha1_alpha2, root_alpha2_norm_sq]
  -- Goal: root_alpha1 - 2 * (-1/2) / 1 • root_alpha2 = root_alpha3
  have h : (2 : ℝ) * (-1/2) / 1 = -1 := by ring
  rw [h, neg_one_smul, sub_neg_eq_add]
  exact root_alpha3_eq_sum.symm

/-- Weyl reflection of α₃ across α₁ gives α₂.

s_{α₁}(α₃) = α₃ - 2(α₃·α₁)/(α₁·α₁) α₁ = α₃ - 2(1/2)/1 · α₁ = α₃ - α₁

We need: α₃ - α₁ = α₂, i.e., (w_R - w_B) - (w_R - w_G) = w_G - w_B ✓ -/
theorem weyl_reflection_alpha1_alpha3 :
    weylReflection root_alpha1 root_alpha3 = root_alpha2 := by
  simp only [weylReflection, weightDot_comm, root_dot_alpha1_alpha3, root_alpha1_norm_sq]
  simp only [div_one]
  have h : (2 : ℝ) * (1/2) = 1 := by ring
  rw [h, one_smul]
  apply WeightVector.ext
  · simp only [WeightVector.sub_t3, root_alpha3_t3, root_alpha1_t3, root_alpha2_t3]
    ring
  · simp only [WeightVector.sub_t8, root_alpha3_t8, root_alpha1_t8, root_alpha2_t8]
    ring

/-- Weyl reflection of α₃ across α₂ gives α₁.

s_{α₂}(α₃) = α₃ - 2(α₃·α₂)/(α₂·α₂) α₂ = α₃ - 2(1/2)/1 · α₂ = α₃ - α₂ = α₁ -/
theorem weyl_reflection_alpha2_alpha3 :
    weylReflection root_alpha2 root_alpha3 = root_alpha1 := by
  simp only [weylReflection, weightDot_comm, root_dot_alpha2_alpha3, root_alpha2_norm_sq]
  simp only [div_one]
  have h : (2 : ℝ) * (1/2) = 1 := by ring
  rw [h, one_smul]
  apply WeightVector.ext
  · simp only [WeightVector.sub_t3, root_alpha3_t3, root_alpha2_t3, root_alpha1_t3]
    ring
  · simp only [WeightVector.sub_t8, root_alpha3_t8, root_alpha2_t8, root_alpha1_t8]
    ring

/-- Weyl reflection of any simple root across itself gives its negative.

s_α(α) = α - 2(α·α)/(α·α) α = α - 2α = -α -/
theorem weyl_reflection_self (α : WeightVector) (hα : weightNormSq α ≠ 0) :
    weylReflection α α = -α := by
  unfold weylReflection
  rw [← weightNormSq_eq_dot_self]
  -- Goal: α - (2 * weightNormSq α / weightNormSq α) • α = -α
  have h : (2 : ℝ) * weightNormSq α / weightNormSq α = 2 := by
    rw [mul_div_assoc, div_self hα, mul_one]
  rw [h, two_smul]
  -- Goal: α - (α + α) = -α
  apply WeightVector.ext
  · simp only [WeightVector.sub_t3, WeightVector.add_t3, WeightVector.neg_t3]; ring
  · simp only [WeightVector.sub_t8, WeightVector.add_t8, WeightVector.neg_t8]; ring

/-- The Weyl group action on roots stays in the root system.

For the A₂ root system, reflecting any root across any simple root gives another root.
This is the reflection closure property. -/
theorem weyl_reflection_closure_positive :
    (weylReflection root_alpha1 root_alpha2 ∈ su3_roots) ∧
    (weylReflection root_alpha2 root_alpha1 ∈ su3_roots) ∧
    (weylReflection root_alpha1 root_alpha3 ∈ su3_roots) ∧
    (weylReflection root_alpha2 root_alpha3 ∈ su3_roots) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [weyl_reflection_alpha1_alpha2]
    -- root_alpha3 ∈ [α₁, α₂, α₃, -α₁, -α₂, -α₃]
    simp only [su3_roots, List.mem_cons]
    right; right; left; trivial
  · rw [weyl_reflection_alpha2_alpha1]
    simp only [su3_roots, List.mem_cons]
    right; right; left; trivial
  · rw [weyl_reflection_alpha1_alpha3]
    -- root_alpha2 ∈ su3_roots
    simp only [su3_roots, List.mem_cons]
    right; left; trivial
  · rw [weyl_reflection_alpha2_alpha3]
    -- root_alpha1 ∈ su3_roots
    simp only [su3_roots, List.mem_cons]
    left; trivial

/-! ## Connection to Gell-Mann Matrices

The weight vectors are eigenvalues of the diagonal Gell-Mann matrices T₃ and T₈
acting on the fundamental representation states |R⟩, |G⟩, |B⟩.

**Eigenvalue equations (in Dirac notation):**
- T₃|R⟩ = (1/2)|R⟩,   T₈|R⟩ = (1/(2√3))|R⟩
- T₃|G⟩ = (-1/2)|G⟩,  T₈|G⟩ = (1/(2√3))|G⟩
- T₃|B⟩ = 0,          T₈|B⟩ = (-1/√3)|B⟩

**Matrix form:**
T₃ = (1/2)diag(1, -1, 0) = λ₃/2
T₈ = (1/(2√3))diag(1, 1, -2) = λ₈/2

The weight w_c = (T₃ eigenvalue, T₈ eigenvalue) for color c ∈ {R, G, B}.

Note: Full eigenvalue proofs require importing and working with the Gell-Mann
matrix definitions from SU3.lean. Here we verify consistency of our weight
definitions with the expected diagonal entries.
-/

/-- The T₃ eigenvalue for Red matches w_R.t3 -/
theorem t3_eigenvalue_R : w_R.t3 = 1/2 := by simp [w_R]

/-- The T₃ eigenvalue for Green matches w_G.t3 -/
theorem t3_eigenvalue_G : w_G.t3 = -1/2 := by simp [w_G]

/-- The T₃ eigenvalue for Blue matches w_B.t3 -/
theorem t3_eigenvalue_B : w_B.t3 = 0 := by simp [w_B]

/-- The T₈ eigenvalue for Red matches w_R.t8 -/
theorem t8_eigenvalue_R : w_R.t8 = 1/(2 * Real.sqrt 3) := by simp [w_R]

/-- The T₈ eigenvalue for Green matches w_G.t8 -/
theorem t8_eigenvalue_G : w_G.t8 = 1/(2 * Real.sqrt 3) := by simp [w_G]

/-- The T₈ eigenvalue for Blue matches w_B.t8 -/
theorem t8_eigenvalue_B : w_B.t8 = -1/Real.sqrt 3 := by simp [w_B]

/-- Red and Green have the same T₈ eigenvalue (form an isospin doublet) -/
theorem t8_R_eq_G : w_R.t8 = w_G.t8 := by simp [w_R, w_G]

/-- T₃ eigenvalues sum to zero (traceless) -/
theorem t3_eigenvalue_sum : w_R.t3 + w_G.t3 + w_B.t3 = 0 := fundamental_t3_sum_zero

/-- T₈ eigenvalues sum to zero (traceless) -/
theorem t8_eigenvalue_sum : w_R.t8 + w_G.t8 + w_B.t8 = 0 := fundamental_t8_sum_zero

/-- The diagonal of λ₃/2 gives T₃ eigenvalues.

λ₃ = diag(1, -1, 0), so λ₃/2 = diag(1/2, -1/2, 0)
The eigenvalues are w_R.t3, w_G.t3, w_B.t3. -/
theorem gellmann_lambda3_diagonal :
    (w_R.t3, w_G.t3, w_B.t3) = (1/2, -1/2, 0) := by
  simp only [t3_eigenvalue_R, t3_eigenvalue_G, t3_eigenvalue_B]

/-- The diagonal of λ₈/2 gives T₈ eigenvalues.

λ₈ = (1/√3)diag(1, 1, -2), so λ₈/2 = diag(1/(2√3), 1/(2√3), -1/√3)
The eigenvalues are w_R.t8, w_G.t8, w_B.t8. -/
theorem gellmann_lambda8_diagonal :
    (w_R.t8, w_G.t8, w_B.t8) = (1/(2 * Real.sqrt 3), 1/(2 * Real.sqrt 3), -1/Real.sqrt 3) := by
  simp only [t8_eigenvalue_R, t8_eigenvalue_G, t8_eigenvalue_B]

/-- Weight-root relation: root α₁ = w_R - w_G corresponds to the off-diagonal
generator that raises Green to Red (or lowers Red to Green).

This confirms that root vectors correspond to the action of raising/lowering
operators in the Lie algebra. -/
theorem root_alpha1_weight_diff : root_alpha1 = w_R - w_G := rfl

/-- Weight-root relation: root α₂ = w_G - w_B -/
theorem root_alpha2_weight_diff : root_alpha2 = w_G - w_B := rfl

/-- Weight-root relation: root α₃ = w_R - w_B -/
theorem root_alpha3_weight_diff : root_alpha3 = w_R - w_B := rfl

end ChiralGeometrogenesis.PureMath.LieAlgebra
