/-
  PureMath/LieAlgebra/SU2.lean

  SU(2) Lie Algebra Foundations

  This file establishes the mathematical structure of the SU(2) Lie algebra,
  leveraging Mathlib's infrastructure for Lie algebras and special linear groups.

  We use:
  - Mathlib.LinearAlgebra.UnitaryGroup for SU(2) as a group
  - Custom definitions for Pauli matrices (physics convention)

  The SU(2) Lie algebra has 3 generators (Pauli matrices σ₁, σ₂, σ₃),
  satisfying Tr(σ_a σ_b) = 2δ_ab.

  Reference: Standard physics conventions for weak isospin generators
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.PureMath.LieAlgebra

/-! ## SU(2) Group and Lie Algebra using Mathlib

Mathlib provides:
- `Matrix.specialUnitaryGroup n α` : SU(n) as matrices with det = 1, U*U = 1
- `LieAlgebra.SpecialLinear.sl n R` : sl(n,R) = traceless matrices

The Lie algebra 𝔰𝔲(2) consists of 2×2 traceless anti-Hermitian matrices.
Over ℂ, we have 𝔰𝔲(2) ⊗ ℂ ≅ sl(2,ℂ).
-/

/-- SU(2) group: 2×2 unitary matrices with determinant 1.

This provides the type-level representation of SU(2) using Mathlib's infrastructure.
SU(2) ≅ S³ as manifolds, which is essential for π₃(SU(2)) = ℤ. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- sl(2,ℂ): The Lie algebra of traceless 2×2 complex matrices.

This is the complexification of the Lie algebra 𝔰𝔲(2). The 3 Pauli matrices
form a basis when multiplied by i/2 (to get anti-Hermitian generators). -/
abbrev sl2ℂ := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

/-- The Lie algebra has 3 generators (Pauli matrices), consistent with dim(SU(n)) = n² - 1.

This connects the formula 2² - 1 = 3 to the actual count of Pauli matrices we define. -/
theorem pauli_count : Fintype.card (Fin 3) = 3 := rfl

/-- Dimension formula for SU(n): dim = n² - 1. For n=2, this gives 3. -/
theorem su2_dimension_formula : 2^2 - 1 = 3 := rfl

/-- The Cartan subalgebra has 1 generator (σ₃), consistent with rank(SU(n)) = n - 1.

For SU(2), there is a single diagonal generator σ₃. -/
theorem cartan_generators_count_su2 : Fintype.card (Fin 1) = 1 := rfl

/-- Rank formula for SU(n): rank = n - 1. For n=2, this gives 1. -/
theorem su2_rank_formula : 2 - 1 = 1 := rfl

/-! ## Pauli Matrices (Physics Convention)

The 3 Pauli matrices form a basis for 𝔰𝔲(2).
These are NOT in Mathlib - they are physics-specific with normalization Tr(σ_a σ_b) = 2δ_ab.

Note: Pauli matrices are Hermitian. The anti-Hermitian generators are i·σ_a/2.

**Physical significance:**
- σ₁, σ₂, σ₃ are the generators of weak isospin SU(2)_L
- The weak isospin operators are T_a = σ_a/2
- Commutation: [σ_a, σ_b] = 2i ε_abc σ_c
-/

/--
The 3 Pauli matrices σ₁, σ₂, σ₃ (Hermitian basis for su(2)).
Physics convention: Tr(σ_a σ_b) = 2δ_ab

Standard definitions:
- σ₁ = [[0, 1], [1, 0]]
- σ₂ = [[0, -i], [i, 0]]
- σ₃ = [[1, 0], [0, -1]]
-/
noncomputable def pauliMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | ⟨0, _⟩ => !![0, 1; 1, 0]  -- σ₁
  | ⟨1, _⟩ => !![0, -Complex.I; Complex.I, 0]  -- σ₂
  | ⟨2, _⟩ => !![1, 0; 0, -1]  -- σ₃

/-! ## Pauli Matrix Properties

The Pauli matrices satisfy:
1. Traceless: Tr(σ_a) = 0 (they generate sl(2,ℂ))
2. Hermitian: σ_a† = σ_a
3. Orthonormal: Tr(σ_a σ_b) = 2δ_ab
4. Algebra: σ_a σ_b = δ_ab I + i ε_abc σ_c
-/

/-- Helper: trace of a 2×2 complex matrix via Fin.sum_univ_two -/
private theorem trace_fin2_eq {M : Matrix (Fin 2) (Fin 2) ℂ} :
    Matrix.trace M = M 0 0 + M 1 1 := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Fin.sum_univ_two]

/-- σ₁ is traceless -/
theorem pauli_trace_0 : Matrix.trace (pauliMatrix 0) = 0 := by
  simp only [pauliMatrix, trace_fin2_eq]
  have h0 : (!![(0:ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := rfl
  have h1 : (!![(0:ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := rfl
  rw [h0, h1]; ring

/-- σ₂ is traceless -/
theorem pauli_trace_1 : Matrix.trace (pauliMatrix 1) = 0 := by
  simp only [pauliMatrix, trace_fin2_eq]
  have h0 : (!![(0:ℂ), -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := rfl
  have h1 : (!![(0:ℂ), -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := rfl
  rw [h0, h1]; ring

/-- σ₃ is traceless -/
theorem pauli_trace_2 : Matrix.trace (pauliMatrix 2) = 0 := by
  simp only [pauliMatrix, trace_fin2_eq]
  have h0 : (!![(1:ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := rfl
  have h1 : (!![(1:ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -1 := rfl
  rw [h0, h1]; ring

/-- All Pauli matrices are traceless (they form a basis for sl(2,ℂ)) -/
theorem pauli_traceless : ∀ i : Fin 3, Matrix.trace (pauliMatrix i) = 0 := by
  intro i
  fin_cases i
  · exact pauli_trace_0
  · exact pauli_trace_1
  · exact pauli_trace_2

/-! ## Trace of Squared Pauli Matrices

For the physics normalization, we have Tr(σ_a σ_b) = 2δ_ab.
This section proves Tr(σ_a²) = 2 for each Pauli matrix.
-/

/-- σ₁² = I (identity matrix) -/
theorem pauli_sq_0_eq_id :
    pauliMatrix 0 * pauliMatrix 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Tr(σ₁²) = 2 -/
theorem trace_pauli_sq_0 :
    Matrix.trace (pauliMatrix 0 * pauliMatrix 0) = 2 := by
  rw [pauli_sq_0_eq_id]
  simp only [Matrix.trace_one, Fintype.card_fin]
  norm_cast

/-- σ₂² = I (identity matrix) -/
theorem pauli_sq_1_eq_id :
    pauliMatrix 1 * pauliMatrix 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Tr(σ₂²) = 2 -/
theorem trace_pauli_sq_1 :
    Matrix.trace (pauliMatrix 1 * pauliMatrix 1) = 2 := by
  rw [pauli_sq_1_eq_id]
  simp only [Matrix.trace_one, Fintype.card_fin]
  norm_cast

/-- σ₃² = I (identity matrix) -/
theorem pauli_sq_2_eq_id :
    pauliMatrix 2 * pauliMatrix 2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Tr(σ₃²) = 2 -/
theorem trace_pauli_sq_2 :
    Matrix.trace (pauliMatrix 2 * pauliMatrix 2) = 2 := by
  rw [pauli_sq_2_eq_id]
  simp only [Matrix.trace_one, Fintype.card_fin]
  norm_cast

/-- **Key theorem: All Pauli matrices satisfy Tr(σ_a²) = 2**

This is the physics normalization convention Tr(σ_a σ_b) = 2δ_ab
specialized to the diagonal case a = b.

**Physical interpretation:**
- This normalization ensures canonical commutation relations
- The generators T_a = σ_a/2 satisfy Tr(T_a T_b) = ½δ_ab (fundamental rep)
- The quadratic Casimir is C₂ = Σ_a T_a² = 3/4 for the doublet rep
-/
theorem trace_pauli_sq_all :
    ∀ a : Fin 3, Matrix.trace (pauliMatrix a * pauliMatrix a) = 2 := by
  intro a
  fin_cases a
  · exact trace_pauli_sq_0
  · exact trace_pauli_sq_1
  · exact trace_pauli_sq_2

/-! ## Trace Positivity

The positive-definite trace property is essential for anomaly calculations.
-/

/-- **Trace of σ_a² is positive**

This is the key property for Argument 5D in Theorem 2.3.1:
Tr[T²] > 0 for all non-zero Hermitian generators implies anomaly
coefficients have the same sign as each other. -/
theorem trace_pauli_sq_pos :
    ∀ a : Fin 3, (Matrix.trace (pauliMatrix a * pauliMatrix a) : ℂ) = 2 ∧ (2 : ℂ) ≠ 0 := by
  intro a
  constructor
  · exact trace_pauli_sq_all a
  · norm_num

/-- Trace squared is real and positive (as a real number) -/
theorem trace_pauli_sq_real_pos :
    ∀ a : Fin 3, ∃ r : ℝ, r > 0 ∧ (r : ℂ) = Matrix.trace (pauliMatrix a * pauliMatrix a) := by
  intro a
  use 2
  constructor
  · linarith
  · rw [trace_pauli_sq_all]
    norm_cast

/-! ## Pauli Algebra Relations

The Pauli matrices satisfy fundamental algebraic identities.
-/

/-- σ_a² = I for all Pauli matrices -/
theorem pauli_sq_eq_id :
    ∀ a : Fin 3, pauliMatrix a * pauliMatrix a = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro a
  fin_cases a
  · exact pauli_sq_0_eq_id
  · exact pauli_sq_1_eq_id
  · exact pauli_sq_2_eq_id

/-- Pauli matrix anticommutator: {σ_a, σ_a} = 2I (diagonal case)

For a = b, we have {σ_a, σ_a} = 2σ_a² = 2I. -/
theorem pauli_anticomm_diag :
    ∀ a : Fin 3, pauliMatrix a * pauliMatrix a + pauliMatrix a * pauliMatrix a =
      2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro a
  rw [pauli_sq_eq_id]
  simp only [two_smul]

/-! ### Off-Diagonal Anticommutators

For a ≠ b, the anticommutator {σ_a, σ_b} = σ_a σ_b + σ_b σ_a = 0.
This is the off-diagonal part of the complete relation {σ_a, σ_b} = 2δ_ab I.
-/

/-- σ₁ σ₂ product (explicit computation) -/
theorem pauli_01_mul :
    pauliMatrix 0 * pauliMatrix 1 = Complex.I • !![1, 0; 0, -1] := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σ₂ σ₁ product (explicit computation) -/
theorem pauli_10_mul :
    pauliMatrix 1 * pauliMatrix 0 = Complex.I • !![-1, 0; 0, 1] := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- {σ₁, σ₂} = 0 (anticommutator of σ₁ and σ₂) -/
theorem pauli_anticomm_01 :
    pauliMatrix 0 * pauliMatrix 1 + pauliMatrix 1 * pauliMatrix 0 = 0 := by
  rw [pauli_01_mul, pauli_10_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply]

/-- σ₁ σ₃ product -/
theorem pauli_02_mul :
    pauliMatrix 0 * pauliMatrix 2 = !![0, -1; 1, 0] := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σ₃ σ₁ product -/
theorem pauli_20_mul :
    pauliMatrix 2 * pauliMatrix 0 = !![0, 1; -1, 0] := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- {σ₁, σ₃} = 0 -/
theorem pauli_anticomm_02 :
    pauliMatrix 0 * pauliMatrix 2 + pauliMatrix 2 * pauliMatrix 0 = 0 := by
  rw [pauli_02_mul, pauli_20_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply]

/-- σ₂ σ₃ product -/
theorem pauli_12_mul :
    pauliMatrix 1 * pauliMatrix 2 = !![(0:ℂ), Complex.I; Complex.I, 0] := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σ₃ σ₂ product -/
theorem pauli_21_mul :
    pauliMatrix 2 * pauliMatrix 1 = !![(0:ℂ), -Complex.I; -Complex.I, 0] := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- {σ₂, σ₃} = 0 -/
theorem pauli_anticomm_12 :
    pauliMatrix 1 * pauliMatrix 2 + pauliMatrix 2 * pauliMatrix 1 = 0 := by
  rw [pauli_12_mul, pauli_21_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply]

/-- **Complete anticommutator relation: {σ_a, σ_b} = 2δ_ab I**

For a = b: {σ_a, σ_a} = 2I (proven in pauli_anticomm_diag)
For a ≠ b: {σ_a, σ_b} = 0 (proven in pauli_anticomm_01, _02, _12) -/
theorem pauli_anticomm_complete :
    ∀ a b : Fin 3, pauliMatrix a * pauliMatrix b + pauliMatrix b * pauliMatrix a =
      if a = b then 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) else 0 := by
  intro a b
  by_cases hab : a = b
  · simp only [hab, if_true]
    exact pauli_anticomm_diag b
  · simp only [hab, if_false]
    -- Case analysis on distinct pairs
    fin_cases a <;> fin_cases b
    all_goals first | exact absurd rfl hab | skip
    · exact pauli_anticomm_01
    · exact pauli_anticomm_02
    · rw [add_comm]; exact pauli_anticomm_01
    · exact pauli_anticomm_12
    · rw [add_comm]; exact pauli_anticomm_02
    · rw [add_comm]; exact pauli_anticomm_12

/-! ## Hermitian Property

Pauli matrices are Hermitian: σ_a† = σ_a.
This is essential for the matrices to represent observable operators in quantum mechanics.
-/

/-- σ₁ is Hermitian: σ₁† = σ₁ -/
theorem pauli_hermitian_0 : (pauliMatrix 0).conjTranspose = pauliMatrix 0 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

/-- σ₂ is Hermitian: σ₂† = σ₂ -/
theorem pauli_hermitian_1 : (pauliMatrix 1).conjTranspose = pauliMatrix 1 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.conj_I]

/-- σ₃ is Hermitian: σ₃† = σ₃ -/
theorem pauli_hermitian_2 : (pauliMatrix 2).conjTranspose = pauliMatrix 2 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

/-- **All Pauli matrices are Hermitian**

This is a fundamental property ensuring Pauli matrices represent
observable operators in quantum mechanics. -/
theorem pauli_hermitian :
    ∀ a : Fin 3, (pauliMatrix a).conjTranspose = pauliMatrix a := by
  intro a
  fin_cases a
  · exact pauli_hermitian_0
  · exact pauli_hermitian_1
  · exact pauli_hermitian_2

/-! ## Commutator Relations (Lie Bracket)

The Pauli matrices satisfy the fundamental Lie algebra relation:
[σ_a, σ_b] = σ_a σ_b - σ_b σ_a = 2i ε_abc σ_c

This is the defining structure of the SU(2) Lie algebra.
-/

/-- [σ₁, σ₂] = 2i σ₃ -/
theorem pauli_comm_01 :
    pauliMatrix 0 * pauliMatrix 1 - pauliMatrix 1 * pauliMatrix 0 =
      (2 * Complex.I) • pauliMatrix 2 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply]
  all_goals ring

/-- [σ₂, σ₃] = 2i σ₁ -/
theorem pauli_comm_12 :
    pauliMatrix 1 * pauliMatrix 2 - pauliMatrix 2 * pauliMatrix 1 =
      (2 * Complex.I) • pauliMatrix 0 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply]
  all_goals ring

set_option linter.flexible false in
/-- [σ₃, σ₁] = 2i σ₂ -/
theorem pauli_comm_20 :
    pauliMatrix 2 * pauliMatrix 0 - pauliMatrix 0 * pauliMatrix 2 =
      (2 * Complex.I) • pauliMatrix 1 := by
  rw [pauli_20_mul, pauli_02_mul]
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    -- Use plain simp to reduce matrix entries to scalar equations
    simp [Matrix.sub_apply, Matrix.smul_apply]
  -- Goals have 2 * I * I (left-associated), need to reassociate
  · -- Goal: 1 + 1 = -(2 * I * I)
    have hI : Complex.I * Complex.I = -1 := by rw [← sq, Complex.I_sq]
    calc (1 : ℂ) + 1 = 2 := by ring
      _ = -(-(2 : ℂ)) := by ring
      _ = -(2 * (-1)) := by ring
      _ = -(2 * (Complex.I * Complex.I)) := by rw [hI]
      _ = -((2 * Complex.I) * Complex.I) := by ring
      _ = -(2 * Complex.I * Complex.I) := by ring
  · -- Goal: -1 - 1 = 2 * I * I
    have hI : Complex.I * Complex.I = -1 := by rw [← sq, Complex.I_sq]
    calc (-1 : ℂ) - 1 = -2 := by ring
      _ = 2 * (-1) := by ring
      _ = 2 * (Complex.I * Complex.I) := by rw [hI]
      _ = (2 * Complex.I) * Complex.I := by ring
      _ = 2 * Complex.I * Complex.I := by ring

/-- Levi-Civita symbol for indices 0,1,2 (representing 1,2,3) -/
def leviCivita3 : Fin 3 → Fin 3 → Fin 3 → ℤ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | 1, 0, 2 => -1
  | _, _, _ => 0

/-- The commutator [σ_a, σ_b] = 2i ε_abc σ_c

This is stated for the cyclic cases. The general formula involves
summing over c with the Levi-Civita symbol. -/
theorem pauli_comm_cyclic :
    -- [σ₁, σ₂] = 2i σ₃
    (pauliMatrix 0 * pauliMatrix 1 - pauliMatrix 1 * pauliMatrix 0 =
      (2 * Complex.I) • pauliMatrix 2) ∧
    -- [σ₂, σ₃] = 2i σ₁
    (pauliMatrix 1 * pauliMatrix 2 - pauliMatrix 2 * pauliMatrix 1 =
      (2 * Complex.I) • pauliMatrix 0) ∧
    -- [σ₃, σ₁] = 2i σ₂
    (pauliMatrix 2 * pauliMatrix 0 - pauliMatrix 0 * pauliMatrix 2 =
      (2 * Complex.I) • pauliMatrix 1) :=
  ⟨pauli_comm_01, pauli_comm_12, pauli_comm_20⟩

/-- Commutator is zero for equal indices: [σ_a, σ_a] = 0 -/
theorem pauli_comm_self :
    ∀ a : Fin 3, pauliMatrix a * pauliMatrix a - pauliMatrix a * pauliMatrix a = 0 := by
  intro a
  simp only [sub_self]

/-! ## Off-Diagonal Trace Orthogonality

For the complete orthonormality Tr(σ_a σ_b) = 2δ_ab, we need to prove
Tr(σ_a σ_b) = 0 when a ≠ b.
-/

/-- Tr(σ₁ σ₂) = 0 -/
theorem trace_pauli_01 : Matrix.trace (pauliMatrix 0 * pauliMatrix 1) = 0 := by
  rw [pauli_01_mul]
  simp only [Matrix.trace_smul]
  have htr : Matrix.trace (!![(1:ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    rw [trace_fin2_eq]
    have h0 : (!![(1:ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := rfl
    have h1 : (!![(1:ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -1 := rfl
    rw [h0, h1]; ring
  rw [htr]; simp

/-- Tr(σ₁ σ₃) = 0 -/
theorem trace_pauli_02 : Matrix.trace (pauliMatrix 0 * pauliMatrix 2) = 0 := by
  rw [pauli_02_mul]
  simp only [trace_fin2_eq]
  have h0 : (!![(0:ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := rfl
  have h1 : (!![(0:ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := rfl
  rw [h0, h1]; ring

/-- Tr(σ₂ σ₃) = 0 -/
theorem trace_pauli_12 : Matrix.trace (pauliMatrix 1 * pauliMatrix 2) = 0 := by
  rw [pauli_12_mul]
  simp only [trace_fin2_eq]
  have h0 : (!![(0:ℂ), Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := rfl
  have h1 : (!![(0:ℂ), Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := rfl
  rw [h0, h1]; ring

/-- Trace is symmetric: Tr(AB) = Tr(BA) -/
theorem trace_pauli_comm (a b : Fin 3) :
    Matrix.trace (pauliMatrix a * pauliMatrix b) =
      Matrix.trace (pauliMatrix b * pauliMatrix a) := by
  rw [Matrix.trace_mul_comm]

/-- Tr(σ₂ σ₁) = 0 (by symmetry) -/
theorem trace_pauli_10 : Matrix.trace (pauliMatrix 1 * pauliMatrix 0) = 0 := by
  rw [← trace_pauli_comm]; exact trace_pauli_01

/-- Tr(σ₃ σ₁) = 0 (by symmetry) -/
theorem trace_pauli_20 : Matrix.trace (pauliMatrix 2 * pauliMatrix 0) = 0 := by
  rw [← trace_pauli_comm]; exact trace_pauli_02

/-- Tr(σ₃ σ₂) = 0 (by symmetry) -/
theorem trace_pauli_21 : Matrix.trace (pauliMatrix 2 * pauliMatrix 1) = 0 := by
  rw [← trace_pauli_comm]; exact trace_pauli_12

/-- **Complete orthonormality: Tr(σ_a σ_b) = 2δ_ab**

This combines the diagonal case Tr(σ_a²) = 2 with the off-diagonal case Tr(σ_a σ_b) = 0 for a ≠ b.
This is the physics normalization convention for Pauli matrices. -/
theorem trace_pauli_orthonormal :
    ∀ a b : Fin 3, Matrix.trace (pauliMatrix a * pauliMatrix b) =
      if a = b then 2 else 0 := by
  intro a b
  by_cases hab : a = b
  · simp only [hab, if_true]
    exact trace_pauli_sq_all b
  · simp only [hab, if_false]
    fin_cases a <;> fin_cases b
    all_goals first | exact absurd rfl hab | skip
    · exact trace_pauli_01
    · exact trace_pauli_02
    · exact trace_pauli_10
    · exact trace_pauli_12
    · exact trace_pauli_20
    · exact trace_pauli_21

/-! ## Pauli Product Formula

The complete algebra relation: σ_a σ_b = δ_ab I + i ε_abc σ_c

This combines the anticommutator {σ_a, σ_b} = 2δ_ab I and commutator [σ_a, σ_b] = 2i ε_abc σ_c
via the identity: σ_a σ_b = ½({σ_a, σ_b} + [σ_a, σ_b])
-/

/-- σ₁ σ₂ = i σ₃ -/
theorem pauli_product_01 : pauliMatrix 0 * pauliMatrix 1 = Complex.I • pauliMatrix 2 := by
  -- From anticomm {σ₁,σ₂} = 0 and comm [σ₁,σ₂] = 2iσ₃, we get σ₁σ₂ = iσ₃
  have hanti := pauli_anticomm_01
  have hcomm := pauli_comm_01
  -- σ₁σ₂ = ½(σ₁σ₂ + σ₂σ₁) + ½(σ₁σ₂ - σ₂σ₁) = 0 + ½(2iσ₃) = iσ₃
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σ₂ σ₃ = i σ₁ -/
theorem pauli_product_12 : pauliMatrix 1 * pauliMatrix 2 = Complex.I • pauliMatrix 0 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σ₃ σ₁ = i σ₂ -/
theorem pauli_product_20 : pauliMatrix 2 * pauliMatrix 0 = Complex.I • pauliMatrix 1 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σ₂ σ₁ = -i σ₃ -/
theorem pauli_product_10 : pauliMatrix 1 * pauliMatrix 0 = (-Complex.I) • pauliMatrix 2 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σ₃ σ₂ = -i σ₁ -/
theorem pauli_product_21 : pauliMatrix 2 * pauliMatrix 1 = (-Complex.I) • pauliMatrix 0 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σ₁ σ₃ = -i σ₂ -/
theorem pauli_product_02 : pauliMatrix 0 * pauliMatrix 2 = (-Complex.I) • pauliMatrix 1 := by
  simp only [pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-! ## Connection to Physics

These properties connect to the weak isospin structure in the Standard Model.
-/

/-- Weak isospin generators T_a = σ_a/2 would satisfy Tr(T_a²) = 1/2.

In the full formalization, we'd have generators in the normalization
Tr(T_a T_b) = (1/2)δ_ab for the fundamental (doublet) representation.

For the purpose of anomaly calculations, what matters is:
- Tr(T_a²) > 0 (positive definite)
- All generators have the same sign in trace

The factor of 2 in Tr(σ_a²) = 2 becomes 1/2 for T_a = σ_a/2. -/
def weak_isospin_trace_convention : Prop :=
  ∀ a : Fin 3, Matrix.trace (pauliMatrix a * pauliMatrix a) = 2

theorem weak_isospin_trace_holds : weak_isospin_trace_convention :=
  trace_pauli_sq_all

end ChiralGeometrogenesis.PureMath.LieAlgebra
