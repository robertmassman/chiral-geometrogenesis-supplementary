/-
  ChiralGeometrogenesis/Tactics/TrigSimplify.lean

  Trigonometric simplification tactics and lemmas.

  This module provides automation for trigonometric proofs, especially those
  involving the 120° phase separations central to SU(3) and Kuramoto dynamics.

  ## Key Features

  1. **Sum formulas for 120° separation** (NOVEL - not in Mathlib):
     - sin(θ) + sin(θ + 2π/3) + sin(θ + 4π/3) = 0
     - cos(θ) + cos(θ + 2π/3) + cos(θ + 4π/3) = 0

  2. **Special values at 2π/3 and 4π/3** (NOVEL - not directly in Mathlib):
     - sin(2π/3) = √3/2, cos(2π/3) = -1/2
     - sin(4π/3) = -√3/2, cos(4π/3) = -1/2

  3. **Product-to-sum formulas** (Standard identities, derived from Mathlib primitives)

  4. **Extended periodicity lemmas** (Extensions of Mathlib's periodicity)

  5. **The `trig_simp` macro** for batch simplification

  6. **Trefoil-specific lemmas** for the knot injectivity proof

  ## Mathematical Background

  The 120° phase separation appears because SU(3) has three fundamental
  representation weights arranged in an equilateral triangle. In the
  Sakaguchi-Kuramoto model, the coupling at equilibrium vanishes precisely
  when phases differ by 2π/3.

  ## Mathlib Dependencies

  This module relies on the following Mathlib results:
  - `sin_add`, `cos_add`: Addition formulas (Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic)
  - `sin_pi_div_three`, `cos_pi_div_three`: Values at π/3
  - `sin_add_pi`, `cos_add_pi`: Addition of π
  - `sin_pi_sub`, `cos_pi_sub`: Subtraction from π
  - `sin_two_mul`, `cos_two_mul`: Double angle formulas
  - `sin_three_mul`, `cos_three_mul`: Triple angle formulas
  - `sin_eq_sin_iff`: Characterization of sin equality (from Complex module)
-/

import ChiralGeometrogenesis.Tactics.Basic
-- Note: sin_eq_sin_iff comes transitively through Mathlib.Tactic
-- which imports Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Tactics

open Real

/-! ## Sum-to-Product Identities

These lemmas express sums of sines/cosines at equally spaced angles.
The key insight is that the three cube roots of unity sum to zero:
  1 + e^{i·2π/3} + e^{i·4π/3} = 0
-/

/-- **120° Sum Identity for Sine**

sin(θ) + sin(θ + 2π/3) + sin(θ + 4π/3) = 0

Proof: Use sin(a+b) = sin(a)cos(b) + cos(a)sin(b) and the facts that
- cos(2π/3) = cos(4π/3) = -1/2
- sin(2π/3) = √3/2, sin(4π/3) = -√3/2
-/
theorem sum_sin_120 (θ : ℝ) :
    sin θ + sin (θ + 2 * π / 3) + sin (θ + 4 * π / 3) = 0 := by
  -- Expand using sin(a + b) = sin a * cos b + cos a * sin b
  rw [sin_add, sin_add]
  -- Values at 2π/3 and 4π/3
  have h_cos_2pi3 : cos (2 * π / 3) = -1/2 := by
    rw [show (2 : ℝ) * π / 3 = π - π / 3 by ring]
    rw [cos_pi_sub]
    rw [cos_pi_div_three]
    norm_num
  have h_sin_2pi3 : sin (2 * π / 3) = sqrt 3 / 2 := by
    rw [show (2 : ℝ) * π / 3 = π - π / 3 by ring]
    rw [sin_pi_sub]
    rw [sin_pi_div_three]
  have h_cos_4pi3 : cos (4 * π / 3) = -1/2 := by
    rw [show (4 : ℝ) * π / 3 = π / 3 + π by ring]
    rw [cos_add_pi]
    rw [cos_pi_div_three]
    norm_num
  have h_sin_4pi3 : sin (4 * π / 3) = -sqrt 3 / 2 := by
    rw [show (4 : ℝ) * π / 3 = π / 3 + π by ring]
    rw [sin_add_pi]
    rw [sin_pi_div_three]
    ring
  -- Substitute and simplify
  rw [h_cos_2pi3, h_sin_2pi3, h_cos_4pi3, h_sin_4pi3]
  ring

/-- **120° Sum Identity for Cosine**

cos(θ) + cos(θ + 2π/3) + cos(θ + 4π/3) = 0
-/
theorem sum_cos_120 (θ : ℝ) :
    cos θ + cos (θ + 2 * π / 3) + cos (θ + 4 * π / 3) = 0 := by
  -- Expand using cos(a + b) = cos a * cos b - sin a * sin b
  rw [cos_add, cos_add]
  -- Values at 2π/3 and 4π/3
  have h_cos_2pi3 : cos (2 * π / 3) = -1/2 := by
    rw [show (2 : ℝ) * π / 3 = π - π / 3 by ring]
    rw [cos_pi_sub]
    rw [cos_pi_div_three]
    norm_num
  have h_sin_2pi3 : sin (2 * π / 3) = sqrt 3 / 2 := by
    rw [show (2 : ℝ) * π / 3 = π - π / 3 by ring]
    rw [sin_pi_sub]
    rw [sin_pi_div_three]
  have h_cos_4pi3 : cos (4 * π / 3) = -1/2 := by
    rw [show (4 : ℝ) * π / 3 = π / 3 + π by ring]
    rw [cos_add_pi]
    rw [cos_pi_div_three]
    norm_num
  have h_sin_4pi3 : sin (4 * π / 3) = -sqrt 3 / 2 := by
    rw [show (4 : ℝ) * π / 3 = π / 3 + π by ring]
    rw [sin_add_pi]
    rw [sin_pi_div_three]
    ring
  -- Substitute and simplify
  rw [h_cos_2pi3, h_sin_2pi3, h_cos_4pi3, h_sin_4pi3]
  ring

/-- Generalized 120° sum for sine with arbitrary base and offset -/
theorem sum_sin_120_general (θ φ : ℝ) :
    sin (θ + φ) + sin (θ + φ + 2 * π / 3) + sin (θ + φ + 4 * π / 3) = 0 :=
  sum_sin_120 (θ + φ)

/-- Generalized 120° sum for cosine with arbitrary base and offset -/
theorem sum_cos_120_general (θ φ : ℝ) :
    cos (θ + φ) + cos (θ + φ + 2 * π / 3) + cos (θ + φ + 4 * π / 3) = 0 :=
  sum_cos_120 (θ + φ)

/-! ## Double and Triple Angle Formulas

These reference the standard Mathlib lemmas. We provide aliases for
backward compatibility with existing code in this project.

**Mathlib References:**
- `Real.sin_two_mul`: sin(2θ) = 2·sin(θ)·cos(θ)
- `Real.cos_two_mul`: cos(2θ) = 2·cos²(θ) - 1
- `Real.sin_three_mul`: sin(3θ) = 3·sin(θ) - 4·sin³(θ)
- `Real.cos_three_mul`: cos(3θ) = 4·cos³(θ) - 3·cos(θ)
-/

/-- Double angle for sine (alias for Mathlib's `sin_two_mul`) -/
theorem sin_two_mul' (θ : ℝ) : sin (2 * θ) = 2 * sin θ * cos θ := sin_two_mul θ

/-- Double angle for cosine in terms of cos² (alias for Mathlib's `cos_two_mul`) -/
theorem cos_two_mul_cos_sq (θ : ℝ) : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := cos_two_mul θ

/-- Double angle for cosine in terms of sin².

This is a derived form: cos(2θ) = 1 - 2·sin²(θ).
Derived from `cos_two_mul` and `sin_sq_add_cos_sq`.
-/
theorem cos_two_mul_sin_sq (θ : ℝ) : cos (2 * θ) = 1 - 2 * sin θ ^ 2 := by
  have h1 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := cos_two_mul θ
  have h2 : sin θ ^ 2 + cos θ ^ 2 = 1 := sin_sq_add_cos_sq θ
  linarith

-- Note: sin_three_mul and cos_three_mul are available directly from Mathlib
-- as Real.sin_three_mul and Real.cos_three_mul. We re-export them for convenience.

/-- Triple angle for sine (re-export of Mathlib's `Real.sin_three_mul`).

sin(3θ) = 3·sin(θ) - 4·sin³(θ)
-/
theorem sin_three_mul' (θ : ℝ) : sin (3 * θ) = 3 * sin θ - 4 * sin θ ^ 3 :=
  Real.sin_three_mul θ

/-- Triple angle for cosine (re-export of Mathlib's `Real.cos_three_mul`).

cos(3θ) = 4·cos³(θ) - 3·cos(θ)
-/
theorem cos_three_mul' (θ : ℝ) : cos (3 * θ) = 4 * cos θ ^ 3 - 3 * cos θ :=
  Real.cos_three_mul θ

/-! ## Periodicity Lemmas

These extend Mathlib's periodicity lemmas to integer multiples.
-/

/-- sin(θ + 2πk) = sin(θ) for any integer k -/
theorem sin_add_two_pi_int (θ : ℝ) (k : ℤ) : sin (θ + 2 * π * k) = sin θ := by
  have h : sin (θ + k * (2 * π)) = sin θ := sin_add_int_mul_two_pi θ k
  convert h using 2
  ring

/-- cos(θ + 2πk) = cos(θ) for any integer k -/
theorem cos_add_two_pi_int (θ : ℝ) (k : ℤ) : cos (θ + 2 * π * k) = cos θ := by
  have h : cos (θ + k * (2 * π)) = cos θ := cos_add_int_mul_two_pi θ k
  convert h using 2
  ring

/-- sin(2πk) = 0 for any integer k -/
theorem sin_two_pi_int (k : ℤ) : sin (2 * π * k) = 0 := by
  have h := sin_add_two_pi_int 0 k
  simp only [zero_add, sin_zero] at h
  exact h

/-- cos(2πk) = 1 for any integer k -/
theorem cos_two_pi_int (k : ℤ) : cos (2 * π * k) = 1 := by
  have h := cos_add_two_pi_int 0 k
  simp only [zero_add, cos_zero] at h
  exact h

/-! ## Special Values at π/3, 2π/3, etc.

Convenient forms for the angles appearing in 120° calculations.

**Mathlib provides directly:**
- `sin_pi_div_three`: sin(π/3) = √3/2
- `cos_pi_div_three`: cos(π/3) = 1/2

**This module provides (derived from Mathlib):**
- `sin_two_pi_div_three`: sin(2π/3) = √3/2
- `cos_two_pi_div_three`: cos(2π/3) = -1/2
- `sin_four_pi_div_three`: sin(4π/3) = -√3/2
- `cos_four_pi_div_three`: cos(4π/3) = -1/2
-/

/-- sin(2π/3) = √3/2 -/
theorem sin_two_pi_div_three : sin (2 * π / 3) = sqrt 3 / 2 := by
  rw [show (2 : ℝ) * π / 3 = π - π / 3 by ring]
  rw [sin_pi_sub, sin_pi_div_three]

/-- cos(2π/3) = -1/2 -/
theorem cos_two_pi_div_three : cos (2 * π / 3) = -1 / 2 := by
  rw [show (2 : ℝ) * π / 3 = π - π / 3 by ring]
  rw [cos_pi_sub, cos_pi_div_three]
  norm_num

/-- sin(4π/3) = -√3/2 -/
theorem sin_four_pi_div_three : sin (4 * π / 3) = -sqrt 3 / 2 := by
  rw [show (4 : ℝ) * π / 3 = π / 3 + π by ring]
  rw [sin_add_pi, sin_pi_div_three]
  ring

/-- cos(4π/3) = -1/2 -/
theorem cos_four_pi_div_three : cos (4 * π / 3) = -1 / 2 := by
  rw [show (4 : ℝ) * π / 3 = π / 3 + π by ring]
  rw [cos_add_pi, cos_pi_div_three]
  norm_num

/-! ## Product-to-Sum Formulas

Useful for simplifying products of sines and cosines.
-/

/-- sin(α)·cos(β) = (1/2)(sin(α+β) + sin(α-β)) -/
theorem sin_mul_cos (α β : ℝ) : sin α * cos β = (sin (α + β) + sin (α - β)) / 2 := by
  rw [sin_add, sin_sub]
  ring

/-- cos(α)·sin(β) = (1/2)(sin(α+β) - sin(α-β)) -/
theorem cos_mul_sin (α β : ℝ) : cos α * sin β = (sin (α + β) - sin (α - β)) / 2 := by
  rw [sin_add, sin_sub]
  ring

/-- cos(α)·cos(β) = (1/2)(cos(α+β) + cos(α-β)) -/
theorem cos_mul_cos (α β : ℝ) : cos α * cos β = (cos (α + β) + cos (α - β)) / 2 := by
  rw [cos_add, cos_sub]
  ring

/-- sin(α)·sin(β) = (1/2)(cos(α-β) - cos(α+β)) -/
theorem sin_mul_sin (α β : ℝ) : sin α * sin β = (cos (α - β) - cos (α + β)) / 2 := by
  rw [cos_add, cos_sub]
  ring

/-! ## The `trig_simp` Macro

A convenience macro that applies common trigonometric simplifications.

The macro applies:
1. Double and triple angle formulas (from Mathlib)
2. Addition/subtraction formulas (from Mathlib)
3. Special values at π/3, 2π/3, 4π/3
4. Standard values at 0, π, 2π
5. Algebraic simplifications via `ring`
-/

/-- Collect all trig simplification lemmas (for documentation/reference) -/
theorem trig_simp_lemmas :
    (∀ θ : ℝ, sin θ + sin (θ + 2 * π / 3) + sin (θ + 4 * π / 3) = 0) ∧
    (∀ θ : ℝ, cos θ + cos (θ + 2 * π / 3) + cos (θ + 4 * π / 3) = 0) ∧
    (sin (2 * π / 3) = sqrt 3 / 2) ∧
    (cos (2 * π / 3) = -1 / 2) ∧
    (sin (4 * π / 3) = -sqrt 3 / 2) ∧
    (cos (4 * π / 3) = -1 / 2) :=
  ⟨sum_sin_120, sum_cos_120, sin_two_pi_div_three, cos_two_pi_div_three,
   sin_four_pi_div_three, cos_four_pi_div_three⟩

/-- The `trig_simp` tactic applies standard trigonometric simplifications.

Usage:
```lean
example (θ : ℝ) : sin θ + sin (θ + 2*π/3) + sin (θ + 4*π/3) = 0 := by trig_simp
```

Note: For 120° sum identities, use `trig_simp!` which tries `sum_sin_120` and `sum_cos_120` first.
-/
macro "trig_simp" : tactic =>
  `(tactic| (
    simp only [
      -- Double/triple angle formulas (from Mathlib, Real namespace)
      sin_two_mul', cos_two_mul, cos_two_mul_cos_sq, cos_two_mul_sin_sq,
      Real.sin_three_mul, Real.cos_three_mul,
      -- Addition formulas (from Mathlib)
      sin_add, cos_add, sin_sub, cos_sub,
      -- Special values (π/3 from Mathlib, 2π/3 and 4π/3 from this module)
      sin_pi_div_three, cos_pi_div_three,
      sin_two_pi_div_three, cos_two_pi_div_three,
      sin_four_pi_div_three, cos_four_pi_div_three,
      -- Standard values (from Mathlib)
      sin_zero, cos_zero, sin_pi, cos_pi,
      sin_two_pi, cos_two_pi,
      -- Algebraic simplifications
      mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul
    ]
    <;> try ring
    <;> try ring_nf
  ))

/-- Extended version that also tries the 120° sum identities first.

This is useful when the goal is exactly a 120° sum identity.
-/
macro "trig_simp!" : tactic =>
  `(tactic| (
    first
    | exact sum_sin_120 _
    | exact sum_cos_120 _
    | (simp only [
        sin_two_mul', cos_two_mul, cos_two_mul_cos_sq, cos_two_mul_sin_sq,
        Real.sin_three_mul, Real.cos_three_mul,
        sin_add, cos_add, sin_sub, cos_sub,
        sin_pi_div_three, cos_pi_div_three,
        sin_two_pi_div_three, cos_two_pi_div_three,
        sin_four_pi_div_three, cos_four_pi_div_three,
        sin_zero, cos_zero, sin_pi, cos_pi,
        sin_two_pi, cos_two_pi,
        mul_zero, zero_mul, add_zero, zero_add,
        mul_one, one_mul
      ]
      <;> try ring
      <;> try ring_nf)
  ))

/-! ## Trefoil-Specific Lemmas

These lemmas are tailored for the trefoil injectivity proof.

The trefoil knot is parametrized as:
- x(t) = sin(2πt) + 2·sin(4πt)
- y(t) = cos(2πt) - 2·cos(4πt)
- z(t) = -sin(6πt)

for t ∈ [0, 1). Proving injectivity requires analyzing when
(x(s), y(s), z(s)) = (x(t), y(t), z(t)) implies s = t.
-/

/-- **Trefoil x-coordinate factorization**

sin(2πt) + 2·sin(4πt) = sin(2πt)·(1 + 4·cos(2πt))

**Proof strategy:**
1. Use double angle: sin(4πt) = 2·sin(2πt)·cos(2πt)
2. Factor out sin(2πt)

This factorization is key: it shows x(t) = 0 when sin(2πt) = 0 OR 1 + 4·cos(2πt) = 0.
-/
theorem trefoil_x_factored (t : ℝ) :
    sin (2 * π * t) + 2 * sin (4 * π * t) = sin (2 * π * t) * (1 + 4 * cos (2 * π * t)) := by
  have h : sin (4 * π * t) = 2 * sin (2 * π * t) * cos (2 * π * t) := by
    rw [show (4 : ℝ) * π * t = 2 * (2 * π * t) by ring]
    exact sin_two_mul' (2 * π * t)
  rw [h]
  ring

/-- **Trefoil y-coordinate expansion**

cos(2πt) - 2·cos(4πt) = -4·cos²(2πt) + cos(2πt) + 2

**Proof strategy:**
1. Use double angle: cos(4πt) = 2·cos²(2πt) - 1
2. Expand and collect terms

Let α = cos(2πt). Then y = -4α² + α + 2, a quadratic in α.
-/
theorem trefoil_y_expanded (t : ℝ) :
    cos (2 * π * t) - 2 * cos (4 * π * t) = -4 * cos (2 * π * t) ^ 2 + cos (2 * π * t) + 2 := by
  have h : cos (4 * π * t) = 2 * cos (2 * π * t) ^ 2 - 1 := by
    rw [show (4 : ℝ) * π * t = 2 * (2 * π * t) by ring]
    exact cos_two_mul_cos_sq (2 * π * t)
  rw [h]
  ring

/-- **Z-constraint from sine equality**

If sin(6πs) = sin(6πt), then either:
1. 6πs = 6πt + 2πk for some integer k (same angle mod 2π), or
2. 6πs = π - 6πt + 2πk for some integer k (supplementary angle mod 2π)

**Proof:** Apply Mathlib's `sin_eq_sin_iff` which characterizes when sin(x) = sin(y):
  sin(x) = sin(y) ↔ ∃ k : ℤ, y = 2πk + x ∨ y = (2k+1)π - x

Then solve for x in terms of y.
-/
theorem trefoil_z_constraint {s t : ℝ} (h : sin (6 * π * s) = sin (6 * π * t)) :
    (∃ k : ℤ, 6 * π * s = 6 * π * t + 2 * π * k) ∨
    (∃ k : ℤ, 6 * π * s = π - 6 * π * t + 2 * π * k) := by
  -- sin_eq_sin_iff says: sin x = sin y ↔ ∃ k, y = 2πk + x ∨ y = (2k+1)π - x
  rw [sin_eq_sin_iff] at h
  rcases h with ⟨k, hk | hk⟩
  · -- Case: 6πt = 2πk + 6πs, so 6πs = 6πt - 2πk = 6πt + 2π(-k)
    left
    use -k
    simp only [Int.cast_neg]
    -- hk says 6πt = 2kπ + 6πs, so 6πs = 6πt - 2kπ
    linarith
  · -- Case: 6πt = (2k + 1)π - 6πs
    right
    use k
    -- hk says 6πt = (2k+1)π - 6πs, so 6πs = (2k+1)π - 6πt = π - 6πt + 2kπ
    linarith

end ChiralGeometrogenesis.Tactics
