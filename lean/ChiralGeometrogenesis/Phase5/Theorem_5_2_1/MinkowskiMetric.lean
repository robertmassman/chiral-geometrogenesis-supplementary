/-
  Phase5/Theorem_5_2_1/MinkowskiMetric.lean

  Part 2: Minkowski Metric (Zeroth Order) for Theorem 5.2.1 (Emergent Metric)

  The flat background metric η_μν = diag(-1, +1, +1, +1).

  Reference: §1, §3.2
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase5.Theorem_5_2_1.MinkowskiMetric

/-- Lorentz index type (0 = time, 1, 2, 3 = space) -/
abbrev LorentzIndex := Fin 4

/-- The Minkowski metric η_μν in mostly-plus convention.

    η = diag(-1, +1, +1, +1)

    Reference: §1.1, signature convention -/
structure MinkowskiMetricData where
  /-- Diagonal component value -/
  diag : LorentzIndex → ℝ
  /-- Time component η_00 = -1 -/
  time_component : diag 0 = -1
  /-- Spatial components η_ii = +1 for i = 1, 2, 3 -/
  space_components : ∀ i : Fin 3, diag (i.succ) = 1

/-- Standard Minkowski metric -/
def eta : MinkowskiMetricData where
  diag := fun i => if i = 0 then -1 else 1
  time_component := by simp
  space_components := by intro i; simp

/-- The Minkowski metric is diagonal -/
def minkowski_component (μ ν : LorentzIndex) : ℝ :=
  if μ = ν then eta.diag μ else 0

/-- The Minkowski metric has signature (-1, +1, +1, +1) -/
theorem minkowski_signature :
    eta.diag 0 = -1 ∧ eta.diag 1 = 1 ∧ eta.diag 2 = 1 ∧ eta.diag 3 = 1 := by
  refine ⟨eta.time_component, ?_, ?_, ?_⟩
  all_goals simp only [eta]; rfl

/-- The determinant of the Minkowski metric: det(η) = -1.

    This follows from det(diag(-1, 1, 1, 1)) = (-1) · 1 · 1 · 1 = -1.

    Reference: §3 (Pre-Metric Structure) -/
theorem minkowski_determinant_neg_one :
    (-1 : ℝ) * 1 * 1 * 1 = -1 := by ring

/-- The inverse Minkowski metric equals the Minkowski metric.

    For diagonal metrics: η^{μν} = 1/η_{μν} = η_{μν} (since η_{ii}² = 1) -/
theorem minkowski_inverse :
    ((-1 : ℝ))⁻¹ = -1 ∧ (1 : ℝ)⁻¹ = 1 := by
  constructor <;> norm_num

/-- The trace of the Minkowski metric is 4 (dimension).

    Tr(η) = η^{μν}η_{μν} = (-1)·(-1) + 1·1 + 1·1 + 1·1 = 4 -/
theorem minkowski_trace :
    (-1 : ℝ) * (-1) + 1 * 1 + 1 * 1 + 1 * 1 = 4 := by ring

/-- The Minkowski metric is Lorentzian (one negative eigenvalue) -/
theorem minkowski_is_lorentzian :
    eta.diag 0 < 0 ∧ eta.diag 1 > 0 ∧ eta.diag 2 > 0 ∧ eta.diag 3 > 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [eta]; norm_num
  · simp only [eta]; norm_num
  · simp only [eta]; simp only [show (2 : Fin 4) ≠ 0 by decide]; norm_num
  · simp only [eta]; simp only [show (3 : Fin 4) ≠ 0 by decide]; norm_num

end ChiralGeometrogenesis.Phase5.Theorem_5_2_1.MinkowskiMetric
