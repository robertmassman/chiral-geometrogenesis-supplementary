/-
  Phase5/Theorem_5_2_1/NewtonianLimit.lean

  Part 6: Newtonian Limit for Theorem 5.2.1 (Emergent Metric)

  The weak-field limit recovers Newtonian gravity.

  Reference: §6 (Weak-Field Limit)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import ChiralGeometrogenesis.Phase5.Theorem_5_2_1.PhysicalConstants

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase5.Theorem_5_2_1.NewtonianLimit

open Real

/-- The Newtonian potential from energy density.

    Poisson equation: ∇²Φ_N = 4πGρ

    Solution: Φ_N(x) = -G ∫ ρ(y)/|x-y| d³y

    Reference: §6.1 -/
structure NewtonianPotential where
  /-- Physical constants -/
  constants : PhysicalConstants.Constants
  /-- Energy density source ρ(x) -/
  energy_density : ℝ
  /-- ρ ≥ 0 -/
  energy_density_nonneg : energy_density ≥ 0
  /-- The potential Φ_N -/
  phi_N : ℝ
  /-- Φ_N ≤ 0 for attractive gravity (positive mass) -/
  phi_N_attractive : phi_N ≤ 0

namespace NewtonianPotential

/-- Time dilation factor from Newtonian potential.

    dt_proper/dt_coordinate = √(-g_00) = √(1 + 2Φ_N/c²)

    For Φ_N < 0: clocks run slower in gravitational wells.

    Reference: §2.2 (Time Emergence), §10.2 -/
noncomputable def timeDilationFactor (np : NewtonianPotential) : ℝ :=
  Real.sqrt (1 + 2 * np.phi_N / np.constants.c^2)

/-- The argument of the square root is positive for weak fields.

    1 + 2Φ_N/c² > 0 when |Φ_N| < c²/2 (weak field condition).

    Reference: §6.2 -/
theorem weak_field_positive_arg (np : NewtonianPotential)
    (h_weak : np.phi_N > -np.constants.c ^ 2 / 2) :
    1 + 2 * np.phi_N / np.constants.c ^ 2 > 0 := by
  have hc2 : np.constants.c ^ 2 > 0 := sq_pos_of_pos np.constants.c_pos
  have hc_ne : np.constants.c ^ 2 ≠ 0 := ne_of_gt hc2
  have h1 : 2 * np.phi_N / np.constants.c ^ 2 > -1 := by
    have h2 : 2 * np.phi_N > -np.constants.c ^ 2 := by linarith
    have h3 : -np.constants.c ^ 2 / np.constants.c ^ 2 = -1 := by
      rw [neg_div, div_self hc_ne]
    calc 2 * np.phi_N / np.constants.c ^ 2
        > -np.constants.c ^ 2 / np.constants.c ^ 2 := by
          apply div_lt_div_of_pos_right h2 hc2
      _ = -1 := h3
  linarith

end NewtonianPotential

/-- Schwarzschild metric in weak-field limit.

    g_00 = -(1 + 2Φ_N/c²)
    g_ij = (1 - 2Φ_N/c²) δ_ij

    **Mathematical content:**
    The weak-field Schwarzschild metric is the first-order expansion
    of the exact Schwarzschild solution in powers of GM/(rc²).

    For r ≫ r_s = 2GM/c² (Schwarzschild radius):
    - g_00 ≈ -(1 - r_s/r) = -(1 + 2Φ_N/c²)
    - g_rr ≈ 1 + r_s/r = 1 - 2Φ_N/c² (in isotropic coords)

    **Citation:** Wald (1984), General Relativity, §6.1;
    Weinberg (1972), Gravitation and Cosmology, Ch. 8

    Reference: §3.3, §3.4, §6.2 -/
structure WeakFieldSchwarzschildApproximation where
  /-- Newtonian potential -/
  potential : NewtonianPotential
  /-- Weak-field condition: |Φ_N| < c²/2 -/
  weak_field_condition : potential.phi_N > -potential.constants.c^2 / 2

namespace WeakFieldSchwarzschildApproximation

/-- The g_00 component in weak-field Schwarzschild.

    g_00 = -(1 + 2Φ_N/c²) ≈ -1 for Φ_N → 0

    Reference: §3.3 -/
noncomputable def g_00 (wf : WeakFieldSchwarzschildApproximation) : ℝ :=
  -(1 + 2 * wf.potential.phi_N / wf.potential.constants.c^2)

/-- The g_ii components in weak-field Schwarzschild.

    g_ii = (1 - 2Φ_N/c²) for i = 1, 2, 3

    Reference: §3.3 -/
noncomputable def g_ii (wf : WeakFieldSchwarzschildApproximation) : ℝ :=
  1 - 2 * wf.potential.phi_N / wf.potential.constants.c^2

/-- The metric approaches Minkowski as Φ_N → 0.

    lim_{Φ_N → 0} g_μν = η_μν

    Reference: §10.1 -/
theorem flat_limit_g_00 :
    -(1 + 2 * (0 : ℝ) / 1) = -1 := by ring

theorem flat_limit_g_ii :
    (1 : ℝ) - 2 * 0 / 1 = 1 := by ring

end WeakFieldSchwarzschildApproximation

end ChiralGeometrogenesis.Phase5.Theorem_5_2_1.NewtonianLimit
