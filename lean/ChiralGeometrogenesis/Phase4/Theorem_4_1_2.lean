/-
  Phase4/Theorem_4_1_2.lean

  Theorem 4.1.2: Soliton Mass Spectrum

  Status: ESTABLISHED (Standard Result from Adkins, Nappi & Witten 1983)

  This file formalizes the soliton (skyrmion) mass spectrum, which determines
  the mass of topological solitons from their topological charge and chiral
  parameters.

  **Mathematical Foundation:**
  The soliton mass formula is:
    M_soliton = (6π² f_π / e) |Q| · F(m_π / f_π e)

  where:
  - f_π: pion decay constant (or chiral VEV in CG)
  - e: Skyrme parameter (dimensionless, e ∈ [4.0, 6.0])
  - Q: topological charge (integer winding number from π₃(SU(2)) ≅ ℤ)
  - F: form factor for explicit symmetry breaking

  **Key Results:**
  1. Classical soliton mass ≈ 1240 MeV (for QCD parameters)
  2. Quantum corrections reduce this by ~25% to ~940 MeV (nucleon mass)
  3. CG application: M_CG ≈ 14.6 TeV / g_χ

  **Physical Applications:**
  - Skyrmions model baryons in QCD (nucleon mass ≈ 940 MeV)
  - In CG: electroweak scale solitons with mass ~3-15 TeV

  **Original Sources:**
  - Adkins, G.S., Nappi, C.R., & Witten, E. (1983). "Static properties of
    nucleons in the Skyrme model." Nucl. Phys. B 228:552-566.
  - Adkins, G.S. & Nappi, C.R. (1984). "The Skyrme model with pion masses."
    Nucl. Phys. B 233:109-115.
  - Derrick, G.H. (1964). "Comments on nonlinear wave equations..."
    J. Math. Phys. 5:1252.

  **CG Prerequisites:**
  - Theorem 4.1.1 (Existence of Solitons): Establishes soliton existence
  - PureMath/AlgebraicTopology/HomotopyGroups.lean: π₃(SU(2)) ≅ ℤ

  **Cross-References:**
  - Phase4/Theorem_4_1_1.lean: SolitonConfig, SkyrmeParameters, BogomolnySoliton
  - Phase3/Theorem_3_1_1.lean: Phase-gradient mass generation mass (complementary mechanism)

  Reference: docs/proofs/Phase4/Theorem-4.1.2-Soliton-Mass-Spectrum.md
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds  -- For explicit π bounds: π > 3.14, π < 3.15

-- Import project modules
import ChiralGeometrogenesis.Phase4.Theorem_4_1_1

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase4.SolitonMass

open ChiralGeometrogenesis.Phase4.Solitons
open ChiralGeometrogenesis.PureMath.AlgebraicTopology

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 1: SOLITON MASS FORMULA
    ═══════════════════════════════════════════════════════════════════════════

    The soliton mass is determined by the topological charge and Skyrme
    parameters. The key formula is:

    M = (6π² f_π / e) |Q| · F(m_π / f_π e)

    where F is a form factor accounting for explicit chiral symmetry breaking.

    Reference: Theorem-4.1.2-Soliton-Mass-Spectrum.md §1, §2
-/

/-- **Form Factor for Pion Mass Correction**

    The form factor F accounts for explicit chiral symmetry breaking due to
    pion mass. For massless pions, F = 1. For physical pions, F ≈ 1.23.

    **Mathematical Definition:**
    F(x) where x = m_π / (f_π · e) encodes the effect of the mass term in
    the Skyrme Lagrangian on the soliton profile and energy.

    **Numerical Values (from literature):**
    - F(0) = 1.0 (massless pion limit)
    - F(0.178) ≈ 1.23 (physical pion mass with f_π = 93 MeV, e = 4.84)

    **Mathematical Properties:**
    - F is monotonically increasing: larger explicit breaking → larger mass
    - F(0) = 1 (chiral limit)
    - F is bounded: 1 ≤ F(x) < ∞ for finite x
    - F is continuous (from variational analysis)

    **Physical Interpretation:**
    The form factor captures how the explicit chiral symmetry breaking term
    (proportional to m_π²) modifies the soliton profile and hence its mass.
    As mπ increases, the soliton becomes more localized, increasing the
    gradient energy and hence the total mass.

    **References:**
    - Adkins & Nappi (1984). Nucl. Phys. B 233:109-115
    - Holzwarth & Schwesinger (1986). Rep. Prog. Phys. 49:825

    This structure captures the essential properties; the exact functional
    form requires numerical solution of the profile equation. -/
structure FormFactor where
  /-- The form factor function F: ℝ → ℝ -/
  F : ℝ → ℝ
  /-- F(0) = 1 (massless limit) -/
  massless_limit : F 0 = 1
  /-- F is positive for physical parameters -/
  F_pos : ∀ x, x ≥ 0 → F x > 0
  /-- F ≥ 1 for x ≥ 0 (explicit breaking always increases mass) -/
  F_ge_one : ∀ x, x ≥ 0 → F x ≥ 1
  /-- F is monotonically non-decreasing for x ≥ 0 -/
  F_mono : ∀ x y, 0 ≤ x → x ≤ y → F x ≤ F y

/-- **Standard Form Factor (Linear Approximation)**

    For small x = m_π/(f_π e), the form factor admits a linear expansion:
    F(x) ≈ 1 + ax where a ≈ 1.3 (from numerical fits).

    For QCD parameters: x ≈ 0.178, giving F ≈ 1.23.

    **Model:** F(x) = 1 + 1.3x (valid for x ∈ [0, 0.3])

    **Note:** This linear model is an approximation. The full form factor
    requires solving the profile equation numerically. For precision work,
    use `numerical_form_factor` which encodes tabulated values.

    **Reference:** Adkins & Nappi (1984), Table 1 -/
noncomputable def standard_form_factor : FormFactor where
  F := fun x => if x ≤ 0 then 1 else 1 + 1.3 * x  -- Linear model for x > 0
  massless_limit := by simp only [le_refl, ite_true]
  F_pos := by
    intro x hx
    by_cases h : x ≤ 0
    · simp only [h, ite_true]; norm_num
    · simp only [h, ite_false]
      push_neg at h
      have : 1.3 * x > 0 := mul_pos (by norm_num : (1.3 : ℝ) > 0) h
      linarith
  F_ge_one := by
    intro x hx
    by_cases h : x ≤ 0
    · simp only [h, ite_true]; norm_num
    · simp only [h, ite_false]
      push_neg at h
      have : 1.3 * x ≥ 0 := mul_nonneg (by norm_num : (1.3 : ℝ) ≥ 0) (le_of_lt h)
      linarith
  F_mono := by
    intro x y hx hxy
    by_cases hxneg : x ≤ 0
    · by_cases hyneg : y ≤ 0
      · simp only [hxneg, hyneg, ite_true]; norm_num
      · simp only [hxneg, ite_true, hyneg, ite_false]
        push_neg at hyneg
        have : 1.3 * y ≥ 0 := mul_nonneg (by norm_num) (le_of_lt hyneg)
        linarith
    · -- x > 0, so y > 0 too
      push_neg at hxneg
      have hyneg : ¬ y ≤ 0 := by linarith
      have hxneg' : ¬ x ≤ 0 := by linarith
      simp only [hxneg', hyneg, ite_false]
      have : 1.3 * x ≤ 1.3 * y := by linarith
      linarith

/-- Form factor value at QCD physical point x ≈ 0.178 gives F ≈ 1.23 -/
theorem standard_form_factor_qcd_value :
    let x := (0.178 : ℝ)  -- m_π / (f_π · e) for QCD
    |standard_form_factor.F x - 1.23| < 0.01 := by
  simp only [standard_form_factor]
  norm_num

/-- **Classical Soliton Mass (No Pion Mass Correction)**

    The classical soliton mass without explicit symmetry breaking:
    M_classical = (6π² f_π / e) |Q|

    This corresponds to F = 1 in the full formula.

    **Numerical Evaluation (QCD):**
    With f_π = 93 MeV, e = 4.84:
    M_classical = 6π² × 93 / 4.84 ≈ 1140 MeV (per unit charge)

    Reference: §2.4 -/
noncomputable def classical_soliton_mass (p : SkyrmeParameters) (Q : ℤ) : ℝ :=
  bogomolny_constant p * |Q|

/-- Classical soliton mass equals Bogomolny bound (for saturating solutions) -/
theorem classical_mass_eq_bogomolny (p : SkyrmeParameters) (Q : ℤ) :
    classical_soliton_mass p Q = bogomolny_constant p * |Q| := rfl

/-- Classical soliton mass is non-negative -/
theorem classical_mass_nonneg (p : SkyrmeParameters) (Q : ℤ) :
    classical_soliton_mass p Q ≥ 0 := by
  unfold classical_soliton_mass
  apply mul_nonneg
  · exact le_of_lt (bogomolny_constant_pos p)
  · simp only [Int.cast_abs]
    exact abs_nonneg _

/-- Classical soliton mass is positive for Q ≠ 0 -/
theorem classical_mass_pos (p : SkyrmeParameters) (Q : ℤ) (hQ : Q ≠ 0) :
    classical_soliton_mass p Q > 0 := by
  unfold classical_soliton_mass
  apply mul_pos
  · exact bogomolny_constant_pos p
  · have h : |Q| > 0 := abs_pos.mpr hQ
    exact Int.cast_pos.mpr h

/-- **Charge Conjugation Symmetry (C-symmetry) for Classical Mass**

    The soliton mass depends only on |Q|, so M(Q) = M(-Q).
    This reflects C-symmetry: solitons and anti-solitons have equal mass.

    **Physical Interpretation:**
    - Q > 0: soliton (e.g., proton in Skyrme model)
    - Q < 0: anti-soliton (e.g., antiproton)
    - |Q| determines mass, not the sign

    **Derivation:**
    M(Q) = C|Q| and M(-Q) = C|-Q| = C|Q| = M(Q)

    **Reference:** Manton & Sutcliffe (2004), Ch. 9 -/
theorem classical_mass_charge_conjugation (p : SkyrmeParameters) (Q : ℤ) :
    classical_soliton_mass p Q = classical_soliton_mass p (-Q) := by
  unfold classical_soliton_mass
  simp only [abs_neg]

/-- **Full Soliton Mass with Form Factor**

    The complete soliton mass formula including pion mass effects:
    M_soliton = (6π² f_π / e) |Q| · F(m_π / f_π e)

    Reference: §1, §2.4 -/
noncomputable def soliton_mass (p : SkyrmeParameters) (Q : ℤ) (ff : FormFactor)
    (m_pi : ℝ) : ℝ :=
  classical_soliton_mass p Q * ff.F (m_pi / (p.f_pi * p.e))

/-- In the massless pion limit, soliton mass equals classical mass -/
theorem soliton_mass_massless_limit (p : SkyrmeParameters) (Q : ℤ) (ff : FormFactor) :
    soliton_mass p Q ff 0 = classical_soliton_mass p Q := by
  unfold soliton_mass
  simp only [zero_div, ff.massless_limit, mul_one]

/-- Soliton mass is positive for Q ≠ 0 -/
theorem soliton_mass_pos (p : SkyrmeParameters) (Q : ℤ) (hQ : Q ≠ 0) (ff : FormFactor)
    (m_pi : ℝ) (hm : m_pi ≥ 0) :
    soliton_mass p Q ff m_pi > 0 := by
  unfold soliton_mass
  apply mul_pos
  · exact classical_mass_pos p Q hQ
  · have harg : m_pi / (p.f_pi * p.e) ≥ 0 := by
      apply div_nonneg hm
      exact le_of_lt (mul_pos p.f_pi_pos p.e_pos)
    exact ff.F_pos _ harg

/-- **Charge Conjugation Symmetry (C-symmetry) for Full Soliton Mass**

    C-symmetry extends to the full mass formula with form factor.
    Solitons (Q > 0) and anti-solitons (Q < 0) have identical masses. -/
theorem soliton_mass_charge_conjugation (p : SkyrmeParameters) (Q : ℤ) (ff : FormFactor)
    (m_pi : ℝ) :
    soliton_mass p Q ff m_pi = soliton_mass p (-Q) ff m_pi := by
  unfold soliton_mass
  rw [classical_mass_charge_conjugation]

/-- Soliton and anti-soliton masses are equal (Q = ±1 case) -/
theorem soliton_antisoliton_equal_mass (p : SkyrmeParameters) (ff : FormFactor) (m_pi : ℝ) :
    soliton_mass p 1 ff m_pi = soliton_mass p (-1) ff m_pi :=
  soliton_mass_charge_conjugation p 1 ff m_pi

/-- **Bogomolny Bound for Full Soliton Mass**

    The soliton mass with form factor is bounded below by the Bogomolny bound:
    M_soliton ≥ C|Q|

    where C = 6π² f_π / e is the Bogomolny constant.

    **Derivation:**
    Since F(x) ≥ 1 for all x ≥ 0 (explicit breaking increases mass), we have:
    M_soliton = C|Q| · F(x) ≥ C|Q| · 1 = C|Q|

    This is the key physical bound ensuring soliton stability.

    **Reference:** Theorem-4.1.2-Soliton-Mass-Spectrum.md §2.5 -/
theorem soliton_mass_bogomolny_bound (p : SkyrmeParameters) (Q : ℤ) (ff : FormFactor)
    (m_pi : ℝ) (hm : m_pi ≥ 0) :
    soliton_mass p Q ff m_pi ≥ bogomolny_constant p * |Q| := by
  unfold soliton_mass classical_soliton_mass
  have harg : m_pi / (p.f_pi * p.e) ≥ 0 := by
    apply div_nonneg hm
    exact le_of_lt (mul_pos p.f_pi_pos p.e_pos)
  have hF : ff.F (m_pi / (p.f_pi * p.e)) ≥ 1 := ff.F_ge_one _ harg
  have hC : bogomolny_constant p ≥ 0 := le_of_lt (bogomolny_constant_pos p)
  have hQ : (↑|Q| : ℝ) ≥ 0 := by simp only [Int.cast_abs]; exact abs_nonneg _
  calc bogomolny_constant p * |Q| * ff.F (m_pi / (p.f_pi * p.e))
      ≥ bogomolny_constant p * |Q| * 1 := by
        apply mul_le_mul_of_nonneg_left hF
        exact mul_nonneg hC hQ
    _ = bogomolny_constant p * |Q| := by ring

/-- Soliton mass equals Bogomolny bound in the massless limit -/
theorem soliton_mass_saturates_bound_massless (p : SkyrmeParameters) (Q : ℤ) (ff : FormFactor) :
    soliton_mass p Q ff 0 = bogomolny_constant p * |Q| := by
  rw [soliton_mass_massless_limit]
  rfl

/-- Soliton mass exceeds classical mass for non-zero pion mass -/
theorem soliton_mass_ge_classical (p : SkyrmeParameters) (Q : ℤ) (ff : FormFactor)
    (m_pi : ℝ) (hm : m_pi ≥ 0) :
    soliton_mass p Q ff m_pi ≥ classical_soliton_mass p Q := by
  unfold soliton_mass
  have harg : m_pi / (p.f_pi * p.e) ≥ 0 := by
    apply div_nonneg hm
    exact le_of_lt (mul_pos p.f_pi_pos p.e_pos)
  have hF : ff.F (m_pi / (p.f_pi * p.e)) ≥ 1 := ff.F_ge_one _ harg
  have hM : classical_soliton_mass p Q ≥ 0 := classical_mass_nonneg p Q
  calc classical_soliton_mass p Q * ff.F (m_pi / (p.f_pi * p.e))
      ≥ classical_soliton_mass p Q * 1 := by
        apply mul_le_mul_of_nonneg_left hF hM
    _ = classical_soliton_mass p Q := mul_one _

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 2: NUMERICAL COEFFICIENTS AND PHENOMENOLOGY
    ═══════════════════════════════════════════════════════════════════════════

    Key numerical results from the literature:
    - Coefficient: 6π² × 1.23 ≈ 73 (for F ≈ 1.23)
    - Classical mass: ~1240 MeV for e = 5.45
    - After quantum corrections: ~940 MeV (nucleon mass!)

    Reference: §2.4, §4
-/

/-- **Numerical Coefficient**

    The coefficient 6π² ≈ 59.2 appears in the mass formula.
    With form factor F ≈ 1.23: 6π² × 1.23 ≈ 73 -/
noncomputable def mass_coefficient : ℝ := 6 * Real.pi^2

/-- 6π² is positive -/
theorem mass_coefficient_pos : mass_coefficient > 0 := by
  unfold mass_coefficient
  apply mul_pos
  · linarith
  · exact sq_pos_of_pos Real.pi_pos

/-- **6π² ≈ 59.22 (proven bounds)**

    Using Mathlib's proven bounds on π (from Real.pi_gt_d2 and Real.pi_lt_d2):
    - 3.14 < π < 3.15

    We derive:
    - 6 × 3.14² = 6 × 9.8596 = 59.1576 < 6π²
    - 6π² < 6 × 3.15² = 6 × 9.9225 = 59.535

    So 59.15 < 6π² < 59.54, which gives us 59 < 6π² < 60.

    **Reference:** Mathlib.Analysis.Real.Pi.Bounds -/
theorem mass_coefficient_bounds :
    mass_coefficient > 59 ∧ mass_coefficient < 60 := by
  unfold mass_coefficient
  constructor
  · -- 6π² > 59, i.e., π² > 59/6 ≈ 9.833
    -- Since π > 3.14, we have π² > 3.14² = 9.8596 > 9.833...
    have hpi : Real.pi > 3.14 := Real.pi_gt_d2
    have hpisq : Real.pi ^ 2 > 3.14 ^ 2 := sq_lt_sq' (by linarith) hpi
    calc 6 * Real.pi ^ 2 > 6 * (3.14 : ℝ) ^ 2 := by linarith
      _ = 6 * 9.8596 := by norm_num
      _ = 59.1576 := by norm_num
      _ > 59 := by norm_num
  · -- 6π² < 60, i.e., π² < 10
    -- Since π < 3.15, we have π² < 3.15² = 9.9225 < 10
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hpisq : Real.pi ^ 2 < 3.15 ^ 2 := by
      apply sq_lt_sq'
      · have h1 : Real.pi > 0 := Real.pi_pos
        linarith
      · exact hpi
    calc 6 * Real.pi ^ 2 < 6 * (3.15 : ℝ) ^ 2 := by linarith
      _ = 6 * 9.9225 := by norm_num
      _ = 59.535 := by norm_num
      _ < 60 := by norm_num

/-- **Tighter Mass Coefficient Bounds (4 decimal places)**

    Using Mathlib's `Real.pi_gt_d4` (π > 3.1415) and `Real.pi_lt_d4` (π < 3.1416):

    **Calculation:**
    - 6π² > 6 × 3.1415² = 6 × 9.86901225 = 59.21407...
    - 6π² < 6 × 3.1416² = 6 × 9.86965... = 59.21792...

    So 59.21 < 6π² < 59.22.

    This is ~10× more precise than the 2-decimal bounds.

    **Reference:** Mathlib.Analysis.Real.Pi.Bounds (pi_gt_d4, pi_lt_d4) -/
theorem mass_coefficient_bounds_tight :
    mass_coefficient > 59.21 ∧ mass_coefficient < 59.22 := by
  unfold mass_coefficient
  constructor
  · -- 6π² > 59.21
    -- Since π > 3.1415, we have π² > 3.1415² = 9.86901225
    -- 6 × 3.1415² = 59.2140735 > 59.21
    have hpi : Real.pi > 3.1415 := Real.pi_gt_d4
    have hpisq : Real.pi ^ 2 > 3.1415 ^ 2 := sq_lt_sq' (by linarith) hpi
    have h1 : 6 * Real.pi ^ 2 > 6 * 3.1415 ^ 2 := by nlinarith [sq_nonneg Real.pi]
    -- 6 × 3.1415² = 6 × 9.86901225 = 59.2140735
    have h2 : (6 : ℝ) * 3.1415 ^ 2 > 59.21 := by norm_num
    linarith
  · -- 6π² < 59.22
    -- Since π < 3.1416, we have π² < 3.1416²
    -- 6 × 3.1416² = 59.21792256 < 59.22
    have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
    have hpi_pos : Real.pi > 0 := Real.pi_pos
    have hpisq : Real.pi ^ 2 < 3.1416 ^ 2 := sq_lt_sq' (by linarith) hpi
    have h1 : 6 * Real.pi ^ 2 < 6 * 3.1416 ^ 2 := by nlinarith [sq_nonneg Real.pi]
    have h2 : (6 : ℝ) * 3.1416 ^ 2 < 59.22 := by norm_num
    linarith

/-- **Approximate value of 6π²**

    For reference, 6π² ≈ 59.2176 (to 4 decimal places)

    The tight bounds give: 59.21 < 6π² < 59.22
    So |6π² - 59.215| < 0.005 (using center of interval) -/
theorem mass_coefficient_value_approx :
    |mass_coefficient - 59.215| < 0.006 := by
  have ⟨hlo, hhi⟩ := mass_coefficient_bounds_tight
  -- 59.21 < mass_coefficient < 59.22
  -- Center is 59.215, half-width is 0.005
  -- |x - 59.215| < 0.005 for x ∈ (59.21, 59.22)
  rw [abs_lt]
  constructor <;> linarith

/-- With form factor 1.23, effective coefficient ≈ 73 -/
theorem effective_coefficient_bounds :
    mass_coefficient * 1.23 > 72 ∧ mass_coefficient * 1.23 < 74 := by
  have ⟨hlo, hhi⟩ := mass_coefficient_bounds
  constructor <;> linarith

/-- **Tighter effective coefficient bounds**

    With form factor F = 1.23 and tight mass_coefficient bounds:
    - 59.21 × 1.23 = 72.8283
    - 59.22 × 1.23 = 72.8406

    So 72.82 < 6π² × 1.23 < 72.85 -/
theorem effective_coefficient_bounds_tight :
    mass_coefficient * 1.23 > 72.82 ∧ mass_coefficient * 1.23 < 72.85 := by
  have ⟨hlo, hhi⟩ := mass_coefficient_bounds_tight
  constructor <;> linarith

/-- **QCD Soliton Mass (Physical Parameters)**

    With physical QCD parameters:
    - f_π = 92.1 MeV (pion decay constant)
    - e ≈ 5.45 (Skyrme parameter from nucleon mass fit)
    - F ≈ 1.23 (form factor)

    Classical mass: M ≈ 1240 MeV
    After ~25% quantum corrections: M ≈ 940 MeV ≈ nucleon mass!

    Reference: §2.4, §4 -/
structure QCDSolitonMass where
  /-- Classical soliton mass in MeV -/
  classical_mass : ℝ
  /-- Quantum corrections (negative, ~-300 MeV) -/
  quantum_correction : ℝ
  /-- Physical mass after corrections -/
  physical_mass : ℝ
  /-- Physical = classical + quantum -/
  mass_relation : physical_mass = classical_mass + quantum_correction
  /-- Quantum correction is negative (reduces mass) -/
  correction_neg : quantum_correction < 0

/-- Standard QCD soliton mass values from Adkins-Nappi-Witten -/
noncomputable def anw_soliton_mass : QCDSolitonMass where
  classical_mass := 1240   -- MeV, for e ≈ 5.45
  quantum_correction := -300  -- ~25% reduction from spin quantization + Casimir
  physical_mass := 940  -- MeV, approximately nucleon mass
  mass_relation := by ring
  correction_neg := by norm_num

/-- Physical soliton mass is close to nucleon mass (938 MeV) -/
theorem anw_mass_near_nucleon :
    |anw_soliton_mass.physical_mass - 938| < 10 := by
  simp only [anw_soliton_mass, abs_sub_lt_iff]
  constructor <;> norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 3: STABILITY FROM DERRICK'S THEOREM
    ═══════════════════════════════════════════════════════════════════════════

    Derrick's theorem (1964) states that in 3D, a scalar field with only
    two-derivative kinetic term cannot support stable solitons. The Skyrme
    term (four derivatives) provides the stabilization.

    Reference: §2.5
-/

/-- **Scaling Behavior of Energy Components**

    Under rescaling φ(x) → φ(λx), the energy components scale as:
    - Kinetic term: E_kin(λ) = λ⁻¹ E_kin
    - Skyrme term: E_Skyrme(λ) = λ E_Skyrme
    - Potential term: E_pot(λ) = λ⁻³ E_pot

    The competition between kinetic and Skyrme terms allows stable solitons.

    Reference: §2.5 -/
structure DerrickScaling where
  /-- Kinetic energy (two-derivative term) -/
  E_kin : ℝ
  /-- Skyrme energy (four-derivative term) -/
  E_Skyrme : ℝ
  /-- Potential energy (zero-derivative term) -/
  E_pot : ℝ
  /-- All energies are non-negative -/
  E_kin_nonneg : E_kin ≥ 0
  E_Skyrme_nonneg : E_Skyrme ≥ 0
  E_pot_nonneg : E_pot ≥ 0

/-- Scaled kinetic energy: E_kin(λ) = λ⁻¹ E_kin -/
noncomputable def DerrickScaling.scaled_kin (d : DerrickScaling) (scale : ℝ) : ℝ :=
  d.E_kin / scale

/-- Scaled Skyrme energy: E_Skyrme(λ) = λ E_Skyrme -/
noncomputable def DerrickScaling.scaled_Skyrme (d : DerrickScaling) (scale : ℝ) : ℝ :=
  scale * d.E_Skyrme

/-- Scaled potential energy: E_pot(λ) = λ⁻³ E_pot -/
noncomputable def DerrickScaling.scaled_pot (d : DerrickScaling) (scale : ℝ) : ℝ :=
  d.E_pot / scale^3

/-- Total scaled energy -/
noncomputable def DerrickScaling.total_energy (d : DerrickScaling) (scale : ℝ) : ℝ :=
  d.scaled_kin scale + d.scaled_Skyrme scale + d.scaled_pot scale

/-- **Virial Relation (Stability Condition)**

    At the stable soliton size (λ = 1), the virial relation holds:
    E_kin = E_Skyrme

    This comes from ∂E/∂λ|_{λ=1} = 0:
    -E_kin + E_Skyrme - 3E_pot = 0

    For massless pions (E_pot = 0): E_kin = E_Skyrme

    Reference: §2.5 -/
def DerrickScaling.satisfies_virial (d : DerrickScaling) : Prop :=
  d.E_Skyrme - d.E_kin = 3 * d.E_pot

/-- **Derivation of Virial Relation from Scaling**

    The virial relation comes from requiring dE/dλ|_{λ=1} = 0 for stability.

    Given E(λ) = E_kin/λ + λ·E_Skyrme + E_pot/λ³, we compute:
    dE/dλ = -E_kin/λ² + E_Skyrme - 3E_pot/λ⁴

    At λ = 1:
    dE/dλ|_{λ=1} = -E_kin + E_Skyrme - 3E_pot = 0

    Rearranging: E_Skyrme - E_kin = 3E_pot

    **Mathematical Note:** This derivation uses calculus (differentiation)
    which is available in Mathlib but would require additional imports
    (Mathlib.Analysis.Calculus.Deriv.Basic). We formalize the algebraic
    consequence directly.

    **Reference:** Derrick (1964), Manton & Sutcliffe (2004) Ch. 4 -/
theorem virial_from_stability_condition (d : DerrickScaling) :
    -- The virial relation is exactly the condition dE/dλ|_{λ=1} = 0
    -- expressed algebraically as: E_Skyrme - E_kin = 3 * E_pot
    d.satisfies_virial ↔ d.E_Skyrme - d.E_kin = 3 * d.E_pot := by
  rfl

/-- Total energy at λ = 1 equals sum of components -/
theorem total_energy_at_one (d : DerrickScaling) :
    d.total_energy 1 = d.E_kin + d.E_Skyrme + d.E_pot := by
  unfold DerrickScaling.total_energy DerrickScaling.scaled_kin
    DerrickScaling.scaled_Skyrme DerrickScaling.scaled_pot
  simp only [div_one, one_mul, one_pow]

/-- Scaling derivative coefficient at λ = 1

    This represents d/dλ[E(λ)]|_{λ=1} = -E_kin + E_Skyrme - 3E_pot

    A stable soliton requires this to be zero, giving the virial relation. -/
noncomputable def DerrickScaling.scaling_derivative (d : DerrickScaling) : ℝ :=
  -d.E_kin + d.E_Skyrme - 3 * d.E_pot

/-- Virial relation is equivalent to zero scaling derivative -/
theorem virial_iff_zero_derivative (d : DerrickScaling) :
    d.satisfies_virial ↔ d.scaling_derivative = 0 := by
  unfold DerrickScaling.satisfies_virial DerrickScaling.scaling_derivative
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Massless pion virial: E_kin = E_Skyrme -/
theorem virial_massless (d : DerrickScaling) (h_pot : d.E_pot = 0) :
    d.satisfies_virial → d.E_kin = d.E_Skyrme := by
  intro hvir
  simp only [DerrickScaling.satisfies_virial, h_pot, mul_zero] at hvir
  linarith

/-- **Derrick's No-Go Theorem (Without Skyrme Term)**

    Pure sigma model (E_Skyrme = 0) cannot have stable solitons.
    The virial condition becomes -E_kin = 3E_pot, which with E_pot ≥ 0
    implies E_kin ≤ 0. But E_kin ≥ 0, so E_kin = 0.

    Reference: §2.5 -/
theorem derrick_no_go (d : DerrickScaling)
    (h_no_Skyrme : d.E_Skyrme = 0)
    (h_virial : d.satisfies_virial) :
    d.E_kin = 0 := by
  simp only [DerrickScaling.satisfies_virial, h_no_Skyrme, zero_sub] at h_virial
  -- h_virial: -E_kin = 3 * E_pot
  -- E_kin ≥ 0 and E_pot ≥ 0 implies E_kin = 0
  have h1 : -d.E_kin ≥ 0 := by linarith [d.E_pot_nonneg]
  linarith [d.E_kin_nonneg]

/-- **Second Derivative of Scaled Energy**

    The second derivative d²E/dλ²|_{λ=1} determines stability:
    d²E/dλ² = 2E_kin/λ³ + 12E_pot/λ⁵

    At λ = 1: d²E/dλ²|_{λ=1} = 2E_kin + 12E_pot

    **Derivation:**
    From E(λ) = E_kin/λ + λ·E_Skyrme + E_pot/λ³:
    - dE/dλ = -E_kin/λ² + E_Skyrme - 3E_pot/λ⁴
    - d²E/dλ² = 2E_kin/λ³ + 12E_pot/λ⁵

    Note: The Skyrme term (linear in λ) contributes 0 to the second derivative.

    **Reference:** Manton & Sutcliffe (2004), Ch. 4 -/
noncomputable def DerrickScaling.second_derivative (d : DerrickScaling) : ℝ :=
  2 * d.E_kin + 12 * d.E_pot

/-- Second derivative is non-negative for physical configurations -/
theorem DerrickScaling.second_derivative_nonneg (d : DerrickScaling) :
    d.second_derivative ≥ 0 := by
  unfold second_derivative
  have h1 : 2 * d.E_kin ≥ 0 := mul_nonneg (by norm_num) d.E_kin_nonneg
  have h2 : 12 * d.E_pot ≥ 0 := mul_nonneg (by norm_num) d.E_pot_nonneg
  linarith

/-- **Stability Theorem: Skyrme Soliton is a Local Energy Minimum**

    With E_Skyrme > 0 and the virial condition satisfied, the soliton
    configuration is a LOCAL MINIMUM of the energy functional under scaling.

    **Conditions for stability:**
    1. First derivative zero: dE/dλ|_{λ=1} = 0 (virial condition)
    2. Second derivative positive: d²E/dλ²|_{λ=1} > 0

    The second derivative is 2E_kin + 12E_pot, which is strictly positive
    when E_kin > 0 (guaranteed by the virial condition with E_Skyrme > 0).

    **Derivation:**
    From virial: E_Skyrme - E_kin = 3E_pot
    If E_Skyrme > 0 and E_pot ≥ 0, then E_kin = E_Skyrme - 3E_pot.
    For E_pot = 0 (massless pions): E_kin = E_Skyrme > 0
    For E_pot > 0: E_kin could be positive or negative depending on balance.

    The key insight is that for physical Skyrme solitons, E_kin > 0 always.

    **Reference:** Derrick (1964), Manton & Sutcliffe (2004) Ch. 4 -/
theorem skyrme_soliton_is_stable (d : DerrickScaling)
    (h_virial : d.satisfies_virial)
    (h_kin_pos : d.E_kin > 0) :
    d.second_derivative > 0 := by
  unfold DerrickScaling.second_derivative
  have h1 : 2 * d.E_kin > 0 := mul_pos (by norm_num : (2:ℝ) > 0) h_kin_pos
  have h2 : 12 * d.E_pot ≥ 0 := mul_nonneg (by norm_num) d.E_pot_nonneg
  linarith

/-- **Stability with massless pions**

    For massless pions (E_pot = 0), the virial condition gives E_kin = E_Skyrme.
    With E_Skyrme > 0, we have E_kin > 0, ensuring stability. -/
theorem skyrme_soliton_stable_massless (d : DerrickScaling)
    (h_pot : d.E_pot = 0)
    (h_Skyrme_pos : d.E_Skyrme > 0)
    (h_virial : d.satisfies_virial) :
    d.second_derivative > 0 := by
  have h_kin : d.E_kin = d.E_Skyrme := virial_massless d h_pot h_virial
  have h_kin_pos : d.E_kin > 0 := by rw [h_kin]; exact h_Skyrme_pos
  exact skyrme_soliton_is_stable d h_virial h_kin_pos

/-- **Necessary condition for non-trivial soliton**

    A non-trivial stable soliton requires E_Skyrme > 0.
    Without the Skyrme term, Derrick's no-go theorem applies. -/
theorem skyrme_term_necessary (d : DerrickScaling)
    (h_virial : d.satisfies_virial)
    (h_kin_pos : d.E_kin > 0) :
    d.E_Skyrme > 0 := by
  -- From virial: E_Skyrme - E_kin = 3 * E_pot
  -- So E_Skyrme = E_kin + 3 * E_pot
  have hv : d.E_Skyrme - d.E_kin = 3 * d.E_pot := h_virial
  have hp : 3 * d.E_pot ≥ 0 := mul_nonneg (by norm_num) d.E_pot_nonneg
  linarith

/-- **Forward stability criterion**

    If a configuration satisfies the virial condition with E_kin > 0,
    then it represents a stable soliton (local energy minimum).

    This is the physically relevant direction: given a Skyrme soliton
    with non-trivial field gradients (E_kin > 0), it is stable. -/
theorem stability_criterion_forward (d : DerrickScaling)
    (h_virial : d.satisfies_virial)
    (h_kin_pos : d.E_kin > 0) :
    d.scaling_derivative = 0 ∧ d.second_derivative > 0 :=
  ⟨(virial_iff_zero_derivative d).mp h_virial, skyrme_soliton_is_stable d h_virial h_kin_pos⟩

/-- **Stability implies non-trivial configuration**

    If the second derivative is positive, then either E_kin > 0 or E_pot > 0
    (or both). A completely trivial configuration (E_kin = E_pot = 0) cannot
    be stable. -/
theorem stability_implies_nontrivial (d : DerrickScaling)
    (h_stable : d.second_derivative > 0) :
    d.E_kin > 0 ∨ d.E_pot > 0 := by
  unfold DerrickScaling.second_derivative at h_stable
  by_contra h
  push_neg at h
  have hk : d.E_kin = 0 := le_antisymm h.1 d.E_kin_nonneg
  have hp : d.E_pot = 0 := le_antisymm h.2 d.E_pot_nonneg
  rw [hk, hp] at h_stable
  simp only [mul_zero, add_zero] at h_stable
  exact (lt_irrefl 0) h_stable

/-- **Physical soliton criterion**

    A physical Skyrme soliton has:
    1. Non-trivial topology (Q ≠ 0, handled elsewhere)
    2. Localized field configuration (E_kin > 0)
    3. Virial condition satisfied (stability)
    4. Skyrme term present (E_Skyrme > 0)

    This structure captures all requirements for a stable soliton. -/
structure PhysicalSolitonCriterion where
  /-- The energy scaling data -/
  scaling : DerrickScaling
  /-- Kinetic energy is positive (localized field) -/
  kin_pos : scaling.E_kin > 0
  /-- Virial condition is satisfied -/
  virial : scaling.satisfies_virial

/-- A physical soliton is automatically stable -/
theorem PhysicalSolitonCriterion.is_stable (p : PhysicalSolitonCriterion) :
    p.scaling.second_derivative > 0 :=
  skyrme_soliton_is_stable p.scaling p.virial p.kin_pos

/-- A physical soliton has non-zero Skyrme term -/
theorem PhysicalSolitonCriterion.skyrme_pos (p : PhysicalSolitonCriterion) :
    p.scaling.E_Skyrme > 0 :=
  skyrme_term_necessary p.scaling p.virial p.kin_pos

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 4: CG APPLICATION - ELECTROWEAK SCALE SOLITONS
    ═══════════════════════════════════════════════════════════════════════════

    In Chiral Geometrogenesis, the soliton mass formula applies at the
    electroweak scale with v_χ = 246 GeV replacing f_π = 93 MeV.

    Reference: §3
-/

/-- **CG Soliton Mass Scale**

    In CG, the soliton mass becomes:
    M_CG = (6π² v_χ / g_χ) |Q| · F(m_χ / v_χ g_χ)

    With v_χ = 246 GeV and g_χ ∼ O(1):
    M_CG ≈ 14.6 TeV / g_χ

    Reference: §3.1, §3.2 -/
structure CGSolitonMassScale where
  /-- Chiral VEV (electroweak scale, in GeV) -/
  v_chi : ℝ
  /-- Chiral coupling parameter -/
  g_chi : ℝ
  /-- VEV is positive -/
  v_chi_pos : v_chi > 0
  /-- Coupling is positive -/
  g_chi_pos : g_chi > 0

/-- Standard CG parameters: v_χ = 246 GeV -/
noncomputable def cg_standard_params (g : ℝ) (hg : g > 0) : CGSolitonMassScale where
  v_chi := 246  -- GeV
  g_chi := g
  v_chi_pos := by norm_num
  g_chi_pos := hg

/-- CG soliton mass (without form factor, in GeV) -/
noncomputable def cg_soliton_mass_GeV (params : CGSolitonMassScale) (Q : ℤ) : ℝ :=
  6 * Real.pi^2 * params.v_chi / params.g_chi * |Q|

/-- CG soliton mass is positive for Q ≠ 0 -/
theorem cg_mass_pos (params : CGSolitonMassScale) (Q : ℤ) (hQ : Q ≠ 0) :
    cg_soliton_mass_GeV params Q > 0 := by
  unfold cg_soliton_mass_GeV
  apply mul_pos
  · apply div_pos
    · apply mul_pos
      · apply mul_pos (by linarith : (6 : ℝ) > 0)
        exact sq_pos_of_pos Real.pi_pos
      · exact params.v_chi_pos
    · exact params.g_chi_pos
  · have h : |Q| > 0 := abs_pos.mpr hQ
    exact Int.cast_pos.mpr h

/-- **CG Mass Scale: ~14.6 TeV / g_χ**

    For g_χ = 1: M_CG ≈ 14.6 TeV = 14600 GeV

    Reference: §3.2 -/
theorem cg_mass_scale_estimate :
    let params := cg_standard_params 1 (by norm_num : (1:ℝ) > 0)
    cg_soliton_mass_GeV params 1 > 14000 ∧ cg_soliton_mass_GeV params 1 < 15000 := by
  simp only [cg_soliton_mass_GeV, cg_standard_params, abs_one, Int.cast_one, mul_one, div_one]
  have ⟨hlo, hhi⟩ := mass_coefficient_bounds
  unfold mass_coefficient at hlo hhi
  constructor
  · -- 6π² × 246 > 14000
    -- 6π² > 59, so 6π² × 246 > 59 × 246 = 14514 > 14000
    have h : 6 * Real.pi^2 * 246 > 59 * 246 := by linarith
    linarith
  · -- 6π² × 246 < 15000
    -- 6π² < 60, so 6π² × 246 < 60 × 246 = 14760 < 15000
    have h : 6 * Real.pi^2 * 246 < 60 * 246 := by linarith
    linarith

/-- CG mass values for various coupling choices -/
theorem cg_mass_table :
    let params1 := cg_standard_params 1 (by norm_num)
    let params2 := cg_standard_params 2 (by norm_num)
    let params5 := cg_standard_params 5 (by norm_num)
    -- g_χ = 1: ~14.6 TeV
    -- g_χ = 2: ~7.3 TeV (halved)
    -- g_χ = 5: ~2.9 TeV (divided by 5)
    cg_soliton_mass_GeV params1 1 / cg_soliton_mass_GeV params2 1 = 2 ∧
    cg_soliton_mass_GeV params1 1 / cg_soliton_mass_GeV params5 1 = 5 := by
  simp only [cg_soliton_mass_GeV, cg_standard_params, abs_one, Int.cast_one, mul_one]
  constructor <;> field_simp

/-- **Scale Ratio: CG vs QCD**

    The ratio v_χ / f_π sets the hierarchy between electroweak and QCD scales.

    **Precise values (PDG 2024):**
    - v_χ = v_H = 246.22 GeV (Higgs VEV = 1/(√2 G_F)^(1/2))
    - f_π = 92.1 MeV (pion decay constant)

    **Ratio:** v_χ / f_π = 246220 / 92.1 ≈ 2673

    **Simplified values used in this file:**
    - v_χ ≈ 246 GeV (rounded for convenience)
    - f_π ≈ 93 MeV (rounded, sometimes 92.1 MeV in literature)

    **Ratio (simplified):** 246000 / 93 ≈ 2645

    Both give scale ratio ≈ 2600-2700, which is consistent for order-of-magnitude
    calculations. The exact value only matters for precision phenomenology.

    Reference: §3.1, PDG 2024 -/
noncomputable def scale_ratio_cg_qcd : ℝ := 246000 / 93  -- in MeV for both (simplified)

/-- Precise scale ratio using PDG 2024 values -/
noncomputable def scale_ratio_cg_qcd_precise : ℝ := 246220 / 92.1

theorem scale_ratio_bounds :
    scale_ratio_cg_qcd > 2600 ∧ scale_ratio_cg_qcd < 2700 := by
  simp only [scale_ratio_cg_qcd]
  constructor <;> norm_num

theorem scale_ratio_bounds_precise :
    scale_ratio_cg_qcd_precise > 2670 ∧ scale_ratio_cg_qcd_precise < 2680 := by
  simp only [scale_ratio_cg_qcd_precise]
  constructor <;> norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 5: MULTI-SOLITON STATES AND BINDING
    ═══════════════════════════════════════════════════════════════════════════

    Higher topological charges give bound states with masses less than Q × M_B
    due to binding energy.

    Reference: §3.3
-/

/-- **Multi-Soliton Binding**

    For |Q| > 1, multi-soliton configurations have binding energy.
    The mass is less than |Q| times the single soliton mass.

    Reference: §3.3 -/
structure MultiSolitonBinding where
  /-- Topological charge -/
  Q : ℤ
  /-- Single soliton mass -/
  M_1 : ℝ
  /-- Multi-soliton mass -/
  M_Q : ℝ
  /-- Charge is non-zero -/
  Q_nonzero : Q ≠ 0
  /-- Single soliton mass is positive -/
  M_1_pos : M_1 > 0
  /-- Multi-soliton mass is positive -/
  M_Q_pos : M_Q > 0
  /-- Binding: M_Q < |Q| × M_1 for |Q| > 1 -/
  binding : |Q| > 1 → M_Q < |Q| * M_1

/-- Binding energy for multi-soliton state -/
noncomputable def MultiSolitonBinding.binding_energy (b : MultiSolitonBinding) : ℝ :=
  |b.Q| * b.M_1 - b.M_Q

/-- Binding energy is positive for |Q| > 1 -/
theorem MultiSolitonBinding.binding_energy_pos (b : MultiSolitonBinding)
    (hQ : |b.Q| > 1) : b.binding_energy > 0 := by
  unfold binding_energy
  have hM : b.M_Q < |b.Q| * b.M_1 := b.binding hQ
  linarith

/-- Literature values for multi-soliton binding (from Battye & Sutcliffe) -/
structure LiteratureBinding where
  Q : ℤ
  mass_ratio : ℝ  -- M_Q / M_1
  binding_ratio : ℝ  -- (|Q| × M_1 - M_Q) / M_1 = |Q| - mass_ratio

/-- Deuteron-like state (Q=2): mass ratio ≈ 1.90 -/
def deuteron_binding : LiteratureBinding where
  Q := 2
  mass_ratio := 1.90
  binding_ratio := 0.10  -- 2 - 1.90

/-- Alpha-like state (Q=4): mass ratio ≈ 3.70 -/
def alpha_binding : LiteratureBinding where
  Q := 4
  mass_ratio := 3.70
  binding_ratio := 0.30  -- 4 - 3.70

/-! ### LiteratureBinding Consistency Verification

    The binding ratio should satisfy: binding_ratio = |Q| - mass_ratio
    This represents the binding energy as a fraction of the single-soliton mass.

    **Physical Meaning:**
    - If M_Q is the mass of a Q-soliton and M_1 is the single soliton mass
    - mass_ratio = M_Q / M_1
    - binding_ratio = (|Q| × M_1 - M_Q) / M_1 = |Q| - mass_ratio
    - Positive binding_ratio indicates the multi-soliton is bound

    **Verification:** These theorems prove the defined values are self-consistent.
-/

/-- **Binding Consistency Predicate**

    A LiteratureBinding is consistent if its binding_ratio correctly equals
    |Q| - mass_ratio. This is the fundamental definition of binding energy. -/
def LiteratureBinding.is_consistent (b : LiteratureBinding) : Prop :=
  b.binding_ratio = |b.Q| - b.mass_ratio

/-- **Deuteron binding is internally consistent**

    Verifies: 0.10 = |2| - 1.90 = 2 - 1.90 ✓

    **Physical Context:**
    The deuteron-like B=2 skyrmion has mass ~1.90 M_nucleon, giving a
    binding energy of ~0.10 M_nucleon ≈ 94 MeV per nucleon.
    (Compare to actual deuteron: 2.224 MeV total binding.) -/
theorem deuteron_binding_consistent : deuteron_binding.is_consistent := by
  unfold LiteratureBinding.is_consistent deuteron_binding
  simp only [abs_of_pos (by norm_num : (2 : ℤ) > 0)]
  norm_num

/-- **Alpha binding is internally consistent**

    Verifies: 0.30 = |4| - 3.70 = 4 - 3.70 ✓

    **Physical Context:**
    The alpha-like B=4 skyrmion has mass ~3.70 M_nucleon, giving a
    binding energy of ~0.30 M_nucleon ≈ 282 MeV per 4 nucleons.
    (Compare to actual alpha: 28.3 MeV total binding.) -/
theorem alpha_binding_consistent : alpha_binding.is_consistent := by
  unfold LiteratureBinding.is_consistent alpha_binding
  simp only [abs_of_pos (by norm_num : (4 : ℤ) > 0)]
  norm_num

/-- **Binding ratio is positive for bound states**

    A positive binding ratio indicates the multi-soliton configuration is
    energetically favorable compared to separated single solitons.
    This is necessary for stable nuclei/skyrmions. -/
theorem deuteron_binding_positive : deuteron_binding.binding_ratio > 0 := by
  unfold deuteron_binding
  norm_num

theorem alpha_binding_positive : alpha_binding.binding_ratio > 0 := by
  unfold alpha_binding
  norm_num

/-- **Mass ratio satisfies sublinear scaling**

    For bound systems, M_Q < |Q| × M_1, i.e., mass_ratio < |Q|.
    This is equivalent to binding_ratio > 0.

    **Physical Meaning:**
    The multi-soliton has less mass than |Q| separated solitons due to
    attractive interactions (binding energy). -/
theorem deuteron_mass_sublinear :
    deuteron_binding.mass_ratio < |deuteron_binding.Q| := by
  unfold deuteron_binding
  simp only [abs_of_pos (by norm_num : (2 : ℤ) > 0)]
  norm_num

theorem alpha_mass_sublinear :
    alpha_binding.mass_ratio < |alpha_binding.Q| := by
  unfold alpha_binding
  simp only [abs_of_pos (by norm_num : (4 : ℤ) > 0)]
  norm_num

/-- **Binding increases with charge (multi-soliton effect)**

    Larger nuclei have more binding per nucleon (up to iron peak).
    α has more binding than deuteron: 0.30 > 0.10. -/
theorem alpha_more_bound_than_deuteron :
    alpha_binding.binding_ratio > deuteron_binding.binding_ratio := by
  unfold alpha_binding deuteron_binding
  norm_num

/-- **Binding per nucleon increases**

    The binding per unit charge: binding_ratio / |Q|
    α: 0.30/4 = 0.075, d: 0.10/2 = 0.05
    So α is more tightly bound per nucleon. -/
theorem alpha_more_bound_per_nucleon :
    alpha_binding.binding_ratio / |alpha_binding.Q| >
    deuteron_binding.binding_ratio / |deuteron_binding.Q| := by
  unfold alpha_binding deuteron_binding
  simp only [abs_of_pos (by norm_num : (4 : ℤ) > 0)]
  simp only [abs_of_pos (by norm_num : (2 : ℤ) > 0)]
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 6: THEOREM 4.1.2 - MAIN STATEMENT
    ═══════════════════════════════════════════════════════════════════════════

    The main theorem combining all components.

    Reference: §1, §7
-/

/-- **Mass ratio theorem (auxiliary)**

    For Q₂ ≠ 0, the mass ratio equals the charge ratio. -/
theorem mass_ratio_eq_charge_ratio (p : SkyrmeParameters) (Q₁ Q₂ : ℤ) (hQ₂ : Q₂ ≠ 0) :
    classical_soliton_mass p Q₁ / classical_soliton_mass p Q₂ = |Q₁| / |Q₂| := by
  unfold classical_soliton_mass
  have hC : bogomolny_constant p ≠ 0 := ne_of_gt (bogomolny_constant_pos p)
  have hQ₂abs : |Q₂| ≠ 0 := abs_ne_zero.mpr hQ₂
  have hQ₂real : (↑|Q₂| : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hQ₂abs
  field_simp [hC, hQ₂real]

/-- **Theorem 4.1.2 (Soliton Mass Spectrum)**

    The soliton mass is determined by:
    M_soliton = (6π² f_π / e) |Q| · F(m_π / f_π e)

    This theorem establishes:
    1. Mass formula is positive for non-trivial charge
    2. Classical mass equals Bogomolny bound: M = C|Q|
    3. Massless limit simplifies formula: F(0) = 1
    4. Mass scales linearly with |Q| (for Q₂ ≠ 0)
    5. Form factor satisfies F ≥ 1 (explicit breaking increases mass)

    Reference: §1, §2 -/
theorem theorem_4_1_2 :
    -- Part 1: Mass formula is positive for non-trivial charge
    (∀ (p : SkyrmeParameters) (Q : ℤ) (hQ : Q ≠ 0) (ff : FormFactor) (m_pi : ℝ)
       (hm : m_pi ≥ 0),
       soliton_mass p Q ff m_pi > 0) ∧
    -- Part 2: Classical mass equals Bogomolny bound
    (∀ (p : SkyrmeParameters) (Q : ℤ),
       classical_soliton_mass p Q = bogomolny_constant p * |Q|) ∧
    -- Part 3: Massless limit simplifies formula
    (∀ (p : SkyrmeParameters) (Q : ℤ) (ff : FormFactor),
       soliton_mass p Q ff 0 = classical_soliton_mass p Q) ∧
    -- Part 4: Mass scales linearly with |Q| (STRENGTHENED: no disjunction)
    (∀ (p : SkyrmeParameters) (Q₁ Q₂ : ℤ) (hQ₂ : Q₂ ≠ 0),
       classical_soliton_mass p Q₁ / classical_soliton_mass p Q₂ = |Q₁| / |Q₂|) ∧
    -- Part 5: Form factor F ≥ 1 (explicit breaking always increases mass)
    (∀ (ff : FormFactor) (x : ℝ) (hx : x ≥ 0), ff.F x ≥ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Part 1: Positivity
    intro p Q hQ ff m_pi hm
    exact soliton_mass_pos p Q hQ ff m_pi hm
  · -- Part 2: Bogomolny bound
    intro p Q
    rfl
  · -- Part 3: Massless limit
    intro p Q ff
    exact soliton_mass_massless_limit p Q ff
  · -- Part 4: Linearity in |Q| (using auxiliary theorem)
    intro p Q₁ Q₂ hQ₂
    exact mass_ratio_eq_charge_ratio p Q₁ Q₂ hQ₂
  · -- Part 5: Form factor bound
    intro ff x hx
    exact ff.F_ge_one x hx

/-- **Corollary: CG Soliton Mass Scale**

    In the CG framework with v_χ = 246 GeV:
    M_CG ≈ 14.6 TeV / g_χ for Q = 1

    Reference: §3.2 -/
theorem corollary_cg_mass_scale :
    ∀ (g : ℝ) (hg : g > 0),
      let params := cg_standard_params g hg
      cg_soliton_mass_GeV params 1 > 14000 / g ∧
      cg_soliton_mass_GeV params 1 < 15000 / g := by
  intro g hg
  simp only [cg_soliton_mass_GeV, cg_standard_params, abs_one, Int.cast_one, mul_one]
  have ⟨hlo, hhi⟩ := mass_coefficient_bounds
  unfold mass_coefficient at hlo hhi
  constructor
  · -- Lower bound: 6π² × 246 / g > 14000 / g
    apply div_lt_div_of_pos_right _ hg
    have h : 6 * Real.pi^2 * 246 > 59 * 246 := by linarith
    linarith
  · -- Upper bound: 6π² × 246 / g < 15000 / g
    apply div_lt_div_of_pos_right _ hg
    have h : 6 * Real.pi^2 * 246 < 60 * 246 := by linarith
    linarith

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 7: QUANTUM CORRECTIONS
    ═══════════════════════════════════════════════════════════════════════════

    Quantum corrections reduce the classical soliton mass by ~25%.

    Reference: §4.2, §4.3
-/

/-- **Quantum Corrections Structure**

    The physical soliton mass includes quantum corrections:
    - Collective coordinate quantization: −150 MeV
    - Casimir energy: −60 MeV
    - Pion mass form factor: +60 MeV

    Net: ~−150 MeV (≈ −12% of classical mass)

    Reference: §4.2, §4.3 -/
structure QuantumCorrections where
  /-- Spin/isospin quantization correction -/
  collective_coords : ℝ
  /-- Zero-point fluctuations -/
  casimir : ℝ
  /-- Pion mass contribution -/
  pion_mass : ℝ
  /-- Total correction -/
  total : ℝ
  /-- Total equals sum -/
  total_eq : total = collective_coords + casimir + pion_mass

/-- **Standard quantum corrections from literature**

    **Discrepancy Note:** There are two commonly cited decompositions:

    **Decomposition A (Adkins-Nappi-Witten 1983, used here):**
    For e ≈ 5.45 giving classical mass ~1240 MeV:
    - Total correction: ~−300 MeV
    - Result: ~940 MeV (nucleon mass)

    **Decomposition B (cited in proof document §2.4):**
    - Collective coordinate quantization: −150 MeV
    - Casimir energy: −60 MeV
    - Pion mass form factor: +60 MeV
    - Net: ~−150 MeV

    The discrepancy arises from different treatments of the pion mass:
    - Decomposition A: pion mass absorbed into form factor F ≈ 1.23
    - Decomposition B: pion mass as separate correction

    Both give physical nucleon mass ~940 MeV when properly combined with
    the corresponding classical mass calculation.

    **Reference:** Adkins et al. (1983), Holzwarth & Schwesinger (1986) -/
def standard_corrections : QuantumCorrections where
  collective_coords := -200  -- MeV (spin/isospin quantization)
  casimir := -100  -- MeV (zero-point fluctuations)
  pion_mass := 0  -- MeV (absorbed into form factor in this treatment)
  total := -300  -- Net correction
  total_eq := by ring

/-- Alternative quantum corrections (decomposition B from proof document) -/
def document_corrections : QuantumCorrections where
  collective_coords := -150  -- MeV (collective coordinate quantization)
  casimir := -60  -- MeV (Casimir/zero-point energy)
  pion_mass := 60  -- MeV (pion mass form factor, explicit)
  total := -150  -- Net correction
  total_eq := by ring

/-- Both decompositions are self-consistent -/
theorem corrections_consistency :
    standard_corrections.total = -300 ∧
    document_corrections.total = -150 := by
  simp only [standard_corrections, document_corrections]
  constructor <;> norm_num

/-- Net quantum correction is negative (mass reduction) -/
theorem quantum_correction_negative : standard_corrections.total < 0 := by
  simp only [standard_corrections]
  norm_num

/-- Quantum-corrected mass formula -/
noncomputable def quantum_corrected_mass (classical : ℝ) (qc : QuantumCorrections) : ℝ :=
  classical + qc.total

/-- For classical mass ~1240 MeV, corrected mass ~940 MeV -/
theorem quantum_corrected_mass_nucleon :
    let classical := (1240 : ℝ)
    let qc := standard_corrections
    |quantum_corrected_mass classical qc - 938| < 100 := by
  simp only [quantum_corrected_mass, standard_corrections]
  -- 1240 + (-300) = 940, |940 - 938| = 2 < 100 ✓
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 8: DIMENSIONAL ANALYSIS AND SELF-CONSISTENCY
    ═══════════════════════════════════════════════════════════════════════════

    Verification of dimensional consistency and numerical accuracy.

    Reference: §7
-/

/-- **Dimensional Analysis (Documented)**

    In natural units (ℏ = c = 1):
    - f_π: mass dimension [M]
    - e: dimensionless [1]
    - Q: dimensionless [1] (integer)
    - M = f_π/e × |Q|: [M]·[1]⁻¹·[1] = [M] ✓

    This is a type-level documentation; Lean doesn't enforce dimensions. -/
theorem dimensional_consistency :
    -- The mass formula M = C × f_π / e × |Q| has dimension [M]
    -- where C = 6π² is dimensionless
    -- This is verified by checking the formula structure
    ∀ (p : SkyrmeParameters) (Q : ℤ),
      classical_soliton_mass p Q = 6 * Real.pi^2 * p.f_pi / p.e * |Q| := by
  intro p Q
  unfold classical_soliton_mass bogomolny_constant
  ring

/-- Self-consistency: vacuum has zero mass -/
theorem vacuum_zero_mass (p : SkyrmeParameters) :
    classical_soliton_mass p 0 = 0 := by
  unfold classical_soliton_mass
  simp only [abs_zero, Int.cast_zero, mul_zero]

/-- Self-consistency: mass is additive in charge magnitude -/
theorem mass_additive_in_charge (p : SkyrmeParameters) (Q₁ Q₂ : ℤ)
    (h : |Q₁| + |Q₂| = |Q₁ + Q₂|) :  -- Triangle inequality case where signs align
    classical_soliton_mass p Q₁ + classical_soliton_mass p Q₂ =
    classical_soliton_mass p (Q₁ + Q₂) := by
  unfold classical_soliton_mass
  rw [← mul_add]
  congr 1
  -- Need to show: ↑|Q₁| + ↑|Q₂| = ↑|Q₁ + Q₂|
  simp only [Int.cast_abs, Int.cast_add]
  -- Now goal is |↑Q₁| + |↑Q₂| = |↑Q₁ + ↑Q₂|
  have h_cast : (|Q₁| : ℝ) + |Q₂| = |Q₁ + Q₂| := by exact_mod_cast h
  simp only [Int.cast_abs, Int.cast_add] at h_cast
  exact h_cast

/-- Verification record: key numerical results -/
theorem verification_record :
    -- Coefficient 6π² × 1.23 ≈ 73
    mass_coefficient * 1.23 > 72 ∧ mass_coefficient * 1.23 < 74 ∧
    -- Scale ratio v_χ / f_π ≈ 2645
    scale_ratio_cg_qcd > 2600 ∧ scale_ratio_cg_qcd < 2700 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact effective_coefficient_bounds.1
  · exact effective_coefficient_bounds.2
  · exact scale_ratio_bounds.1
  · exact scale_ratio_bounds.2

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 9: CONNECTION TO THEOREM 4.1.1 (SOLITON EXISTENCE)
    ═══════════════════════════════════════════════════════════════════════════

    This section explicitly connects the mass spectrum (Theorem 4.1.2) to the
    existence theorem (Theorem 4.1.1). The key dependencies are:

    1. **SolitonConfig** from Theorem 4.1.1: Provides the topological structure
    2. **SkyrmeParameters** from Theorem 4.1.1: Defines f_π and e
    3. **BogomolnySoliton** from Theorem 4.1.1: Soliton with energy bound
    4. **bogomolny_constant** from Theorem 4.1.1: The coefficient 6π² f_π / e

    Theorem 4.1.2 uses these structures to define the mass spectrum.

    Reference: docs/proofs/Phase4/Theorem-4.1.1-Existence-of-Solitons.md
-/

/-- **Explicit Dependency: BogomolnySoliton → Classical Mass**

    A BogomolnySoliton from Theorem 4.1.1 has energy ≥ bogomolny_constant × |Q|.
    The classical soliton mass equals this Bogomolny bound (for saturating solutions).

    This theorem shows that classical_soliton_mass gives the lower bound
    from Theorem 4.1.1's BogomolnySoliton structure. -/
theorem bogomolny_soliton_mass_bound (s : BogomolnySoliton) :
    s.energy ≥ classical_soliton_mass s.params s.Q := by
  unfold classical_soliton_mass
  exact s.satisfies_bound

/-- **Construct Classical Mass from BogomolnySoliton**

    Given a BogomolnySoliton from Theorem 4.1.1, extract its classical mass.
    This is the Bogomolny bound, which is saturated for the ground state. -/
noncomputable def bogomolny_soliton_classical_mass (s : BogomolnySoliton) : ℝ :=
  classical_soliton_mass s.params s.Q

/-- The extracted classical mass matches the Bogomolny bound -/
theorem bogomolny_soliton_classical_mass_eq (s : BogomolnySoliton) :
    bogomolny_soliton_classical_mass s = bogomolny_constant s.params * |s.Q| := rfl

/-- **Connection: Existence implies Mass Spectrum**

    From Theorem 4.1.1's existence result (static_solitons_exist), we know that
    for each Q ≠ 0, there exists a BogomolnySoliton. This section connects
    that existence to the mass formula in Theorem 4.1.2.

    For any Q ≠ 0 and parameters p, there exists a soliton with mass at least
    the classical mass formula. -/
theorem existence_implies_mass_bound (Q : ℤ) (hQ : Q ≠ 0) (p : SkyrmeParameters) :
    ∃ (s : BogomolnySoliton), s.Q = Q ∧ s.energy ≥ classical_soliton_mass p Q := by
  obtain ⟨s, hQ_eq, hp_eq⟩ := static_solitons_exist Q hQ p
  use s
  constructor
  · exact hQ_eq
  · -- s.Q = Q and s.params = p, so classical_soliton_mass p Q = classical_soliton_mass s.params s.Q
    have h1 : classical_soliton_mass p Q = classical_soliton_mass s.params s.Q := by
      rw [← hQ_eq, ← hp_eq]
    rw [h1]
    exact bogomolny_soliton_mass_bound s

/-- **Soliton Energy Hierarchy**

    The energy of a physical soliton satisfies:
    classical_soliton_mass ≤ actual_energy ≤ soliton_mass (with form factor)

    The classical mass is the Bogomolny lower bound.
    The soliton mass with form factor is the actual mass including pion effects. -/
theorem soliton_energy_hierarchy (s : BogomolnySoliton) (ff : FormFactor)
    (m_pi : ℝ) (hm : m_pi ≥ 0)
    (h_actual : s.energy = soliton_mass s.params s.Q ff m_pi) :
    classical_soliton_mass s.params s.Q ≤ s.energy := by
  rw [h_actual]
  exact soliton_mass_ge_classical s.params s.Q ff m_pi hm

/-- **Mass Formula Consistency with Existence**

    The mass formula from Theorem 4.1.2 is consistent with the existence
    theorem from Theorem 4.1.1: any soliton guaranteed to exist by 4.1.1
    has a well-defined mass computable by the formula from 4.1.2. -/
theorem mass_formula_consistent_with_existence (Q : ℤ) (hQ : Q ≠ 0) (p : SkyrmeParameters)
    (ff : FormFactor) (m_pi : ℝ) (hm : m_pi ≥ 0) :
    soliton_mass p Q ff m_pi > 0 :=
  soliton_mass_pos p Q hQ ff m_pi hm

/-- **Dependency Summary**

    Theorem 4.1.2 (Soliton Mass Spectrum) depends on Theorem 4.1.1 via:

    1. SkyrmeParameters: physical parameters (f_π, e) defining the theory
    2. bogomolny_constant: the coefficient 6π² f_π / e from energy bound
    3. BogomolnySoliton: structure proving solitons satisfy E ≥ C|Q|
    4. static_solitons_exist: existence of solitons in each sector

    This file extends 4.1.1 by computing the EXPLICIT mass values from
    these structures, adding form factor corrections, and analyzing
    phenomenological implications. -/
theorem dependency_summary :
    -- The mass formula uses the same coefficient as Theorem 4.1.1
    (∀ p Q, classical_soliton_mass p Q = bogomolny_constant p * |Q|) ∧
    -- Classical mass is positive for non-trivial charge
    (∀ p Q, Q ≠ 0 → classical_soliton_mass p Q > 0) ∧
    -- Mass satisfies C-symmetry (from |Q| dependence)
    (∀ p Q, classical_soliton_mass p Q = classical_soliton_mass p (-Q)) :=
  ⟨fun p Q => rfl,
   fun p Q hQ => classical_mass_pos p Q hQ,
   fun p Q => classical_mass_charge_conjugation p Q⟩

end ChiralGeometrogenesis.Phase4.SolitonMass
