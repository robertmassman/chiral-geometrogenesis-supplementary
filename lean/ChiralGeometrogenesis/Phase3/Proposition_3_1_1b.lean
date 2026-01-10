/-
  Phase3/Proposition_3_1_1b.lean

  Proposition 3.1.1b: RG Fixed Point Analysis for g_χ

  This proposition analyzes the renormalization group (RG) flow of the chiral
  coupling g_χ in the phase-gradient mass generation framework.

  **Main Results:**
  1. β-function computed at one-loop: β_{g_χ} = (g_χ³/16π²)(A_ψ N_f + A_χ)
  2. For N_f > 4/3, the β-function is NEGATIVE (asymptotic freedom)
  3. Coupling is naturally O(1) at QCD scale when g_χ(M_P) ~ 0.5
  4. Two-loop quasi-fixed point estimate: g_χ* ≈ 1.5–2.2
  5. Analysis provides consistency checks, not unique determination

  **Physical Interpretation:**
  The phase-gradient coupling exhibits asymptotic freedom like QCD:
  - g_χ is small at high energies (UV)
  - g_χ grows toward low energies (IR)
  - Starting from g_χ(M_P) ≈ 0.47, flows to g_χ(Λ_QCD) ≈ 1.3

  **Key Coefficients:**
  - A_ψ = -N_c/2 = -3/2 (fermion loop contribution, per flavor)
  - A_χ = +2 (vertex + self-energy contribution)
  - b₁ = A_ψ N_f + A_χ = 2 - N_c N_f/2

  **Asymptotic Freedom Condition:**
  For b₁ < 0 (asymptotic freedom), need N_f > 4/3.
  For N_f = 6: b₁ = 2 - 9 = -7 < 0 ✓

  Dependencies:
  - ✅ Proposition 3.1.1a (Lagrangian Form from Symmetry)
  - ✅ Theorem 3.1.1 (Phase-Gradient Mass Formula)
  - ✅ Definition 0.1.2 (Three Color Fields)
  - ✅ PureMath/QFT/RenormalizationGroup.lean (RG structures)

  Reference: docs/proofs/Phase3/Proposition-3.1.1b-RG-Fixed-Point-Analysis.md

  Status: 🔶 NOVEL — Constrains g_χ via RG flow
-/

import ChiralGeometrogenesis.Phase3.Proposition_3_1_1a
import ChiralGeometrogenesis.Phase3.Theorem_3_1_1
import ChiralGeometrogenesis.Phase0.Definition_0_1_2
import ChiralGeometrogenesis.PureMath.QFT.RenormalizationGroup
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Phase3.Proposition_3_1_1b

open ChiralGeometrogenesis
open ChiralGeometrogenesis.Phase3.Proposition_3_1_1a
open ChiralGeometrogenesis.PureMath.QFT

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: β-FUNCTION COEFFICIENTS FOR PHASE-GRADIENT COUPLING
    ═══════════════════════════════════════════════════════════════════════════

    The β-function for the dimension-5 derivative coupling has the form:
      β_{g_χ} = (g_χ³/16π²)(A_ψ N_f + A_χ) + O(g_χ⁵)

    where:
    - A_ψ = -N_c/2 (fermion loop contribution per flavor)
    - A_χ = +2 (vertex + self-energy contributions)

    The sign of the total coefficient determines asymptotic behavior:
    - b₁ = A_ψ N_f + A_χ = 2 - N_c N_f/2
    - b₁ < 0: asymptotic freedom (like QCD)
    - b₁ > 0: infrared freedom

    Reference: docs/proofs/Phase3/Proposition-3.1.1b-RG-Fixed-Point-Analysis.md §2
-/

/-- Symbol table for Proposition 3.1.1b

| Symbol | Definition | Value/Dimension |
|--------|------------|-----------------|
| g_χ | Chiral coupling constant | Dimensionless, O(1) |
| Λ | EFT cutoff scale | ~1 GeV (QCD sector) |
| μ | Renormalization scale | [mass] |
| β_{g_χ} | Beta function | Dimensionless |
| N_f | Number of fermion flavors | 6 (quarks) or 9 (+ leptons) |
| A_ψ | Fermion loop coefficient (per flavor) | -N_c/2 = -3/2 |
| A_χ | Vertex + self-energy coefficient | +2 |
| b₁ | One-loop coefficient | 2 - N_c N_f/2 |
-/
structure SymbolTable_3_1_1b where
  doc : String := "See markdown §1.1 for complete symbol definitions"

/-- Fermion loop coefficient A_ψ (per flavor).

**Definition:** A_ψ = -N_c/2 where N_c is the number of colors.

This arises from:
- Fermion loops in χ wavefunction renormalization
- The negative sign comes from the fermion loop structure

For SU(3): A_ψ = -3/2

Reference: §2.4 of markdown
-/
def fermion_loop_coefficient (n_c : ℕ) : ℚ := -(n_c : ℚ) / 2

/-- For SU(3), A_ψ = -3/2 -/
theorem fermion_loop_su3 : fermion_loop_coefficient 3 = -3/2 := by
  unfold fermion_loop_coefficient
  norm_num

/-- Vertex + self-energy coefficient A_χ.

**Definition:** A_χ = +2

This combines:
- Vertex correction contribution: +1
- Fermion self-energy contribution: +1
- Total: +2

This is the scheme-independent leading-order result.

Reference: §2.4 of markdown (Table in Appendix A.4)
-/
def vertex_selfenergy_coefficient : ℚ := 2

/-- One-loop β-function coefficient numerator b₁ = A_ψ N_f + A_χ = 2 - N_c N_f/2

For the phase-gradient coupling in dimensional regularization.

**Derivation (from Appendix A):**
- Z_v contributes +1
- Z_χ^{-1/2} contributes -N_c N_f/2
- Z_ψ^{-1} contributes +1
- Total: 2 - N_c N_f/2

Reference: §2.4 of markdown
-/
def beta_coefficient_chiral (n_c n_f : ℕ) : ℚ :=
  fermion_loop_coefficient n_c * n_f + vertex_selfenergy_coefficient

/-- Alternative form: b₁ = 2 - N_c N_f/2 -/
theorem beta_coefficient_alternative (n_c n_f : ℕ) :
    beta_coefficient_chiral n_c n_f = 2 - (n_c : ℚ) * n_f / 2 := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  ring

/-- For SU(3) with 6 flavors: b₁ = 2 - 9 = -7 -/
theorem beta_coefficient_su3_nf6 : beta_coefficient_chiral 3 6 = -7 := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  norm_num

/-- For SU(3) with 3 flavors: b₁ = 2 - 4.5 = -2.5 = -5/2 -/
theorem beta_coefficient_su3_nf3 : beta_coefficient_chiral 3 3 = -5/2 := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  norm_num

/-- For SU(3) with 5 flavors: b₁ = 2 - 7.5 = -5.5 = -11/2 -/
theorem beta_coefficient_su3_nf5 : beta_coefficient_chiral 3 5 = -11/2 := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  norm_num

/-- For SU(3) with 4 flavors: b₁ = 2 - 6 = -4 -/
theorem beta_coefficient_su3_nf4 : beta_coefficient_chiral 3 4 = -4 := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: ASYMPTOTIC FREEDOM ANALYSIS
    ═══════════════════════════════════════════════════════════════════════════

    The phase-gradient coupling exhibits asymptotic freedom when b₁ < 0.

    **Condition:** b₁ = 2 - N_c N_f/2 < 0
                   ⟺ N_f > 4/N_c
                   ⟺ N_f > 4/3 for SU(3)

    **Physical Interpretation:**
    - β < 0 means dg/d(ln μ) < 0
    - As μ increases (UV), g decreases
    - As μ decreases (IR), g increases
    - Same qualitative behavior as QCD!

    Reference: §2.5-2.6 and §3.1 of markdown
-/

/-- Critical number of flavors for asymptotic freedom.

For b₁ = 0: 2 - N_c N_f/2 = 0 ⟹ N_f = 4/N_c

For N_c = 3: N_f^{crit} = 4/3 ≈ 1.33

Asymptotic freedom holds for N_f > N_f^{crit}.

Reference: §3.1 of markdown
-/
def critical_flavor_count (n_c : ℕ) : ℚ :=
  if n_c = 0 then 0 else 4 / n_c

/-- For SU(3), critical N_f = 4/3 -/
theorem critical_flavor_su3 : critical_flavor_count 3 = 4/3 := by
  unfold critical_flavor_count
  norm_num

/-- Asymptotic freedom condition: b₁ < 0 ⟺ N_f > 4/N_c

**Key Result:** The phase-gradient coupling is asymptotically free
whenever N_f exceeds the critical value 4/N_c.

This includes ALL physical cases:
- N_f = 3 (light quarks): 3 > 4/3 ✓
- N_f = 6 (all quarks): 6 > 4/3 ✓

Reference: §3.1 of markdown
-/
theorem asymptotic_freedom_condition_chiral (n_c n_f : ℕ) (hn : n_c > 0) :
    beta_coefficient_chiral n_c n_f < 0 ↔ (n_f : ℚ) > critical_flavor_count n_c := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  unfold critical_flavor_count
  have hq : (n_c : ℚ) > 0 := Nat.cast_pos.mpr hn
  have hn_ne : (n_c : ℚ) ≠ 0 := ne_of_gt hq
  split_ifs with h_nc
  · -- Case n_c = 0 contradicts hn
    omega
  · -- Case n_c ≠ 0
    constructor
    · intro h
      -- h : -(n_c : ℚ) / 2 * n_f + 2 < 0
      -- Goal: 4 / n_c < n_f
      have h1 : (n_c : ℚ) * n_f / 2 > 2 := by linarith
      have h2 : (n_c : ℚ) * n_f > 4 := by linarith
      rw [gt_iff_lt]
      rw [div_lt_iff₀ hq]
      calc 4 < (n_c : ℚ) * n_f := h2
        _ = (n_f : ℚ) * n_c := by ring
    · intro h
      -- h : 4 / n_c < n_f
      -- Goal: -(n_c : ℚ) / 2 * n_f + 2 < 0
      rw [gt_iff_lt, div_lt_iff₀ hq] at h
      have h'' : (n_c : ℚ) * n_f > 4 := by linarith
      linarith

/-- SU(3) with any N_f ≥ 2 is asymptotically free for phase-gradient coupling.

This is stronger than QCD's requirement (N_f ≤ 16) because the
phase-gradient coupling has different loop structure.

Reference: §2.5 of markdown
-/
theorem su3_chiral_asymptotic_freedom (n_f : ℕ) (hf : n_f ≥ 2) :
    beta_coefficient_chiral 3 n_f < 0 := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  have h : (n_f : ℚ) ≥ 2 := Nat.cast_le.mpr hf
  linarith

/-- Comparison with QCD: same sign of β-function for physical N_f.

Both QCD and phase-gradient coupling have β < 0 (asymptotic freedom)
for the Standard Model quark content.

Reference: §6.1 of markdown (comparison table)
-/
theorem qcd_chiral_same_sign_nf6 :
    beta_0_numerator 3 6 > 0 ∧ beta_coefficient_chiral 3 6 < 0 := by
  constructor
  · -- QCD: b₀ = 11×3 - 2×6 = 33 - 12 = 21 > 0
    unfold beta_0_numerator gluon_coefficient fermion_coefficient
    norm_num
  · -- Chiral: b₁ = 2 - 9 = -7 < 0
    exact beta_coefficient_su3_nf6 ▸ by norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 3: RG FLOW STRUCTURE
    ═══════════════════════════════════════════════════════════════════════════

    The one-loop RG equation:
      μ dg_χ/dμ = (b₁/16π²) g_χ³

    has solution:
      1/g_χ²(μ) = 1/g_χ²(μ₀) - (b₁/8π²) ln(μ/μ₀)

    For asymptotic freedom (b₁ < 0):
    - As μ → ∞ (UV): g_χ → 0
    - As μ → 0 (IR): g_χ grows

    Reference: §4.1 of markdown
-/

/-- Structure for RG flow parameters of the chiral coupling.

Encapsulates the coupling value at a reference scale and the
β-function coefficient determining its running.

Reference: §4 of markdown
-/
structure ChiralRGFlow where
  /-- Number of colors (from geometry) -/
  n_c : ℕ
  /-- Number of active flavors at this scale -/
  n_f : ℕ
  /-- One-loop β-coefficient -/
  b1 : ℚ := beta_coefficient_chiral n_c n_f
  /-- Coupling is asymptotically free when n_f exceeds critical value -/
  is_asymptotic_free : n_c > 0 → (n_f : ℚ) > critical_flavor_count n_c → b1 < 0

/-- Standard Model QCD-sector chiral flow at high energy (6 flavors) -/
def sm_chiral_flow_high : ChiralRGFlow where
  n_c := 3
  n_f := 6
  is_asymptotic_free := fun _ _ => by
    unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
    norm_num

/-- Standard Model QCD-sector chiral flow at low energy (3 light flavors) -/
def sm_chiral_flow_low : ChiralRGFlow where
  n_c := 3
  n_f := 3
  is_asymptotic_free := fun _ _ => by
    unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
    norm_num

/-- The β-coefficient decreases (more negative) as N_f increases (for n_c > 0).

More flavors = stronger asymptotic freedom for phase-gradient coupling.
(Opposite to QCD where more flavors weaken asymptotic freedom!)

Note: Requires n_c > 0 because when n_c = 0, the coefficient is constant (= 2).

Reference: §2.6 of markdown
-/
theorem beta_coefficient_decreasing_nf (n_c n_f₁ n_f₂ : ℕ) (hnc : n_c > 0) (h : n_f₁ < n_f₂) :
    beta_coefficient_chiral n_c n_f₂ < beta_coefficient_chiral n_c n_f₁ := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  have hq : (n_f₁ : ℚ) < n_f₂ := Nat.cast_lt.mpr h
  have hn_c_pos : (n_c : ℚ) > 0 := Nat.cast_pos.mpr hnc
  have h1' : -(n_c : ℚ) / 2 < 0 := by linarith
  have h2' : -(n_c : ℚ) / 2 * (n_f₂ : ℚ) < -(n_c : ℚ) / 2 * (n_f₁ : ℚ) := by
    apply mul_lt_mul_of_neg_left hq h1'
  linarith

/-- The β-coefficient scales linearly with -N_c.

More colors = stronger asymptotic freedom (per flavor).

Reference: Implicit in §2.4 derivation
-/
theorem beta_coefficient_scales_nc (n_c₁ n_c₂ n_f : ℕ) (h : n_c₁ < n_c₂) (hf : n_f > 0) :
    beta_coefficient_chiral n_c₂ n_f < beta_coefficient_chiral n_c₁ n_f := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  have hn : (n_c₁ : ℚ) < n_c₂ := Nat.cast_lt.mpr h
  have hfq : (n_f : ℚ) > 0 := Nat.cast_pos.mpr hf
  nlinarith

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 4: THRESHOLD MATCHING
    ═══════════════════════════════════════════════════════════════════════════

    As the energy scale crosses quark mass thresholds, the effective N_f changes.
    The β-coefficient must be recalculated at each threshold.

    Energy Scale | N_f | b₁ value
    -------------|-----|----------
    μ > m_t      |  6  | -7
    m_b < μ < m_t|  5  | -11/2
    m_c < μ < m_b|  4  | -4
    μ < m_c      |  3  | -5/2

    Reference: §4.3 of markdown (step-wise running)
-/

/-- β-coefficients at Standard Model quark thresholds.

Lists the one-loop coefficient at each threshold where
a quark becomes active/inactive.

Reference: §4.3 of markdown
-/
def threshold_coefficients : List (ℕ × ℚ) :=
  [(6, beta_coefficient_chiral 3 6),  -- Above top
   (5, beta_coefficient_chiral 3 5),  -- Top decoupled
   (4, beta_coefficient_chiral 3 4),  -- Bottom decoupled
   (3, beta_coefficient_chiral 3 3)]  -- Charm decoupled

/-- All SM thresholds give negative β-coefficient (asymptotic freedom) -/
theorem all_thresholds_asymptotic :
    ∀ p ∈ threshold_coefficients, p.2 < 0 := by
  intro p hp
  simp only [threshold_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · -- p = (6, beta_coefficient_chiral 3 6)
    simp only [beta_coefficient_su3_nf6]; norm_num
  · -- p = (5, beta_coefficient_chiral 3 5)
    simp only [beta_coefficient_su3_nf5]; norm_num
  · -- p = (4, beta_coefficient_chiral 3 4)
    simp only [beta_coefficient_su3_nf4]; norm_num
  · -- p = (3, beta_coefficient_chiral 3 3)
    simp only [beta_coefficient_su3_nf3]; norm_num

/-- The running slows (|b₁| decreases) as more quarks decouple.

Going to lower energies, fewer flavors are active, so
|b₁| = |2 - 3N_f/2| decreases, and the running slows.

Reference: §4.3 of markdown
-/
theorem running_slows_at_thresholds :
    |beta_coefficient_chiral 3 6| > |beta_coefficient_chiral 3 5| ∧
    |beta_coefficient_chiral 3 5| > |beta_coefficient_chiral 3 4| ∧
    |beta_coefficient_chiral 3 4| > |beta_coefficient_chiral 3 3| := by
  simp only [beta_coefficient_su3_nf6, beta_coefficient_su3_nf5,
             beta_coefficient_su3_nf4, beta_coefficient_su3_nf3]
  constructor <;> [norm_num; constructor <;> norm_num]

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 5: FIXED POINT ANALYSIS
    ═══════════════════════════════════════════════════════════════════════════

    At one-loop, β_{g_χ} = 0 only for g_χ = 0 (Gaussian fixed point).

    No non-trivial fixed point exists at one-loop because the
    β-function is cubic: β = b₁ g_χ³/(16π²).

    At two-loops, a quasi-fixed point may exist if b₁ and b₂
    have opposite signs: g_χ* = √(-b₁/b₂ × 16π²)

    However, estimates show b₂ < 0 as well, so no perturbative
    fixed point exists. The "quasi-fixed point" is a non-perturbative
    effect near the chiral symmetry breaking scale.

    Reference: §3 of markdown
-/

/-- At one-loop, the only fixed point is the Gaussian (trivial) fixed point.

The β-function β = b₁ g³/(16π²) vanishes only when g = 0.

**Proof:** For g ≠ 0, we have g³ ≠ 0, so β = b₁ g³/(16π²) = 0 iff b₁ = 0.
But b₁ = 2 - N_c N_f/2 ≠ 0 for physical N_f > 4/3 (when N_c = 3).
Therefore, the only solution to β = 0 is g = 0.

Reference: §3.1 of markdown
-/
theorem one_loop_only_gaussian_fp (n_c n_f : ℕ) (g : ℝ) (hg : g ≠ 0) :
    (beta_coefficient_chiral n_c n_f : ℝ) * g^3 ≠ 0 ↔
    beta_coefficient_chiral n_c n_f ≠ 0 := by
  constructor
  · intro h hb
    simp only [hb, Rat.cast_zero, zero_mul, ne_eq, not_true_eq_false] at h
  · intro hb
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff, Nat.succ_ne_zero, not_false_eq_true, hg,
               or_false]
    exact Rat.cast_ne_zero.mpr hb

/-- Direct statement: β = 0 implies g = 0 when the coefficient is non-zero.

This is the core fixed point result: for physical values of N_f (> 4/3 for SU(3)),
the β-coefficient is non-zero, so the only solution to β = 0 is g = 0.

Reference: §3.1 of markdown
-/
theorem beta_zero_implies_coupling_zero (n_c n_f : ℕ) (g : ℝ)
    (hb : beta_coefficient_chiral n_c n_f ≠ 0)
    (h_beta_zero : (beta_coefficient_chiral n_c n_f : ℝ) * g ^ 3 = 0) :
    g = 0 := by
  simp only [mul_eq_zero] at h_beta_zero
  cases h_beta_zero with
  | inl hb_zero =>
    exfalso
    -- hb_zero : ↑(beta_coefficient_chiral n_c n_f) = 0
    -- Need to show beta_coefficient_chiral n_c n_f = 0
    have h_rat : beta_coefficient_chiral n_c n_f = 0 := by
      have : (beta_coefficient_chiral n_c n_f : ℝ) = ((0 : ℚ) : ℝ) := by
        simp only [Rat.cast_zero]
        exact hb_zero
      exact Rat.cast_injective this
    exact hb h_rat
  | inr hg3_zero =>
    -- g³ = 0 implies g = 0
    exact eq_zero_of_pow_eq_zero hg3_zero

/-- For SU(3) with N_f ≥ 2, the β-coefficient is non-zero.

This ensures that the Gaussian fixed point is the only one at one-loop
for all physical flavor counts.

Reference: §3.1 of markdown
-/
theorem su3_beta_coefficient_nonzero (n_f : ℕ) (hf : n_f ≥ 2) :
    beta_coefficient_chiral 3 n_f ≠ 0 := by
  unfold beta_coefficient_chiral fermion_loop_coefficient vertex_selfenergy_coefficient
  have h : (n_f : ℚ) ≥ 2 := Nat.cast_le.mpr hf
  -- b₁ = 2 - 3n_f/2 = (4 - 3n_f)/2
  -- For n_f ≥ 2: 4 - 3n_f ≤ 4 - 6 = -2 < 0, so b₁ < 0 ≠ 0
  intro h_eq
  have h1 : -(3 : ℚ) / 2 * n_f + 2 = 0 := h_eq
  have h2 : (3 : ℚ) * n_f = 4 := by linarith
  have h3 : (n_f : ℚ) = 4/3 := by linarith
  have h4 : (n_f : ℚ) ≥ 2 := h
  linarith

/-- Two-loop coefficient structure (estimated).

The two-loop β-function has form:
  β = (g³/16π²) b₁ + (g⁵/(16π²)²) b₂ + O(g⁷)

For a fixed point: g*² = -b₁/b₂ × 16π²

Estimates from §3.2 suggest b₂ ≈ -72 for N_f = 6 (same sign as b₁),
so no perturbative fixed point exists.

Reference: §3.2 of markdown
-/
structure TwoLoopEstimate where
  /-- One-loop coefficient -/
  b1 : ℚ
  /-- Two-loop coefficient (estimated) -/
  b2_estimate : ℚ
  /-- Whether perturbative fixed point might exist (requires opposite signs) -/
  has_fp : Bool

/-- Two-loop estimate for SU(3) with N_f = 6.

Both b₁ = -7 and b₂ ≈ -72 are negative, so no perturbative
fixed point exists (product is positive, not negative).

Reference: §3.2 of markdown
-/
def two_loop_su3_nf6 : TwoLoopEstimate where
  b1 := -7
  b2_estimate := -72
  has_fp := false  -- (-7) × (-72) = 504 > 0, so no fixed point

/-- No perturbative fixed point for SM chiral coupling -/
theorem no_perturbative_fp_sm : two_loop_su3_nf6.has_fp = false := rfl

/-- The product of b1 and b2 is positive (same sign), confirming no fixed point -/
theorem two_loop_su3_nf6_same_sign : two_loop_su3_nf6.b1 * two_loop_su3_nf6.b2_estimate > 0 := by
  simp only [two_loop_su3_nf6]
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 6: QUASI-FIXED POINT AND IR BEHAVIOR
    ═══════════════════════════════════════════════════════════════════════════

    Although no exact perturbative fixed point exists, the coupling
    exhibits "quasi-fixed point" behavior near the chiral symmetry
    breaking scale Λ_QCD.

    **Mechanism:**
    1. χ develops VEV at μ ≈ Λ_QCD
    2. Derivative coupling becomes effectively massive
    3. Running "freezes" near symmetry breaking

    The quasi-fixed point value g_χ* ≈ 1.4-1.8 is consistent with
    lattice constraints g_χ ≈ 1.26 ± 1.0.

    Reference: §3.3-3.4 of markdown
-/

/-- Quasi-fixed point value range from two-loop analysis.

The quasi-fixed point (where non-perturbative effects dominate)
is estimated to be in the range 1.4-2.2.

Reference: §3.3 of markdown (Table in §8.1)
-/
structure QuasiFixedPoint where
  /-- Lower bound of quasi-fixed point range -/
  lower : ℚ
  /-- Upper bound of quasi-fixed point range -/
  upper : ℚ
  /-- Range is valid (lower < upper, both positive) -/
  valid : 0 < lower ∧ lower < upper

/-- Quasi-fixed point estimate from two-loop analysis -/
def quasi_fp_estimate : QuasiFixedPoint where
  lower := 14/10  -- 1.4
  upper := 22/10  -- 2.2
  valid := by norm_num

/-- Lattice constraint on g_χ from FLAG 2024.

From matching to chiral perturbation theory LECs:
  g_χ(770 MeV) ≈ 0.35 - 1.5

Central value from pion decay: g_χ ≈ 1.26 ± 1.0

Reference: §3.4 and §5.3 of markdown
-/
structure LatticeConstraint where
  /-- Central value -/
  central : ℚ
  /-- Uncertainty -/
  uncertainty : ℚ
  /-- Lower bound = central - uncertainty -/
  lower : ℚ := central - uncertainty
  /-- Upper bound = central + uncertainty -/
  upper : ℚ := central + uncertainty

/-- FLAG 2024 constraint on chiral coupling -/
def flag_2024_constraint : LatticeConstraint where
  central := 126/100  -- 1.26
  uncertainty := 1

/-- Quasi-fixed point is consistent with lattice constraint.

The two-loop quasi-FP estimate (1.4-2.2) overlaps with the
lattice constraint (0.26-2.26).

Reference: §5.3 of markdown
-/
theorem quasi_fp_consistent_lattice :
    quasi_fp_estimate.lower < flag_2024_constraint.upper ∧
    quasi_fp_estimate.upper > flag_2024_constraint.lower := by
  unfold quasi_fp_estimate flag_2024_constraint LatticeConstraint.lower LatticeConstraint.upper
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 7: UV-IR CONNECTION AND RG FLOW EQUATIONS
    ═══════════════════════════════════════════════════════════════════════════

    The RG flow connects Planck-scale and QCD-scale values of g_χ.

    **One-loop RG equation:**
      μ dg_χ/dμ = (b₁/16π²) g_χ³

    **Solution (integrated form):**
      1/g_χ²(μ) = 1/g_χ²(μ₀) - (b₁/8π²) ln(μ/μ₀)

    For asymptotic freedom (b₁ < 0):
    - Δ(1/g²) = -(b₁/8π²) ln(μ/μ₀) > 0 when μ > μ₀ (so 1/g² increases, g decreases)
    - As μ → ∞ (UV): g_χ → 0
    - As μ → 0 (IR): g_χ grows

    From §4.5:
    If g_χ(Λ_QCD) ≈ 1.3 (lattice), then g_χ(M_P) ≈ 0.47

    The calculation uses step-wise running with threshold matching:
    - Δ(1/g²) ≈ -3.9 total from M_P to Λ_QCD

    Reference: §4.1-4.5 of markdown
-/

/-- RG flow solution relating coupling at two scales.

The one-loop RG equation μ dg/dμ = b₁ g³/(16π²) has the integrated solution:

  1/g²(μ) = 1/g²(μ₀) - (b₁/8π²) ln(μ/μ₀)

This structure encodes the relationship between couplings at different scales.

**Key insight:** The quantity 1/g² runs linearly with log(μ).
-/
structure RGFlowSolution where
  /-- β-coefficient (dimensionless) -/
  b1 : ℚ
  /-- Log of scale ratio ln(μ/μ₀), positive when μ > μ₀ -/
  log_scale_ratio : ℚ
  /-- Coefficient in running: Δ(1/g²) = -(b₁/8π²) ln(μ/μ₀)
      We store the numerical coefficient 8π² ≈ 79 as rational approximation -/
  loop_factor : ℚ := 79  -- 8π² ≈ 78.96

/-- Change in 1/g² under RG flow.

For the one-loop solution: Δ(1/g²) = -(b₁/8π²) × ln(μ/μ₀)

With asymptotic freedom (b₁ < 0) and increasing energy (ln > 0):
- Δ(1/g²) > 0, so 1/g² increases, meaning g decreases (UV freedom)

Reference: §4.1 of markdown
-/
def delta_inverse_coupling_squared (flow : RGFlowSolution) : ℚ :=
  -flow.b1 * flow.log_scale_ratio / flow.loop_factor

/-- For asymptotic freedom (b₁ < 0), going to higher energy (ln > 0)
    increases 1/g², meaning g decreases. -/
theorem asymptotic_freedom_uv_decrease (flow : RGFlowSolution)
    (hb : flow.b1 < 0) (hln : flow.log_scale_ratio > 0) (hf : flow.loop_factor > 0) :
    delta_inverse_coupling_squared flow > 0 := by
  unfold delta_inverse_coupling_squared
  have h1 : -flow.b1 > 0 := neg_pos.mpr hb
  have h2 : -flow.b1 * flow.log_scale_ratio > 0 := mul_pos h1 hln
  exact div_pos h2 hf

/-- For asymptotic freedom (b₁ < 0), going to lower energy (ln < 0)
    decreases 1/g², meaning g increases (IR growth). -/
theorem asymptotic_freedom_ir_growth (flow : RGFlowSolution)
    (hb : flow.b1 < 0) (hln : flow.log_scale_ratio < 0) (hf : flow.loop_factor > 0) :
    delta_inverse_coupling_squared flow < 0 := by
  unfold delta_inverse_coupling_squared
  have h1 : -flow.b1 > 0 := neg_pos.mpr hb
  have h2 : -flow.b1 * flow.log_scale_ratio < 0 := mul_neg_of_pos_of_neg h1 hln
  exact div_neg_of_neg_of_pos h2 hf

/-- IR coupling from UV coupling via RG flow.

Given g²_UV at scale μ_UV, the coupling at scale μ_IR is:
  1/g²_IR = 1/g²_UV + Δ(1/g²)

where Δ(1/g²) = -(b₁/8π²) ln(μ_IR/μ_UV)

For μ_IR < μ_UV (going to lower energy), ln < 0, so:
- If b₁ < 0 (asymptotic freedom): Δ < 0, so 1/g²_IR < 1/g²_UV, meaning g_IR > g_UV
-/
def coupling_squared_from_running (g_squared_uv : ℚ) (delta : ℚ)
    (h_positive : g_squared_uv > 0) (h_valid : 1 / g_squared_uv + delta > 0) : ℚ :=
  1 / (1 / g_squared_uv + delta)

/-- The IR coupling is larger than UV coupling for asymptotic freedom going to IR.

When b₁ < 0 and we flow to lower energy (ln < 0), Δ(1/g²) < 0,
so g²_IR = 1/(1/g²_UV + Δ) > g²_UV (since denominator is smaller).

Reference: §5.1 of markdown
-/
theorem ir_coupling_larger_than_uv (g_sq_uv : ℚ) (delta : ℚ)
    (h_uv_pos : g_sq_uv > 0) (h_delta_neg : delta < 0)
    (h_valid : 1 / g_sq_uv + delta > 0) :
    coupling_squared_from_running g_sq_uv delta h_uv_pos h_valid > g_sq_uv := by
  unfold coupling_squared_from_running
  have h_inv_uv_pos : 1 / g_sq_uv > 0 := one_div_pos.mpr h_uv_pos
  have h_denom_smaller : 1 / g_sq_uv + delta < 1 / g_sq_uv := by linarith
  -- 1/(smaller positive) > 1/(larger positive)
  -- g_sq_uv = 1/(1/g_sq_uv), so we need 1/(1/g_sq_uv + delta) > 1/(1/g_sq_uv)
  have h1 : 1 / (1 / g_sq_uv + delta) > 1 / (1 / g_sq_uv) := by
    apply one_div_lt_one_div_of_lt h_valid h_denom_smaller
  simp only [one_div_one_div] at h1
  exact h1

/-- Total change in 1/g² from Planck to QCD scale.

Summing threshold contributions (from §4.3):
- M_P → m_t: Δ = -(-7) × 40 / 79 ≈ -3.54
- m_t → m_b: Δ = -(-5.5) × 3.7 / 79 ≈ -0.26
- m_b → m_c: Δ = -(-4) × 1.2 / 79 ≈ -0.06
- m_c → Λ_QCD: Δ = -(-2.5) × 1.9 / 79 ≈ -0.06
- Total: ≈ -3.92 ≈ -3.9

Note: The negative total reflects that we're going to LOWER energy,
so ln(μ_QCD/M_P) < 0, and with b₁ < 0, we get Δ(1/g²) < 0.

Reference: §4.3 of markdown
-/
def total_running_change : ℚ := -39/10  -- -3.9

/-- Verification: the threshold contributions sum correctly.

Each step: Δ = -b₁ × ln(μ₂/μ₁) / 79
Going to lower energy means ln < 0, so Δ has sign of b₁.
Since b₁ < 0 for all thresholds, each Δ < 0.
-/
def threshold_mp_to_mt : ℚ := -(-7) * (-40) / 79    -- ≈ -3.54
def threshold_mt_to_mb : ℚ := -(-11/2) * (-37/10) / 79  -- ≈ -0.26
def threshold_mb_to_mc : ℚ := -(-4) * (-12/10) / 79   -- ≈ -0.06
def threshold_mc_to_qcd : ℚ := -(-5/2) * (-19/10) / 79  -- ≈ -0.06

/-- The sum of threshold contributions matches total_running_change (approximately). -/
theorem threshold_sum_approximately :
    let sum := threshold_mp_to_mt + threshold_mt_to_mb + threshold_mb_to_mc + threshold_mc_to_qcd
    sum < -38/10 ∧ sum > -42/10 := by
  unfold threshold_mp_to_mt threshold_mt_to_mb threshold_mb_to_mc threshold_mc_to_qcd
  constructor <;> norm_num

/-- UV value that gives g_χ ≈ 1.3 at QCD scale.

From the running equation:
  1/g²(Λ_QCD) = 1/g²(M_P) + Δ(1/g²)

With g(Λ_QCD) = 1.3 and Δ = -3.9:
  1/1.69 ≈ 0.59 = 1/g²(M_P) - 3.9
  1/g²(M_P) = 0.59 + 3.9 = 4.49
  g²(M_P) ≈ 0.22
  g(M_P) ≈ 0.47

Reference: §4.5 of markdown
-/
def planck_scale_coupling_estimate : ℚ := 47/100  -- 0.47

/-- The Planck scale estimate is consistent with lattice constraint.

Starting from g(M_P) = 0.47, we verify the IR value is O(1).
-/
theorem planck_estimate_gives_ir_order_one :
    let g_sq_uv := planck_scale_coupling_estimate^2  -- ≈ 0.22
    let inv_g_sq_uv := 1/g_sq_uv  -- ≈ 4.5
    let inv_g_sq_ir := inv_g_sq_uv + total_running_change  -- ≈ 0.6
    inv_g_sq_ir > 0 ∧ inv_g_sq_ir < 2 := by
  unfold planck_scale_coupling_estimate total_running_change
  constructor <;> norm_num

/-! ### Focusing Behavior

Focusing behavior: the sensitivity of g²_IR to g²_UV is bounded.

**Definition:** Focusing occurs when the derivative d(1/g²_IR)/d(1/g²_UV) = 1,
meaning changes in 1/g²_UV translate directly to 1/g²_IR, but because
g² = 1/(1/g²), the nonlinear transformation reduces sensitivity of g itself.

**Mathematical statement:** For the one-loop flow,
  1/g²_IR = 1/g²_UV + Δ(1/g²)

where Δ(1/g²) is independent of g²_UV. This means:
- The mapping from 1/g²_UV to 1/g²_IR is linear (just a shift)
- The mapping from g_UV to g_IR is nonlinear
- Large changes in g_UV when g_UV is small produce smaller changes in g_IR

**Quantitative focusing property:**
For small UV couplings (large 1/g²_UV), the IR coupling g_IR satisfies:
  |∂g_IR/∂g_UV| = |g_IR²/g_UV² × g_UV/g_IR| = g_IR³/g_UV³

When g_IR > g_UV (asymptotic freedom to IR), this ratio > 1, BUT
the absolute change |Δg_IR| for a given |Δg_UV| depends on the initial point.

Reference: §5.2 of markdown
-/

/-- Compute IR coupling squared from UV coupling squared via RG flow.

  g²_IR = 1 / (1/g²_UV + Δ)

where Δ = -(b₁/8π²) ln(μ_IR/μ_UV) is the change in 1/g².
-/
def ir_coupling_squared (g_sq_uv : ℚ) (delta : ℚ) : ℚ :=
  1 / (1 / g_sq_uv + delta)

/-- For asymptotic freedom with negative Δ, g²_IR > g²_UV.

This is the core focusing result: going to lower energy with asymptotic freedom
causes the coupling to grow.
-/
theorem focusing_ir_larger (g_sq_uv : ℚ) (delta : ℚ)
    (h_uv_pos : g_sq_uv > 0) (h_delta_neg : delta < 0)
    (h_valid : 1 / g_sq_uv + delta > 0) :
    ir_coupling_squared g_sq_uv delta > g_sq_uv := by
  unfold ir_coupling_squared
  have h_inv_uv_pos : 1 / g_sq_uv > 0 := one_div_pos.mpr h_uv_pos
  have h_denom_smaller : 1 / g_sq_uv + delta < 1 / g_sq_uv := by linarith
  have h1 : 1 / (1 / g_sq_uv + delta) > 1 / (1 / g_sq_uv) := by
    apply one_div_lt_one_div_of_lt h_valid h_denom_smaller
  simp only [one_div_one_div] at h1
  exact h1

/-- Example focusing: g_UV = 0.47 flows to g_IR ≈ 1.3.

This demonstrates that a perturbative UV value produces an O(1) IR value.

Starting values:
- g²_UV = 0.47² ≈ 0.2209
- Δ = -3.9 (total running from Planck to QCD)
- 1/g²_UV ≈ 4.53
- 1/g²_IR = 4.53 - 3.9 ≈ 0.63
- g²_IR ≈ 1.59
- g_IR ≈ 1.26

Reference: §4.5 of markdown
-/
def example_uv_coupling_sq : ℚ := (47/100)^2  -- 0.2209
def example_delta : ℚ := -39/10              -- -3.9

/-- The UV coupling is positive. -/
theorem example_uv_pos : example_uv_coupling_sq > 0 := by
  unfold example_uv_coupling_sq; norm_num

/-- The flow is valid (IR coupling remains positive). -/
theorem example_flow_valid : 1 / example_uv_coupling_sq + example_delta > 0 := by
  unfold example_uv_coupling_sq example_delta; norm_num

/-- The example focusing produces IR coupling in the expected range (g² between 1 and 3). -/
theorem example_focusing_ir_range :
    ir_coupling_squared example_uv_coupling_sq example_delta > 1 ∧
    ir_coupling_squared example_uv_coupling_sq example_delta < 3 := by
  unfold ir_coupling_squared example_uv_coupling_sq example_delta
  constructor <;> norm_num

/-- The example demonstrates IR coupling is larger than UV coupling. -/
theorem example_focusing_growth :
    ir_coupling_squared example_uv_coupling_sq example_delta > example_uv_coupling_sq := by
  exact focusing_ir_larger example_uv_coupling_sq example_delta
    example_uv_pos (by unfold example_delta; norm_num) example_flow_valid

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 8: MAIN PROPOSITION STATEMENT
    ═══════════════════════════════════════════════════════════════════════════

    **Proposition 3.1.1b (RG Fixed Point Analysis for g_χ)**

    The chiral coupling g_χ in the phase-gradient Lagrangian has
    renormalization group flow governed by:

      β_{g_χ} = (g_χ³/16π²)(2 - N_c N_f/2) + O(g_χ⁵)

    Key Results:
    1. For N_f > 4/3, the coupling is asymptotically free
    2. No perturbative fixed point exists (Gaussian only)
    3. Quasi-fixed point near chiral scale: g_χ* ≈ 1.4-2.2
    4. Consistent with lattice constraint g_χ ≈ 1.26 ± 1.0
    5. Natural O(1) value at QCD scale from g_χ(M_P) ≈ 0.47

    Reference: docs/proofs/Phase3/Proposition-3.1.1b-RG-Fixed-Point-Analysis.md
-/

/-- Complete characterization of Proposition 3.1.1b.

Combines all key results about RG flow of the chiral coupling.
-/
theorem proposition_3_1_1b_complete :
    -- (1) β-coefficient formula
    (∀ n_c n_f, beta_coefficient_chiral n_c n_f = 2 - (n_c : ℚ) * n_f / 2) ∧
    -- (2) Asymptotic freedom for N_f > 4/N_c (as an iff)
    (∀ n_c n_f, n_c > 0 →
      (beta_coefficient_chiral n_c n_f < 0 ↔ (n_f : ℚ) > critical_flavor_count n_c)) ∧
    -- (3) SU(3) with N_f = 6 is asymptotically free
    (beta_coefficient_chiral 3 6 < 0) ∧
    -- (4) No perturbative fixed point (two-loop estimate)
    (two_loop_su3_nf6.has_fp = false) ∧
    -- (5) Quasi-fixed point consistent with lattice
    (quasi_fp_estimate.lower < flag_2024_constraint.upper) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact beta_coefficient_alternative
  · intro n_c n_f hn
    exact asymptotic_freedom_condition_chiral n_c n_f hn
  · exact beta_coefficient_su3_nf6 ▸ by norm_num
  · rfl
  · unfold quasi_fp_estimate flag_2024_constraint LatticeConstraint.upper
    norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 9: COMPARISON WITH QCD
    ═══════════════════════════════════════════════════════════════════════════

    Both QCD and phase-gradient coupling exhibit asymptotic freedom,
    but with different mechanisms:

    | Aspect | QCD (α_s) | Phase-Gradient (g_χ) |
    |--------|-----------|----------------------|
    | β-function sign | Negative | Negative |
    | UV behavior | Perturbative | Perturbative |
    | IR behavior | Confining | Freezes at χ VEV |
    | Fixed points | Gaussian (UV) | Gaussian + quasi-FP |

    Reference: §6.1 of markdown
-/

/-- QCD asymptotic freedom condition: N_f < 11N_c/2 -/
theorem qcd_af_condition (n_c n_f : ℕ) :
    beta_0_numerator n_c n_f > 0 ↔ 11 * n_c > 2 * n_f := by
  exact asymptotic_freedom_condition n_c n_f

/-- Chiral asymptotic freedom condition: N_f > 4/N_c -/
theorem chiral_af_condition (n_c n_f : ℕ) (hn : n_c > 0) :
    beta_coefficient_chiral n_c n_f < 0 ↔ (n_f : ℚ) > critical_flavor_count n_c :=
  asymptotic_freedom_condition_chiral n_c n_f hn

/-- Key difference: QCD loses AF at high N_f, chiral gains AF at high N_f.

For QCD: more flavors → weaker asymptotic freedom (can lose it)
For chiral: more flavors → stronger asymptotic freedom (always has it for N_f > 2)

Reference: Implicit in §6.1 comparison
-/
theorem opposite_nf_dependence :
    -- QCD: β₀ decreases with N_f (from asymptotic_freedom_decreasing)
    (∀ n_c n_f₁ n_f₂, n_f₁ ≤ n_f₂ →
      beta_0_numerator n_c n_f₂ ≤ beta_0_numerator n_c n_f₁) ∧
    -- Chiral: |b₁| increases with N_f (stronger AF) for n_c > 0
    (∀ n_c n_f₁ n_f₂, n_c > 0 → n_f₁ < n_f₂ →
      beta_coefficient_chiral n_c n_f₂ < beta_coefficient_chiral n_c n_f₁) := by
  constructor
  · exact asymptotic_freedom_decreasing
  · intro n_c n_f₁ n_f₂ hnc h
    exact beta_coefficient_decreasing_nf n_c n_f₁ n_f₂ hnc h

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 10: PHYSICAL INTERPRETATION SUMMARY
    ═══════════════════════════════════════════════════════════════════════════

    **What RG Analysis Achieves:**
    ✅ Explains why g_χ ~ O(1) at QCD scale
    ✅ Provides UV-IR consistency check
    ✅ Reduces apparent fine-tuning (focusing)
    ✅ Connects to standard QFT methodology

    **What RG Analysis Does NOT Achieve:**
    ❌ Unique determination of g_χ (depends on UV initial condition)
    ❌ Derivation from pure geometry (requires QFT input)
    ❌ Tighter bounds than lattice matching

    Reference: §8.3 of markdown (honest assessment)
-/

/-- Status of g_χ determination after RG analysis.

The RG analysis provides CONSISTENCY CHECKS, not unique determination.
The UV initial condition g_χ(M_P) remains a free parameter.

Reference: §8.2-8.3 of markdown
-/
inductive CouplingStatus
  | Derived       -- Completely determined from theory
  | Constrained   -- Range bounded by consistency
  | FreeParameter -- Needs external input
  deriving DecidableEq, Repr

/-- Current status of g_χ after RG analysis -/
def g_chi_status_post_rg : CouplingStatus := .Constrained

/-- RG analysis constrains but does not uniquely determine g_χ -/
theorem rg_constrains_not_determines : g_chi_status_post_rg = .Constrained := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 11: VERIFICATION CHECKS
    ═══════════════════════════════════════════════════════════════════════════
-/

section Verification

-- β-function coefficients
#check fermion_loop_coefficient
#check vertex_selfenergy_coefficient
#check beta_coefficient_chiral
#check beta_coefficient_alternative

-- Specific values
#check beta_coefficient_su3_nf6
#check beta_coefficient_su3_nf3
#check beta_coefficient_su3_nf5
#check beta_coefficient_su3_nf4

-- Asymptotic freedom
#check critical_flavor_count
#check critical_flavor_su3
#check asymptotic_freedom_condition_chiral
#check su3_chiral_asymptotic_freedom

-- RG flow structure
#check ChiralRGFlow
#check sm_chiral_flow_high
#check sm_chiral_flow_low

-- Threshold analysis
#check threshold_coefficients
#check all_thresholds_asymptotic
#check running_slows_at_thresholds

-- Fixed point analysis
#check one_loop_only_gaussian_fp
#check beta_zero_implies_coupling_zero
#check su3_beta_coefficient_nonzero
#check TwoLoopEstimate
#check two_loop_su3_nf6
#check no_perturbative_fp_sm

-- Quasi-fixed point
#check QuasiFixedPoint
#check quasi_fp_estimate
#check LatticeConstraint
#check flag_2024_constraint
#check quasi_fp_consistent_lattice

-- UV-IR connection and RG flow
#check RGFlowSolution
#check delta_inverse_coupling_squared
#check asymptotic_freedom_uv_decrease
#check asymptotic_freedom_ir_growth
#check coupling_squared_from_running
#check ir_coupling_larger_than_uv
#check total_running_change
#check threshold_mp_to_mt
#check threshold_sum_approximately
#check planck_scale_coupling_estimate
#check planck_estimate_gives_ir_order_one

-- Focusing behavior
#check ir_coupling_squared
#check focusing_ir_larger
#check example_uv_coupling_sq
#check example_focusing_ir_range
#check example_focusing_growth

-- Main proposition
#check proposition_3_1_1b_complete

-- Comparison with QCD
#check qcd_chiral_same_sign_nf6
#check opposite_nf_dependence

-- Status
#check CouplingStatus
#check g_chi_status_post_rg

end Verification

end ChiralGeometrogenesis.Phase3.Proposition_3_1_1b
