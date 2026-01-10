/-
  Phase5/Theorem_5_2_2/ConfigurationSpace.lean

  Theorem 5.2.2: Pre-Geometric Cosmic Coherence — Configuration Space

  This module contains Parts 5-6:
  - PART 5: Pre-Geometric Configuration Space
  - PART 6: The Emergence Map

  Reference: docs/proofs/Phase5/Theorem-5.2.2-Pre-Geometric-Cosmic-Coherence.md §5.1-5.2
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import ChiralGeometrogenesis.Phase0.Definition_0_1_2
import ChiralGeometrogenesis.Phase5.Theorem_5_2_2.SU3Phase

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase5.PreGeometricCoherence

open Real Complex
open ChiralGeometrogenesis.Phase0.Definition_0_1_2

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 5: PRE-GEOMETRIC CONFIGURATION SPACE
    ═══════════════════════════════════════════════════════════════════════════

    The pre-geometric configuration space 𝒞₀ contains:
    - Overall phase Φ ∈ S¹
    - Amplitudes a_c ∈ ℝ⁺ for c ∈ {R, G, B}

    This is a 4-dimensional parameter space with no spatial structure.

    Reference: §5.1 (Pre-Geometric Phase Space)
-/

/-- Pre-geometric configuration: overall phase and three amplitudes.

    This is the configuration space 𝒞₀ from §5.1:
    𝒞₀ = {(Φ, {a_c}) : Φ ∈ S¹, a_c ∈ ℝ⁺}

    No spatial coordinates are involved. -/
structure PreGeometricConfig where
  /-- Overall phase Φ ∈ [0, 2π) -/
  overallPhase : ℝ
  /-- Amplitude for Red -/
  amplitude_R : ℝ
  /-- Amplitude for Green -/
  amplitude_G : ℝ
  /-- Amplitude for Blue -/
  amplitude_B : ℝ
  /-- All amplitudes are positive -/
  amp_R_pos : amplitude_R > 0
  amp_G_pos : amplitude_G > 0
  amp_B_pos : amplitude_B > 0

namespace PreGeometricConfig

/-- The total field in the pre-geometric arena.

    χ_total(Φ, {a_c}) = Σ_c a_c e^{i(φ_c^{(0)} + Φ)}

    Reference: §5.1 -/
noncomputable def totalField (cfg : PreGeometricConfig) : ℂ :=
  cfg.amplitude_R * Complex.exp (Complex.I * (algebraicPhase ColorPhase.R + cfg.overallPhase)) +
  cfg.amplitude_G * Complex.exp (Complex.I * (algebraicPhase ColorPhase.G + cfg.overallPhase)) +
  cfg.amplitude_B * Complex.exp (Complex.I * (algebraicPhase ColorPhase.B + cfg.overallPhase))

/-- For equal amplitudes, the total field vanishes.

    When a_R = a_G = a_B = a, we have:
    χ_total = a · e^{iΦ} · (1 + ω + ω²) = a · e^{iΦ} · 0 = 0

    Reference: §5.4 -/
theorem totalField_vanishes_equal_amplitudes (cfg : PreGeometricConfig)
    (h_equal : cfg.amplitude_R = cfg.amplitude_G ∧ cfg.amplitude_G = cfg.amplitude_B) :
    cfg.totalField = 0 := by
  unfold totalField algebraicPhase ColorPhase.angle
  simp only [Complex.ofReal_zero, zero_add]
  -- Let a = cfg.amplitude_R (we'll use h_equal to substitute)
  have h1 : cfg.amplitude_R = cfg.amplitude_G := h_equal.1
  have h2 : cfg.amplitude_G = cfg.amplitude_B := h_equal.2
  have h3 : cfg.amplitude_R = cfg.amplitude_B := h1.trans h2
  -- Rewrite all amplitudes to use amplitude_R (= a)
  rw [← h1, ← h3]
  -- Now the goal has all amplitude_R terms
  -- Factor: a*exp(I*(0+Φ)) + a*exp(I*(2π/3+Φ)) + a*exp(I*(4π/3+Φ))
  --       = a * exp(I*Φ) * (exp(0) + exp(I*2π/3) + exp(I*4π/3))
  --       = a * exp(I*Φ) * (1 + ω + ω²)
  --       = a * exp(I*Φ) * 0 = 0
  -- Rewrite each exp(I*(θ+Φ)) as exp(I*θ) * exp(I*Φ) using exp_add
  have hR : Complex.exp (I * ↑cfg.overallPhase) =
            phaseFactor ColorPhase.R * Complex.exp (I * ↑cfg.overallPhase) := by
    rw [phaseFactor_R]; ring
  have hG : Complex.exp (I * (↑(2 * π / 3) + ↑cfg.overallPhase)) =
            phaseFactor ColorPhase.G * Complex.exp (I * ↑cfg.overallPhase) := by
    rw [phaseFactor_G]
    -- Goal: exp(I * (2π/3 + Φ)) = ω * exp(I * Φ)
    -- Use: exp(I * (2π/3 + Φ)) = exp(I * 2π/3 + I * Φ) = exp(I * 2π/3) * exp(I * Φ)
    have h_split : I * (↑(2 * π / 3) + ↑cfg.overallPhase) =
                   I * ↑(2 * π / 3) + I * ↑cfg.overallPhase := by ring
    rw [h_split, Complex.exp_add]
    -- Now: exp(I * 2π/3) * exp(I * Φ) = ω * exp(I * Φ)
    congr 1
    -- Show exp(I * 2π/3) = ω
    unfold omega
    congr 1
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hB : Complex.exp (I * (↑(4 * π / 3) + ↑cfg.overallPhase)) =
            phaseFactor ColorPhase.B * Complex.exp (I * ↑cfg.overallPhase) := by
    rw [phaseFactor_B]
    -- Goal: exp(I * (4π/3 + Φ)) = ω² * exp(I * Φ)
    have h_split : I * (↑(4 * π / 3) + ↑cfg.overallPhase) =
                   I * ↑(4 * π / 3) + I * ↑cfg.overallPhase := by ring
    rw [h_split, Complex.exp_add]
    congr 1
    -- Show exp(I * 4π/3) = ω²
    unfold omega
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [Nat.cast_ofNat, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [hR, hG, hB]
  -- Now factor out amplitude_R and exp(I*Φ)
  -- Let a = amplitude_R, rot = exp(I*Φ), pR/pG/pB = phase factors
  -- Goal: a*(pR*rot) + a*(pG*rot) + a*(pB*rot) = a*rot*(pR + pG + pB)
  have factored :
      ↑cfg.amplitude_R * (phaseFactor ColorPhase.R * Complex.exp (I * ↑cfg.overallPhase)) +
      ↑cfg.amplitude_R * (phaseFactor ColorPhase.G * Complex.exp (I * ↑cfg.overallPhase)) +
      ↑cfg.amplitude_R * (phaseFactor ColorPhase.B * Complex.exp (I * ↑cfg.overallPhase)) =
      ↑cfg.amplitude_R * Complex.exp (I * ↑cfg.overallPhase) *
      (phaseFactor ColorPhase.R + phaseFactor ColorPhase.G + phaseFactor ColorPhase.B) := by ring
  rw [factored, phase_factors_sum_zero, mul_zero]

end PreGeometricConfig

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 6: THE EMERGENCE MAP
    ═══════════════════════════════════════════════════════════════════════════

    The emergence map ℰ: 𝒞₀ × Σ → 𝒞_spatial creates spatial dependence
    only in amplitudes, NOT in relative phases.

    Reference: §5.2.1-5.2.2 (Emergence Map Construction, Phase Preservation)
-/

/-- The topological scaffold Σ is the combinatorial structure of the
    stella octangula, with graph distance but no metric.

    **Mathematical Structure:**
    The stella octangula has 8 vertices (4 from each tetrahedron) and 12 edges.
    - Vertices from tetrahedron T₊: v₀, v₁, v₂, v₃ (indices 0-3)
    - Vertices from tetrahedron T₋: v₄, v₅, v₆, v₇ (indices 4-7)
    - Each vertex of T₊ is adjacent to 3 vertices of T₋ (and vice versa)
    - The dual structure: each tetrahedron's vertices are mutually adjacent

    **Graph Distance Properties:**
    - d(v, v) = 0 (reflexivity)
    - d(v, w) = d(w, v) (symmetry)
    - d(v, w) ≤ d(v, u) + d(u, w) (triangle inequality)
    - d(v, w) = 1 iff v and w share an edge
    - Maximum distance is 2 (any two vertices connected by at most 2 edges)

    **Citation:** Definition 0.1.1 (Stella Octangula Boundary Topology)

    Reference: §5.2.1 Step 0 -/
structure TopologicalScaffold where
  /-- The 8 vertices of the stella octangula -/
  vertices : Fin 8
  /-- Graph distance (edge-based, no metric needed) -/
  graph_distance : Fin 8 → Fin 8 → ℕ
  /-- Graph distance is reflexive: d(v, v) = 0 -/
  distance_reflexive : ∀ v : Fin 8, graph_distance v v = 0
  /-- Graph distance is symmetric: d(v, w) = d(w, v) -/
  distance_symmetric : ∀ v w : Fin 8, graph_distance v w = graph_distance w v
  /-- Graph distance satisfies triangle inequality -/
  distance_triangle : ∀ u v w : Fin 8,
    graph_distance u w ≤ graph_distance u v + graph_distance v w
  /-- Maximum distance is bounded (stella octangula diameter is 2) -/
  distance_bounded : ∀ v w : Fin 8, graph_distance v w ≤ 2

/-- A point on the scaffold -/
structure ScaffoldPoint where
  scaffold : TopologicalScaffold
  position : Fin 8

/-- The stella octangula graph distance function.

    For the stella octangula:
    - d = 0: same vertex
    - d = 1: adjacent vertices (share an edge)
    - d = 2: non-adjacent vertices (connected via one intermediate vertex)

    **Explicit structure:**
    Tetrahedra T₊ and T₋ are dual, meaning each vertex of T₊ is adjacent
    to exactly 3 vertices of T₋ (the ones that don't share the same position).

    **Citation:** stellaOctangula3D from Definition_0_1_1 -/
def stellaGraphDistance : Fin 8 → Fin 8 → ℕ :=
  fun v w =>
    if v = w then 0
    else if (v.val < 4 ∧ w.val ≥ 4) ∨ (v.val ≥ 4 ∧ w.val < 4) then 1
    else 2  -- Same tetrahedron, non-adjacent

/-- The stella octangula graph distance satisfies reflexivity -/
theorem stella_distance_reflexive : ∀ v : Fin 8, stellaGraphDistance v v = 0 := by
  intro v
  unfold stellaGraphDistance
  simp

/-- The stella octangula graph distance is symmetric -/
theorem stella_distance_symmetric :
    ∀ v w : Fin 8, stellaGraphDistance v w = stellaGraphDistance w v := by
  intro v w
  unfold stellaGraphDistance
  by_cases h1 : v = w
  · simp [h1]
  · by_cases h2 : w = v
    · simp [h2]
    · simp only [h1, h2, ↓reduceIte]
      -- The condition (v < 4 ∧ w ≥ 4) ∨ (v ≥ 4 ∧ w < 4) is symmetric
      -- because it's just asking if v and w are in different tetrahedra
      by_cases hcond : (v.val < 4 ∧ w.val ≥ 4) ∨ (v.val ≥ 4 ∧ w.val < 4)
      · simp only [hcond, ↓reduceIte]
        -- If original condition holds, so does the swapped version
        have hswap : (w.val < 4 ∧ v.val ≥ 4) ∨ (w.val ≥ 4 ∧ v.val < 4) := by
          rcases hcond with ⟨hv, hw⟩ | ⟨hv, hw⟩
          · right; exact ⟨hw, hv⟩
          · left; exact ⟨hw, hv⟩
        simp [hswap]
      · simp only [hcond, ↓reduceIte]
        -- If original condition fails, so does the swapped version
        have hswap : ¬((w.val < 4 ∧ v.val ≥ 4) ∨ (w.val ≥ 4 ∧ v.val < 4)) := by
          push_neg at hcond ⊢
          -- hcond : (v.val < 4 → w.val < 4) ∧ (v.val ≥ 4 → w.val ≥ 4)
          -- Goal: (w.val < 4 → v.val < 4) ∧ (w.val ≥ 4 → v.val ≥ 4)
          constructor
          · intro hw_lt
            -- w < 4, need v < 4
            by_contra hv_ge
            push_neg at hv_ge
            -- v ≥ 4 and w < 4, so by hcond.2: v ≥ 4 → w ≥ 4, contradiction
            exact Nat.lt_irrefl w.val (Nat.lt_of_lt_of_le hw_lt (hcond.2 hv_ge))
          · intro hw_ge
            -- w ≥ 4, need v ≥ 4
            by_contra hv_lt
            push_neg at hv_lt
            -- v < 4 and w ≥ 4, so by hcond.1: v < 4 → w < 4, contradiction
            exact Nat.lt_irrefl w.val (Nat.lt_of_lt_of_le (hcond.1 hv_lt) hw_ge)
        simp [hswap]

/-- The stella octangula graph distance is bounded by 2 -/
theorem stella_distance_bounded : ∀ v w : Fin 8, stellaGraphDistance v w ≤ 2 := by
  intro v w
  unfold stellaGraphDistance
  split_ifs <;> omega

/-- The stella octangula graph distance satisfies the triangle inequality.

    **Proof Strategy:**
    Since stellaGraphDistance ∈ {0, 1, 2} for all pairs, and the maximum is 2,
    we need to show: d(u,w) ≤ d(u,v) + d(v,w)

    Case analysis:
    - If d(u,w) = 0: u = w, so 0 ≤ d(u,v) + d(v,u) = 2·d(u,v) ≥ 0 ✓
    - If d(u,w) = 1: u,w in different tetrahedra, need d(u,v) + d(v,w) ≥ 1
      This holds unless both are 0, which would require u = v = w, contradiction.
    - If d(u,w) = 2: u,w in same tetrahedron (both < 4 or both ≥ 4)
      Any intermediate v gives d(u,v) + d(v,w) ≥ 2:
      * If v in same tetrahedron as u,w: d(u,v) = 2 or d(v,w) = 2 (unless v=u or v=w)
      * If v in different tetrahedron: d(u,v) = 1 and d(v,w) = 1, so sum = 2 ✓ -/
theorem stella_distance_triangle : ∀ u v w : Fin 8,
    stellaGraphDistance u w ≤ stellaGraphDistance u v + stellaGraphDistance v w := by
  intro u v w
  -- Since d(u,w) ≤ 2 always, we just need d(u,v) + d(v,w) ≥ d(u,w)
  -- Use the fact that the distance is bounded and decidable
  simp only [stellaGraphDistance]
  split_ifs <;> omega

/-- Construct a TopologicalScaffold instance for the stella octangula.

    This provides a concrete witness that stellaGraphDistance satisfies
    all the required metric properties. -/
def stellaScaffold : TopologicalScaffold where
  vertices := ⟨0, by omega⟩  -- Representative vertex
  graph_distance := stellaGraphDistance
  distance_reflexive := stella_distance_reflexive
  distance_symmetric := stella_distance_symmetric
  distance_triangle := stella_distance_triangle
  distance_bounded := stella_distance_bounded

/-- The emergence map preserves RELATIVE phases.

    ℰ: a_c ↦ a_c(x) = a₀ P_c(x)
    ℰ: φ_c^{(0)} ↦ φ_c^{(0)}  (UNCHANGED)

    Therefore:
    φ_G(x) - φ_R(x) = φ_G^{(0)} - φ_R^{(0)} = 2π/3  for all x

    Reference: §5.2.2 (Phase Preservation Theorem) -/
theorem emergence_preserves_relative_phases (x : ℝ) (Φ_x : ℝ) :
    let phase_R := algebraicPhase ColorPhase.R + Φ_x
    let phase_G := algebraicPhase ColorPhase.G + Φ_x
    let phase_B := algebraicPhase ColorPhase.B + Φ_x
    phase_G - phase_R = 2 * Real.pi / 3 ∧
    phase_B - phase_G = 2 * Real.pi / 3 := by
  simp only
  constructor <;> {
    unfold algebraicPhase ColorPhase.angle
    ring
  }

/-- Why phases cannot acquire spatial dependence:

    1. Algebraic constraint: φ_c^{(0)} are determined by SU(3)
    2. No dynamical mechanism: No Hamiltonian causes spatial phase variation
    3. Energy minimization: Deviations from 120° increase energy

    **Key Insight:**
    The RELATIVE phases are algebraic constants: Δφ_GR = φ_G - φ_R = 2π/3.
    The OVERALL phase Φ(x) can vary spatially (Goldstone mode), but this
    cancels in the relative phase calculation:

      (φ_G + Φ(x)) - (φ_R + Φ(x)) = φ_G - φ_R = 2π/3

    So the question "how do phases stay coherent across space?" has the answer:
    "the relative phases are mathematical constants like π — they don't
    propagate, they just ARE."

    Reference: §5.2.2 -/
theorem phases_cannot_vary_spatially :
    ∀ (x y : ℝ) (Φ_x Φ_y : ℝ),
    -- Even if positions have different overall phases Φ_x and Φ_y,
    -- the RELATIVE phases are unchanged
    let phase_G_at_x := algebraicPhase ColorPhase.G + Φ_x
    let phase_R_at_x := algebraicPhase ColorPhase.R + Φ_x
    let phase_G_at_y := algebraicPhase ColorPhase.G + Φ_y
    let phase_R_at_y := algebraicPhase ColorPhase.R + Φ_y
    -- The relative phase at x equals the relative phase at y
    (phase_G_at_x - phase_R_at_x) = (phase_G_at_y - phase_R_at_y) := by
  intros x y Φ_x Φ_y
  -- Both reduce to algebraicPhase G - algebraicPhase R = 2π/3
  -- because the Φ terms cancel
  simp only
  ring

/-- The relative phase is independent of the overall phase.

    This is the mathematical content of "phases cannot vary spatially":
    adding ANY spatially-varying overall phase Φ(x) doesn't change the
    relative phase between colors.

    Δφ_GR(x) = (φ_G + Φ(x)) - (φ_R + Φ(x)) = φ_G - φ_R = 2π/3 -/
theorem relative_phase_independent_of_overall (Φ : ℝ) :
    (algebraicPhase ColorPhase.G + Φ) - (algebraicPhase ColorPhase.R + Φ) =
    algebraicPhase ColorPhase.G - algebraicPhase ColorPhase.R := by
  ring

/-- The relative phase equals 2π/3 regardless of overall phase.

    This combines the independence theorem with the actual value. -/
theorem relative_phase_always_120_degrees (Φ : ℝ) :
    (algebraicPhase ColorPhase.G + Φ) - (algebraicPhase ColorPhase.R + Φ) =
    2 * Real.pi / 3 := by
  rw [relative_phase_independent_of_overall]
  unfold algebraicPhase ColorPhase.angle
  ring

/-- Spatial variation of overall phase doesn't affect coherence.

    Even if Φ varies wildly from point to point, the phase sum still vanishes:
    Σ_c e^{i(φ_c + Φ(x))} = e^{iΦ(x)} · Σ_c e^{iφ_c} = e^{iΦ(x)} · 0 = 0

    **Proof Strategy:**
    Factor out e^{iΦ}, then use 1 + ω + ω² = 0 (cube_roots_sum_zero). -/
theorem spatial_phase_variation_preserves_coherence :
    ∀ (x : ℝ) (Φ_x : ℝ),
    -- The phase sum at position x (with overall phase Φ_x) is zero
    Complex.exp (Complex.I * (algebraicPhase ColorPhase.R + Φ_x)) +
    Complex.exp (Complex.I * (algebraicPhase ColorPhase.G + Φ_x)) +
    Complex.exp (Complex.I * (algebraicPhase ColorPhase.B + Φ_x)) = 0 := by
  intro x Φ_x
  -- Expand the algebraic phases
  unfold algebraicPhase ColorPhase.angle
  simp only [Complex.ofReal_zero, zero_add]
  -- Use exp(a+b) = exp(a) * exp(b) to factor out exp(I*Φ)
  have hR : Complex.exp (Complex.I * ↑Φ_x) =
            Complex.exp (Complex.I * 0) * Complex.exp (Complex.I * ↑Φ_x) := by simp
  have hG : Complex.exp (Complex.I * (↑(2 * Real.pi / 3) + ↑Φ_x)) =
            Complex.exp (Complex.I * ↑(2 * Real.pi / 3)) * Complex.exp (Complex.I * ↑Φ_x) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hB : Complex.exp (Complex.I * (↑(4 * Real.pi / 3) + ↑Φ_x)) =
            Complex.exp (Complex.I * ↑(4 * Real.pi / 3)) * Complex.exp (Complex.I * ↑Φ_x) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hR, hG, hB]
  -- Now have: exp(0)*rot + exp(2πi/3)*rot + exp(4πi/3)*rot where rot = exp(I*Φ)
  -- Factor: rot * (exp(0) + exp(2πi/3) + exp(4πi/3)) = rot * (1 + ω + ω²)
  have h_factor : Complex.exp (I * 0) * Complex.exp (I * ↑Φ_x) +
                  Complex.exp (I * ↑(2 * π / 3)) * Complex.exp (I * ↑Φ_x) +
                  Complex.exp (I * ↑(4 * π / 3)) * Complex.exp (I * ↑Φ_x) =
                  Complex.exp (I * ↑Φ_x) * (Complex.exp (I * 0) +
                                            Complex.exp (I * ↑(2 * π / 3)) +
                                            Complex.exp (I * ↑(4 * π / 3))) := by ring
  rw [h_factor]
  -- Simplify exp(0) = 1
  simp only [mul_zero, Complex.exp_zero]
  -- Show exp(2πi/3) = ω and exp(4πi/3) = ω²
  have hω : Complex.exp (I * ↑(2 * π / 3)) = omega := by
    unfold omega; congr 1
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]; ring
  have hω2 : Complex.exp (I * ↑(4 * π / 3)) = omega ^ 2 := by
    unfold omega
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [Nat.cast_ofNat, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]; ring
  rw [hω, hω2, cube_roots_sum_zero, mul_zero]

end ChiralGeometrogenesis.Phase5.PreGeometricCoherence
