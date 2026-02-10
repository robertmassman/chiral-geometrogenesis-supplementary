/-
  Foundations/Proposition_0_0_17ac.lean

  Proposition 0.0.17ac: Edge-Mode Decomposition of UV Coupling

  STATUS: 🔶 NOVEL — Resolves UV Coupling Discrepancy in Theorem 5.2.6

  **Summary:**
  The (N_c² − 1)² = 64 adj⊗adj channels in the UV coupling decompose into
  52 local (running) face modes and 12 non-local (non-running) holonomy modes
  on the stella octangula. The running coupling 1/α_s(M_P) = 52 matches QCD
  running from α_s(M_Z) to ~1% (1-loop), resolving the ~17–22% discrepancy
  of the original prediction 1/α_s = 64.

  **Key Result:**
  M_P = (√χ/2) · √σ · exp((1/(2b₀)) · (1/α_s(M_P) + N_holonomy))

  where 1/α_s(M_P) = 52 (running, matches QCD) and N_holonomy = 12
  (topological, non-running).

  **Derivation Structure:**
  §2: Definitions (1-skeleton, cycle rank, link variables, Wilson loops)
  §3.1: Total adj⊗adj channel count = 64
  §3.2: Cycle rank β₁(K₄) = 3, β₁(∂S) = 6
  §3.3: Each holonomy carries rank(SU(N_c)) = N_c − 1 Cartan angles
  §3.4: Holonomy mode count N_holonomy = 6 × 2 = 12
  §3.5: Non-running via partition function factorization (Weyl integration)
  §3.6: Modified Planck mass formula
  §3.7: Uniqueness of V = 4, N_c = 3

  **Dependencies:**
  - ✅ Definition 0.1.1 (Stella Octangula): V=8, E=12, F=8, χ=4
  - ✅ Theorem 1.1.1 (SU(3) Weight Diagram): SU(3) gauge symmetry on ∂S
  - ✅ Proposition 0.0.27 (Lattice QFT on Stella): holonomies, Bianchi identity
  - 🔶 Theorem 5.2.6 (Planck Mass Emergence): original M_P formula with 1/α_s = 64
  - 🔶 Proposition 0.0.17w (Equipartition): max entropy → 64 channels

  Reference: docs/proofs/foundations/Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md
-/

import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.Constants
import ChiralGeometrogenesis.Tactics.Prelude
import ChiralGeometrogenesis.PureMath.LieAlgebra.SU3
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.nativeDecide false

namespace ChiralGeometrogenesis.Foundations.Proposition_0_0_17ac

open Real
open ChiralGeometrogenesis
open ChiralGeometrogenesis.Constants

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 1: GRAPH-THEORETIC FOUNDATIONS
    ═══════════════════════════════════════════════════════════════════════════

    Definitions and lemmas for the 1-skeleton graph K₄ of a tetrahedron
    and the disjoint union forming the stella octangula boundary.

    Reference: Markdown §2 (Definitions), §3.2 (Cycle Rank)
-/

/-- A finite simple graph represented by vertex and edge counts.
    We use this lightweight abstraction for the combinatorial arguments
    about K₄ and the stella octangula 1-skeleton. -/
structure SimpleGraphData where
  vertices : ℕ
  edges : ℕ
  components : ℕ
  h_components_pos : components > 0

/-- Cycle rank (first Betti number) of a graph:
    β₁(Γ) = |E| − |V| + c where c is the number of connected components.

    For a connected graph (c = 1): β₁ = |E| − |V| + 1.
    This counts the number of independent closed loops.

    Reference: Definition 2.2, standard graph theory -/
def cycleRank (g : SimpleGraphData) : ℤ :=
  (g.edges : ℤ) - (g.vertices : ℤ) + (g.components : ℤ)

/-- The complete graph K₄ (1-skeleton of a tetrahedron):
    4 vertices, 6 edges, 1 connected component. -/
def K4 : SimpleGraphData where
  vertices := 4
  edges := 6
  components := 1
  h_components_pos := by decide

/-- Stella octangula 1-skeleton as disjoint union of two K₄ graphs:
    8 vertices, 12 edges, 2 connected components. -/
def stellaSkeleton : SimpleGraphData where
  vertices := 8
  edges := 12
  components := 2
  h_components_pos := by decide

/-! ### Lemma 3.2.1: Cycle rank of K₄ -/

/-- **Lemma 3.2.1:** The cycle rank of the tetrahedral graph K₄ is β₁(K₄) = 3.

    *Proof.* K₄ is connected with |V| = 4 and |E| = 6:
    β₁(K₄) = 6 − 4 + 1 = 3. □

    Reference: Markdown §3.2, Lemma 3.2.1 -/
theorem cycleRank_K4 : cycleRank K4 = 3 := by
  unfold cycleRank K4
  norm_num

/-- K₄ vertex count matches the canonical value -/
theorem K4_vertices : K4.vertices = 4 := rfl

/-- K₄ edge count: C(4,2) = 6 (complete graph) -/
theorem K4_edges : K4.edges = 6 := rfl

/-- K₄ is connected -/
theorem K4_connected : K4.components = 1 := rfl

/-! ### Lemma 3.2.2: Cycle rank of the stella octangula 1-skeleton -/

/-- **Lemma 3.2.2:** The cycle rank of the stella octangula 1-skeleton is β₁(∂S) = 6.

    *Proof.* ∂S = K₊ ⊔ K₋ (disjoint union of two K₄ copies).
    For c = 2 components: β₁(∂S) = 12 − 8 + 2 = 6 = 3 + 3. □

    Reference: Markdown §3.2, Lemma 3.2.2 -/
theorem cycleRank_stella : cycleRank stellaSkeleton = 6 := by
  unfold cycleRank stellaSkeleton
  norm_num

/-- Stella 1-skeleton has 8 vertices (4 + 4) -/
theorem stella_skeleton_vertices : stellaSkeleton.vertices = 8 := rfl

/-- Stella 1-skeleton has 12 edges (6 + 6) -/
theorem stella_skeleton_edges : stellaSkeleton.edges = 12 := rfl

/-- Stella 1-skeleton has 2 connected components -/
theorem stella_skeleton_components : stellaSkeleton.components = 2 := rfl

/-- Cycle rank of stella equals twice the cycle rank of K₄ -/
theorem cycleRank_stella_eq_double_K4 :
    cycleRank stellaSkeleton = 2 * cycleRank K4 := by
  unfold cycleRank stellaSkeleton K4
  norm_num

/-! ### Spanning Tree and Independent Cycles

    For K₄ with vertices {0,1,2,3} and edges indexed as:
      0=(0,1), 1=(0,2), 2=(0,3), 3=(1,2), 4=(1,3), 5=(2,3)

    Choose spanning tree T = star from vertex 0: {e₀₁, e₀₂, e₀₃} = edges {0,1,2}.
    The 3 non-tree edges {e₁₂, e₁₃, e₂₃} = edges {3,4,5} generate the
    3 independent fundamental cycles:
      ℓ₁ = e₁₂ ∘ e₀₂⁻¹ ∘ e₀₁  (using non-tree edge 3)
      ℓ₂ = e₁₃ ∘ e₀₃⁻¹ ∘ e₀₁  (using non-tree edge 4)
      ℓ₃ = e₂₃ ∘ e₀₃⁻¹ ∘ e₀₂  (using non-tree edge 5)

    In tree gauge (U_e = 𝟙 for e ∈ T), the holonomy around each cycle
    equals the link variable on the non-tree edge: H_k = U_{non-tree edge k}.

    Reference: Markdown §3.2 (Construction of independent cycles), §3.5.3a -/

/-- Number of spanning tree edges: |T| = V − 1 = 3 for K₄.
    The spanning tree uses edges {0,1,2} = {e₀₁, e₀₂, e₀₃}. -/
theorem spanning_tree_size_K4 : K4.vertices - 1 = 3 := rfl

/-- Number of non-tree edges equals the cycle rank: |E| − |T| = 6 − 3 = 3 = β₁(K₄).
    The non-tree edges {3,4,5} = {e₁₂, e₁₃, e₂₃} generate independent cycles. -/
theorem non_tree_edges_eq_cycle_rank :
    K4.edges - (K4.vertices - 1) = 3 := rfl

/-- Non-tree edge count equals cycle rank (general statement for K₄) -/
theorem non_tree_count_eq_cycleRank_K4 :
    (K4.edges - (K4.vertices - 1) : ℤ) = cycleRank K4 := by
  unfold cycleRank K4; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 2: SU(N) GAUGE-INVARIANT HOLONOMY CONTENT
    ═══════════════════════════════════════════════════════════════════════════

    For SU(N_c), each independent holonomy carries rank(SU(N_c)) = N_c − 1
    gauge-invariant Cartan angles (eigenvalue phases with det = 1 constraint).

    Reference: Markdown §3.3 (Proposition 3.3.1), §3.4 (Theorem 3.4.1)
-/

/-- Rank of SU(N): the number of independent Cartan generators.
    rank(SU(N)) = N − 1.

    Note: This is definitionally equal to Constants.su_rank.
    Both definitions are maintained for readability within this proof file.

    Reference: Definition 2.5, standard Lie theory -/
def suRank (N : ℕ) : ℕ := N - 1

/-- Consistency with Constants.lean: suRank = Constants.su_rank -/
theorem suRank_eq_constants (N : ℕ) : suRank N = Constants.su_rank N := rfl

/-- rank(SU(3)) = 2 -/
theorem suRank_3 : suRank 3 = 2 := rfl

/-- rank(SU(2)) = 1 -/
theorem suRank_2 : suRank 2 = 1 := rfl

/-- **Proposition 3.3.1:** Each independent holonomy carries rank(SU(N_c))
    gauge-invariant parameters (Cartan angles).

    The gauge-invariant content of H ∈ SU(N_c) is its conjugacy class,
    determined by N_c − 1 independent eigenvalue phases (since det(H) = 1
    constrains one phase).

    Reference: Markdown §3.3 -/
theorem cartan_angles_per_holonomy (Nc : ℕ) (hNc : Nc ≥ 2) :
    suRank Nc = Nc - 1 := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 3: THE 64 = 52 + 12 DECOMPOSITION
    ═══════════════════════════════════════════════════════════════════════════

    The main results: holonomy mode count, local mode count, and the
    fundamental decomposition of adj⊗adj channels.

    Reference: Markdown §3.1 (Total Count), §3.4 (Holonomy Count),
               Corollary 3.4.2 (Local Count)
-/

/-- Total adj⊗adj channel count: (N_c² − 1)².
    For SU(3): dim(8⊗8) = 1 + 8 + 8 + 10 + 10 + 27 = 64.

    Note: Definitionally equal to Constants.adj_tensor_dim.

    Reference: Markdown §3.1 -/
def totalChannels (Nc : ℕ) : ℕ := (Nc * Nc - 1) * (Nc * Nc - 1)

/-- Consistency with Constants.lean -/
theorem totalChannels_eq_constants (Nc : ℕ) :
    totalChannels Nc = Constants.adj_tensor_dim Nc := rfl

/-- Total channels for SU(3) = 64 -/
theorem totalChannels_su3 : totalChannels 3 = 64 := rfl

/-- Verification: 8⊗8 Clebsch-Gordan decomposition dimensions sum to 64.
    8⊗8 = 1 ⊕ 8_s ⊕ 8_a ⊕ 10 ⊕ 10̄ ⊕ 27

    Reference: Markdown §3.1 -/
theorem clebsch_gordan_su3_adj_adj :
    1 + 8 + 8 + 10 + 10 + 27 = totalChannels 3 := rfl

/-- **Theorem 3.4.1 (Holonomy Mode Count):**
    N_holonomy = β₁(∂S) × rank(SU(N_c)) = 6 × (N_c − 1).

    For SU(3): N_holonomy = 6 × 2 = 12.

    The total number of gauge-invariant holonomy parameters on ∂S is the
    product of the number of independent cycles and the number of Cartan
    angles per holonomy.

    Reference: Markdown §3.4, Theorem 3.4.1 -/
def holonomyModes (Nc : ℕ) : ℕ := 6 * suRank Nc

/-- N_holonomy = 12 for SU(3) -/
theorem holonomyModes_su3 : holonomyModes 3 = 12 := rfl

/-- Holonomy count agrees with Constants.lean (general N_c) -/
theorem holonomyModes_eq_constants (Nc : ℕ) :
    holonomyModes Nc = Constants.holonomy_mode_count Nc := rfl

/-- Holonomy count from cycle rank × rank formula
    (showing the explicit product structure) -/
theorem holonomyModes_from_product :
    (holonomyModes 3 : ℤ) = cycleRank stellaSkeleton * (suRank 3 : ℤ) := by
  unfold holonomyModes cycleRank stellaSkeleton suRank
  norm_num

/-- **Corollary 3.4.2 (Local Mode Count):**
    N_local = (N_c² − 1)² − N_holonomy.

    For SU(3): N_local = 64 − 12 = 52.

    Reference: Markdown §3.4, Corollary 3.4.2 -/
def localModes (Nc : ℕ) : ℕ := totalChannels Nc - holonomyModes Nc

/-- N_local = 52 for SU(3) -/
theorem localModes_su3 : localModes 3 = 52 := rfl

/-- Local count agrees with Constants.lean (general N_c) -/
theorem localModes_eq_constants (Nc : ℕ) :
    localModes Nc = Constants.local_mode_count Nc := rfl

/-- **The Fundamental Decomposition (Proposition 0.0.17ac, Main Result (a)+(b)):**
    64 = 52 + 12.

    The (N_c² − 1)² = 64 adj⊗adj channels decompose as:
    - 52 local (running) face modes: participate in QCD running
    - 12 non-local (non-running) holonomy modes: topologically protected

    Reference: Markdown §1 (Statement) -/
theorem fundamental_decomposition :
    localModes 3 + holonomyModes 3 = totalChannels 3 := by
  unfold localModes totalChannels holonomyModes suRank
  rfl

/-- The decomposition verified using Constants.lean definitions -/
theorem fundamental_decomposition_constants :
    Constants.adj_tensor_dim 3 =
    Constants.local_mode_count 3 + Constants.holonomy_mode_count 3 := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 4: NON-RUNNING OF HOLONOMY MODES (STRUCTURAL)
    ═══════════════════════════════════════════════════════════════════════════

    The non-running of the 12 holonomy modes is established by the
    partition function factorization (§3.5.3). We formalize the structural
    aspects here; the analytic content (Weyl integration formula, character
    orthogonality) requires measure theory beyond current Mathlib scope.

    Reference: Markdown §3.5 (especially §3.5.3)
-/

/-! ### Established results cited (not formalized — beyond current Mathlib scope)

    **Lemma 3.5.3b (Weyl Integration Formula — Bröcker & tom Dieck 1985, Ch. V; Bump 2013):**
    For any class function f: SU(N_c) → ℂ, the Haar integral factorizes:
      ∫_{SU(N_c)} dH f(H) = (1/|W|) ∫_{T^{N_c-1}} dμ_Weyl(φ) f(φ)
    where dμ_Weyl = (1/(2π)^{N_c-1}) |Δ(e^{iφ})|² dφ₁…dφ_{N_c-1}
    depends ONLY on the root system of SU(N_c) (Vandermonde determinant),
    containing NO dependence on the lattice coupling β or energy scale.

    For SU(3): T² (maximal torus), |W| = |S₃| = 6, and
      |Δ(e^{iφ})|² = 64 sin²((φ₁−φ₂)/2) sin²((2φ₁+φ₂)/2) sin²((φ₁+2φ₂)/2)

    **Theorem 3.5.3c (Partition Function Factorization — Creutz 1983, Drouffe & Zuber 1983):**
    In tree gauge on K₄ (Faddeev-Popov determinant = 1 on finite graphs):
      Z(β) = (1/|W|³) ∫_{(T²)³} ∏_{k=1}^{3} dμ_Weyl(Ω_k) · W(Ω₁,Ω₂,Ω₃;β)
    where the Weyl measures are β-independent and the weight function W
    carries ALL β-dependence through heat-kernel coefficients β_R(β).

    **Corollary 3.5.3d (Non-Running of Holonomy Modes):**
    Under Wilsonian RG (β → β'(μ)):
    - The weight function W runs: β_R(β) → β_R(β'(μ)) [52 local modes]
    - The Weyl measure dμ_Weyl(Ω_k) does NOT run [12 holonomy modes]
    The 12 holonomy parameters parameterize the gauge-invariant configuration
    space whose measure is fixed by SU(3) group structure, hence non-running.

    **Corollary 3.5.3e (52 Running Channels via Weight Conservation):**
    Character orthogonality on T² ⊂ SU(3) imposes 2 weight-conservation
    constraints per independent cycle (one per Cartan generator):
    - Per tetrahedron: 3 cycles × 2 constraints = 6
    - Per stella: 2 × 6 = 12 constraints = 12 non-running modes
    Running channels: 64 − 12 = 52.

    Full measure-theoretic formalization requires compact Lie group integration
    theory beyond current Mathlib scope. The arithmetic consequences
    (count of β-independent parameters) are fully formalized below.
-/

/-- The number of β-independent integration variables per tetrahedron
    equals 2 × β₁(K₄) (Cartan angles of independent holonomies).

    Per tetrahedron: 3 cycles × 2 Cartan angles = 6 parameters.

    Reference: Markdown §3.5.3, Corollary 3.5.3d -/
theorem weyl_integration_variables_per_tet :
    2 * cycleRank K4 = 6 := by
  unfold cycleRank K4
  norm_num

/-- Total β-independent variables for the stella = 12.

    Reference: Markdown §3.5.3, Corollary 3.5.3d -/
theorem weyl_integration_variables_stella :
    2 * cycleRank stellaSkeleton = 12 := by
  unfold cycleRank stellaSkeleton
  norm_num

/-- The holonomy mode count (12) matches the weight-conservation constraint count:
    3 cycles × 2 Cartan generators × 2 tetrahedra = 12.

    The equality follows because each independent cycle imposes rank(SU(3)) = 2
    weight-conservation constraints via character orthogonality on T² ⊂ SU(3)
    (Corollary 3.5.3e). The constraint count equals the holonomy parameter count
    by construction: both count β₁(∂S) × rank(SU(3)).

    Reference: Markdown §3.5.3, Corollary 3.5.3e -/
theorem holonomy_count_eq_constraint_count :
    holonomyModes 3 = 2 * cycleRank stellaSkeleton := by
  unfold holonomyModes suRank cycleRank stellaSkeleton
  norm_num

/-- Running channels from weight conservation:
    N_running = 64 − 12 = 52.

    Reference: Markdown §3.5.3, Corollary 3.5.3e -/
theorem running_channels_from_weight_conservation :
    totalChannels 3 - holonomyModes 3 = 52 := by
  unfold totalChannels holonomyModes suRank
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 5: HODGE LAPLACIAN ON K₄ — EXPLICIT COMPUTATION
    ═══════════════════════════════════════════════════════════════════════════

    We define the boundary operators ∂₁: C₁ → C₀ and ∂₂: C₂ → C₁ for K₄
    explicitly and verify L₁ = ∂₁ᵀ∂₁ + ∂₂∂₂ᵀ = 4I₆ by machine computation
    of all 36 matrix entries. This implies the free gluon propagator is
    diagonal and uniform: G_{ee'} = (g²/4)δ_{ee'}, confirming that holonomy
    modes decouple from RG flow of the measure at one loop.

    Edge indexing: 0=(0,1), 1=(0,2), 2=(0,3), 3=(1,2), 4=(1,3), 5=(2,3)
    Face indexing: 0=(0,1,2), 1=(0,1,3), 2=(0,2,3), 3=(1,2,3)
    Face boundary convention: ∂(i,j,k) = e_{ij} − e_{ik} + e_{jk} for i<j<k

    Reference: Markdown §8.1.5 (Hodge Laplacian), §3.5.3f
-/

/-- Transposed boundary operator ∂₁ᵀ: edges → vertices.
    d1(e, v) = +1 if v is the target of edge e, −1 if v is the source.
    Edges oriented as (i,j) with i < j: source = i, target = j.

    This stores ∂₁ᵀ (the transpose of the vertex-edge incidence matrix)
    for convenient Hodge Laplacian computation: (∂₁ᵀ∂₁)(e,e') = Σ_v d1(e,v)d1(e',v). -/
def d1 : Fin 6 → Fin 4 → ℤ
  | 0, 0 => -1 | 0, 1 =>  1 | 0, 2 =>  0 | 0, 3 =>  0  -- e₀₁: v₀ → v₁
  | 1, 0 => -1 | 1, 1 =>  0 | 1, 2 =>  1 | 1, 3 =>  0  -- e₀₂: v₀ → v₂
  | 2, 0 => -1 | 2, 1 =>  0 | 2, 2 =>  0 | 2, 3 =>  1  -- e₀₃: v₀ → v₃
  | 3, 0 =>  0 | 3, 1 => -1 | 3, 2 =>  1 | 3, 3 =>  0  -- e₁₂: v₁ → v₂
  | 4, 0 =>  0 | 4, 1 => -1 | 4, 2 =>  0 | 4, 3 =>  1  -- e₁₃: v₁ → v₃
  | 5, 0 =>  0 | 5, 1 =>  0 | 5, 2 => -1 | 5, 3 =>  1  -- e₂₃: v₂ → v₃

/-- Boundary operator ∂₂: faces → edges.
    d2(e, f) = coefficient of edge e in the boundary of face f.
    Convention: ∂(i,j,k) = e_{ij} − e_{ik} + e_{jk} for i < j < k. -/
def d2 : Fin 6 → Fin 4 → ℤ
  | 0, 0 =>  1 | 0, 1 =>  1 | 0, 2 =>  0 | 0, 3 =>  0  -- e₀₁ in f₀₁₂, f₀₁₃
  | 1, 0 => -1 | 1, 1 =>  0 | 1, 2 =>  1 | 1, 3 =>  0  -- e₀₂ in f₀₁₂, f₀₂₃
  | 2, 0 =>  0 | 2, 1 => -1 | 2, 2 => -1 | 2, 3 =>  0  -- e₀₃ in f₀₁₃, f₀₂₃
  | 3, 0 =>  1 | 3, 1 =>  0 | 3, 2 =>  0 | 3, 3 =>  1  -- e₁₂ in f₀₁₂, f₁₂₃
  | 4, 0 =>  0 | 4, 1 =>  1 | 4, 2 =>  0 | 4, 3 => -1  -- e₁₃ in f₀₁₃, f₁₂₃
  | 5, 0 =>  0 | 5, 1 =>  0 | 5, 2 =>  1 | 5, 3 =>  1  -- e₂₃ in f₀₂₃, f₁₂₃

/-- Inner product of two Fin 4 → ℤ vectors (used for matrix products). -/
def dot4 (f g : Fin 4 → ℤ) : ℤ :=
  f 0 * g 0 + f 1 * g 1 + f 2 * g 2 + f 3 * g 3

/-- Hodge Laplacian on 1-forms of K₄:
    L₁(e,e') = (∂₁ᵀ∂₁)(e,e') + (∂₂∂₂ᵀ)(e,e')
             = Σ_v d1(e,v)·d1(e',v) + Σ_f d2(e,f)·d2(e',f) -/
def hodgeLaplacian1 (e e' : Fin 6) : ℤ :=
  dot4 (d1 e) (d1 e') + dot4 (d2 e) (d2 e')

/-- **Theorem (L₁ = 4I₆ on K₄):** The Hodge Laplacian on 1-forms of K₄
    equals 4 times the identity. All 6 eigenvalues are 4 (6-fold degenerate).

    *Proof.* Direct computation of all 36 matrix entries by case analysis
    on Fin 6 × Fin 6. The off-diagonal entries of ∂₁ᵀ∂₁ and ∂₂∂₂ᵀ
    cancel exactly — a consequence of S₄ symmetry acting transitively
    on edges of K₄. Each diagonal entry equals 2 + 2 = 4 (each edge
    touches 2 vertices and 2 faces). □

    Reference: Markdown §8.1.5, Supporting Proposition 3.5.3f -/
theorem hodge_laplacian_K4_eq_4I (e e' : Fin 6) :
    hodgeLaplacian1 e e' = if e = e' then 4 else 0 := by
  fin_cases e <;> fin_cases e' <;> native_decide

/-- The common eigenvalue of L₁ on K₄. -/
def hodgeLaplacianEigenvalue_K4 : ℕ := 4

/-- K₄ has 6 edges (the dimension of the 1-form space C₁). -/
theorem K4_edge_count_for_hodge : K4.edges = 6 := rfl

/-- Chain complex property: ∂₁ ∘ ∂₂ = 0 (boundary of a boundary vanishes).
    This verifies the boundary operators are consistent: d1 encodes ∂₁ᵀ
    and d2 encodes ∂₂, so the product Σ_e d1(e,v)·d2(e,f) = (∂₁·∂₂)(v,f) = 0.

    Reference: Standard simplicial homology -/
def d1_d2_product (v : Fin 4) (f : Fin 4) : ℤ :=
  d1 0 v * d2 0 f + d1 1 v * d2 1 f + d1 2 v * d2 2 f +
  d1 3 v * d2 3 f + d1 4 v * d2 4 f + d1 5 v * d2 5 f

theorem chain_complex_K4 (v : Fin 4) (f : Fin 4) :
    d1_d2_product v f = 0 := by
  fin_cases v <;> fin_cases f <;> native_decide

/-- The one-loop scheme conversion coefficient c₁ on K₄.

    c₁ = 3.0 (analytical, confirmed by Monte Carlo).
    The Haar measure Jacobian halves the naive Gaussian value from 6 to 3.

    Reference: Markdown §8.2 -/
noncomputable def c1_plaquette_coefficient : ℝ := 3.0

/-- c₁ > 0 -/
theorem c1_pos : c1_plaquette_coefficient > 0 := by
  unfold c1_plaquette_coefficient; norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 6: MODIFIED PLANCK MASS FORMULA
    ═══════════════════════════════════════════════════════════════════════════

    The decomposed formula replaces 1/α_s = 64 with:
    exponent = (1/α_s(M_P) + N_holonomy) / (2b₀) = (52 + 12) / (2b₀)

    The total exponent is numerically identical to the original, preserving
    the M_P prediction while resolving the UV coupling discrepancy.

    Reference: Markdown §3.6
-/

/-- The running coupling at the Planck scale in the CG framework:
    1/α_s(M_P) = N_local = 52.

    This replaces the original prediction 1/α_s = 64 and matches QCD running
    from α_s(M_Z) to ~1% at 1-loop.

    Reference: Markdown §3.6 -/
def inverse_alpha_s_Planck : ℕ := localModes 3

/-- 1/α_s(M_P) = 52 -/
theorem inverse_alpha_s_value : inverse_alpha_s_Planck = 52 := rfl

/-- The total exponent factor is preserved: 52 + 12 = 64.

    This ensures the M_P prediction is numerically identical to the
    original Theorem 5.2.6 formula.

    Reference: Markdown §4.3 -/
theorem total_exponent_preserved :
    inverse_alpha_s_Planck + holonomyModes 3 = totalChannels 3 := by
  unfold inverse_alpha_s_Planck localModes totalChannels holonomyModes suRank
  norm_num

/-- Holonomy fraction for SU(3): 12/64 ≈ 18.75%.

    In the large-N_c limit, this fraction → 0 as 6/N_c³, consistent
    with 't Hooft planar dominance.

    Reference: Markdown §5.6 -/
theorem holonomy_fraction_su3 :
    (holonomyModes 3 : ℚ) / (totalChannels 3 : ℚ) = 3 / 16 := by
  unfold holonomyModes totalChannels suRank
  norm_num

/-- The b₀ coefficient for SU(3) with N_f = 3 in RG convention:
    b₀ = (11N_c − 2N_f) / (12π) = 9/(4π).

    Convention: μ dα_s/dμ = −2b₀ α_s², so Λ/μ = exp(−1/(2b₀α_s)).

    Reference: Markdown §3.6 -/
noncomputable def b0_RG : ℝ := 9 / (4 * Real.pi)

/-- b₀ > 0 (asymptotic freedom) -/
theorem b0_RG_pos : b0_RG > 0 := by
  unfold b0_RG
  apply div_pos (by norm_num : (9:ℝ) > 0)
  apply mul_pos (by norm_num : (4:ℝ) > 0) Real.pi_pos

/-- The exponent in the modified Planck mass formula:
    (1/α_s(M_P) + N_holonomy) / (2b₀) = 64 / (2 × 9/(4π)) = 128π/9 ≈ 44.68.

    Reference: Markdown §3.6 -/
noncomputable def planck_exponent : ℝ :=
  ((inverse_alpha_s_Planck : ℝ) + (holonomyModes 3 : ℝ)) / (2 * b0_RG)

/-- The exponent simplifies to 128π/9.

    Calculation: (52 + 12) / (2 × 9/(4π)) = 64 / (9/(2π)) = 64 × 2π/9 = 128π/9.

    Reference: Markdown §3.6 -/
theorem planck_exponent_formula : planck_exponent = 128 * Real.pi / 9 := by
  unfold planck_exponent inverse_alpha_s_Planck localModes totalChannels
    holonomyModes suRank b0_RG
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- The modified Planck mass formula (Proposition 0.0.17ac, Main Result (c)):

    M_P = (√χ/2) · √σ · exp((1/(2b₀)) · (1/α_s(M_P) + N_holonomy))

    where:
    - χ = 4 (Euler characteristic of ∂S)
    - √σ = 440 MeV (string tension)
    - 1/α_s(M_P) = 52 (running coupling)
    - N_holonomy = 12 (topological, non-running)
    - b₀ = 9/(4π) (one-loop β-function coefficient)

    Reference: Markdown §3.6 -/
noncomputable def planck_mass_decomposed (chi : ℕ) (sqrt_sigma : ℝ) : ℝ :=
  (Real.sqrt (chi : ℝ) / 2) * sqrt_sigma * Real.exp planck_exponent

/-- M_P prediction with standard values: χ = 4, √σ = 0.440 GeV.

    M_P = (√4/2) × 0.440 × exp(128π/9) ≈ 1.12 × 10¹⁹ GeV.

    Reference: Markdown §3.6 -/
noncomputable def planck_mass_predicted : ℝ :=
  planck_mass_decomposed 4 Constants.sqrt_sigma_GeV

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 7: UNIQUENESS THEOREM
    ═══════════════════════════════════════════════════════════════════════════

    Among all triangulations of S² with V vertices and all SU(N_c) with
    N_c ≥ 2, the identity N_holonomy = χ(S²) × N_c holds if and only if
    V = 4 (tetrahedron) and N_c = 3.

    Reference: Markdown §3.7, Theorem 3.7.1
-/

/-- For a triangulation of S² with V vertices:
    - Every edge is shared by 2 faces: 3F = 2E
    - Euler relation: V − E + F = 2
    - Therefore: E = 3V − 6, F = 2V − 4
    - Cycle rank: β₁ = E − V + 1 = 2V − 5

    Reference: Markdown §3.7 -/
def triangulation_cycle_rank (V : ℕ) : ℤ :=
  2 * (V : ℤ) - 5

/-- Cycle rank of K₄ from the triangulation formula -/
theorem triangulation_cycle_rank_4 : triangulation_cycle_rank 4 = 3 := by
  unfold triangulation_cycle_rank
  norm_num

/-- Consistency: triangulation formula agrees with direct computation -/
theorem triangulation_cycle_rank_agrees_K4 :
    triangulation_cycle_rank 4 = cycleRank K4 := by
  unfold triangulation_cycle_rank cycleRank K4
  norm_num

/-- The target identity for uniqueness:
    N_holonomy = χ(S²) × N_c, equivalently per tetrahedron:
    β₁(K_V) × (N_c − 1) = N_c.

    Solving: (2V − 5)(N_c − 1) = 2N_c.
    Hence: V = (7N_c − 5) / (2(N_c − 1)).

    Reference: Markdown §3.7, Theorem 3.7.1 -/
def uniqueness_numerator (Nc : ℕ) : ℤ := 7 * (Nc : ℤ) - 5

def uniqueness_denominator (Nc : ℕ) : ℤ := 2 * ((Nc : ℤ) - 1)

/-- **Theorem 3.7.1 (Uniqueness):** V = 4 and N_c = 3 is the unique solution.

    For N_c = 3: V = (7×3 − 5) / (2×(3−1)) = 16/4 = 4. ✓
    For N_c = 2: V = 9/2 (not integer). ✗
    For N_c ≥ 4: V < 4 (below minimum for S² triangulation). ✗

    Reference: Markdown §3.7, Theorem 3.7.1 -/
theorem uniqueness_Nc3_V4 :
    uniqueness_numerator 3 = 4 * uniqueness_denominator 3 := by
  unfold uniqueness_numerator uniqueness_denominator
  norm_num

/-- N_c = 2 does NOT give integer V -/
theorem uniqueness_Nc2_fails :
    uniqueness_numerator 2 = 9 ∧ uniqueness_denominator 2 = 2 := by
  unfold uniqueness_numerator uniqueness_denominator
  constructor <;> norm_num

/-- N_c = 4: V = 23/6, not integer and < 4 -/
theorem uniqueness_Nc4_fails :
    uniqueness_numerator 4 = 23 ∧ uniqueness_denominator 4 = 6 := by
  unfold uniqueness_numerator uniqueness_denominator
  constructor <;> norm_num

/-- N_c = 5: V = 30/8 = 15/4, not integer and < 4 -/
theorem uniqueness_Nc5_fails :
    uniqueness_numerator 5 = 30 ∧ uniqueness_denominator 5 = 8 := by
  unfold uniqueness_numerator uniqueness_denominator
  constructor <;> norm_num

/-- N_c = 6: V = 37/10, not integer and < 4 -/
theorem uniqueness_Nc6_fails :
    uniqueness_numerator 6 = 37 ∧ uniqueness_denominator 6 = 10 := by
  unfold uniqueness_numerator uniqueness_denominator
  constructor <;> norm_num

/-- For N_c ≥ 4, the numerator < 4 × denominator, so V < 4.
    This means no valid triangulation of S² exists.

    Proof: 7N_c − 5 < 4 × 2(N_c − 1) = 8N_c − 8 iff N_c > 3.

    Reference: Markdown §3.7 -/
theorem uniqueness_large_Nc (Nc : ℕ) (hNc : Nc ≥ 4) :
    uniqueness_numerator Nc < 4 * uniqueness_denominator Nc := by
  unfold uniqueness_numerator uniqueness_denominator
  omega

/-- Uniqueness verification: the identity N_holonomy = 2χ(S²) × N_c = 4N_c
    holds for N_c = 3 (tetrahedra, V = 4).

    2 × β₁(K₄) × rank(SU(3)) = 2 × 3 × 2 = 12 = 4 × 3 = 4N_c.

    Reference: Markdown §3.7 -/
theorem uniqueness_identity_su3 :
    holonomyModes 3 = 4 * 3 := by
  unfold holonomyModes suRank
  norm_num

/-- SU(2) null test: N_holonomy = 6 ≠ 4N_c = 8 for SU(2).

    Reference: Markdown §8.3.1, Prediction 5 -/
theorem su2_null_test :
    holonomyModes 2 ≠ 4 * 2 := by
  unfold holonomyModes suRank
  norm_num

/-- **Unified Uniqueness Theorem (Theorem 3.7.1, Complete):**
    Among all SU(N_c) with N_c ≥ 2 and all triangulations of S² with V ≥ 4
    vertices, the identity N_holonomy = χ(∂S) × N_c holds if and only if
    V = 4 (tetrahedron) and N_c = 3.

    The proof proceeds by:
    1. N_c = 2: V = 9/2 (not an integer) — excluded
    2. N_c = 3: V = 16/4 = 4 — unique valid solution
    3. N_c ≥ 4: numerator < 4 × denominator, so V < 4 — excluded (below
       minimum vertex count for any triangulation of S²)

    Reference: Markdown §3.7, Theorem 3.7.1 -/
theorem uniqueness_complete (Nc : ℕ) (hNc : Nc ≥ 2) :
    (∃ V : ℕ, V ≥ 4 ∧ uniqueness_numerator Nc = (V : ℤ) * uniqueness_denominator Nc)
    ↔ Nc = 3 := by
  constructor
  · -- Forward: existence of valid V implies Nc = 3
    intro ⟨V, hV4, hVeq⟩
    by_contra hne
    have : Nc = 2 ∨ Nc ≥ 4 := by omega
    rcases this with rfl | hNc4
    · -- Nc = 2: uniqueness_numerator 2 = 9, denominator = 2, so 9 = V × 2
      -- Impossible since 9 is odd
      simp [uniqueness_numerator, uniqueness_denominator] at hVeq
      omega
    · -- Nc ≥ 4: numerator < 4 × denominator (from uniqueness_large_Nc)
      -- But V ≥ 4, so V × denominator ≥ 4 × denominator (since denom > 0)
      -- Contradiction: numerator = V × denom ≥ 4 × denom > numerator
      have hlt := uniqueness_large_Nc Nc hNc4
      have hd_pos : uniqueness_denominator Nc > 0 := by
        unfold uniqueness_denominator; omega
      have hge : 4 * uniqueness_denominator Nc ≤ (V : ℤ) * uniqueness_denominator Nc := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hd_pos)
        exact_mod_cast hV4
      linarith
  · -- Backward: Nc = 3 implies V = 4 works
    intro hNc3
    exact ⟨4, le_refl 4, by subst hNc3; unfold uniqueness_numerator uniqueness_denominator; norm_num⟩

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 8: GENERAL N_c FORMULAS AND LARGE-N_c LIMIT
    ═══════════════════════════════════════════════════════════════════════════

    For general SU(N_c):
    - N_holonomy = 6(N_c − 1) grows linearly
    - N_total = (N_c² − 1)² grows as N_c⁴
    - Holonomy fraction → 0 as 6/N_c³

    Reference: Markdown §5.6
-/

/-- General holonomy mode count for SU(N_c) on stella octangula:
    N_holonomy = 6 × (N_c − 1).

    Reference: Markdown §5.6 -/
theorem holonomy_general (Nc : ℕ) : holonomyModes Nc = 6 * suRank Nc := rfl

/-- General total channel count: (N_c² − 1)².

    Reference: Markdown §3.1 -/
theorem total_general (Nc : ℕ) : totalChannels Nc = (Nc * Nc - 1) * (Nc * Nc - 1) := rfl

/-- Holonomy modes for SU(4): 6 × 3 = 18 -/
theorem holonomyModes_su4 : holonomyModes 4 = 18 := rfl

/-- Total channels for SU(4): 15² = 225 -/
theorem totalChannels_su4 : totalChannels 4 = 225 := rfl

/-- Holonomy modes for SU(5): 6 × 4 = 24 -/
theorem holonomyModes_su5 : holonomyModes 5 = 24 := rfl

/-- Total channels for SU(5): 24² = 576 -/
theorem totalChannels_su5 : totalChannels 5 = 576 := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 9: CONSISTENCY CHECKS
    ═══════════════════════════════════════════════════════════════════════════

    Dimensional analysis, recovery of original formula, compatibility
    with lattice gauge theory.

    Reference: Markdown §5
-/

/-- §5.2: Recovery of original formula.
    The original Theorem 5.2.6 treated all (N_c²−1)² = 64 channels as running,
    giving 1/α_s = 64. The decomposed formula splits this into 52 running + 12
    non-running while preserving the total exponent.

    Without decomposition: 1/α_s = totalChannels 3 = 64 (original).
    With decomposition: 1/α_s = localModes 3 = 52 plus N_holonomy = 12.

    Reference: Markdown §5.2 -/
theorem original_coupling_undecomposed :
    totalChannels 3 = 64 := rfl

/-- The decomposed formula has a strictly smaller running coupling (52 < 64),
    resolving the UV coupling discrepancy with QCD running from α_s(M_Z). -/
theorem decomposed_coupling_smaller :
    localModes 3 < totalChannels 3 := by
  unfold localModes totalChannels holonomyModes suRank
  norm_num

/-- §5.5: Gravitational fixed point g* = χ/(N_c² − 1) = 4/8 = 1/2.
    This is independent of the running/non-running decomposition.

    Reference: Markdown §5.5 -/
theorem gravitational_fixed_point :
    (Constants.stella_boundary_euler_char : ℚ) / (Constants.adjoint_dim 3 : ℚ) = 1 / 2 := by
  unfold Constants.stella_boundary_euler_char Constants.adjoint_dim
  norm_num

/-- Holonomy count matches the stella Euler characteristic times N_c:
    N_holonomy = χ(∂S) × N_c = 4 × 3 = 12.

    Reference: Markdown §3.7, Uniqueness identity -/
theorem holonomy_chi_Nc_relation :
    holonomyModes 3 = 4 * Constants.N_c := by
  unfold holonomyModes suRank Constants.N_c
  rfl

/-- Holonomy fraction < 1 (holonomy modes are a proper subset) -/
theorem holonomy_fraction_lt_one :
    holonomyModes 3 < totalChannels 3 := by
  unfold holonomyModes totalChannels suRank
  norm_num

/-- Local modes are the majority -/
theorem local_modes_majority :
    localModes 3 > totalChannels 3 / 2 := by
  unfold localModes totalChannels holonomyModes suRank
  norm_num

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 10: SCHEME CONVERSION
    ═══════════════════════════════════════════════════════════════════════════

    The ~5% residual between CG prediction (52) and MS̄ running (~54.6)
    is a lattice-to-MS̄ scheme conversion effect.

    Reference: Markdown §8.1
-/

/-- Required scheme conversion offset: δ = 1/α_s^(MS̄) − 1/α_s^(stella) ≈ 2.63.

    Reference: Markdown §8.1.2 -/
noncomputable def scheme_conversion_delta : ℝ := 54.63 - 52

/-- δ > 0 (MS̄ coupling is weaker than stella lattice coupling at M_P) -/
theorem scheme_conversion_pos : scheme_conversion_delta > 0 := by
  unfold scheme_conversion_delta; norm_num

/-- Required Λ ratio: Λ_MS̄/Λ_stella ≈ 10.6.
    exp(2π × 2.63 / 7) ≈ 10.6

    Falls within the known range of lattice scheme conversions [6.3, 28.8].

    Reference: Markdown §8.1.2, §8.1.3 -/
noncomputable def lambda_ratio_stella_MSbar : ℝ :=
  Real.exp (2 * Real.pi * scheme_conversion_delta / 7)

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 11: SUMMARY THEOREM
    ═══════════════════════════════════════════════════════════════════════════

    The complete statement of Proposition 0.0.17ac.
-/

/-- **Proposition 0.0.17ac (Edge-Mode Decomposition of UV Coupling) — Complete Summary**

    For SU(3) lattice gauge theory on the stella octangula ∂S = ∂T₊ ⊔ ∂T₋:

    (a) N_holonomy = 2 × β₁(K₄) × rank(SU(3)) = 2 × 3 × 2 = 12
    (b) N_local = 64 − 12 = 52
    (c) Total exponent preserved: 52 + 12 = 64
    (d) Uniqueness: V = 4, N_c = 3 is the unique solution to N_holonomy = χ × N_c
    (e) Hodge Laplacian: L₁ = 4I₆ on K₄ (uniform gluon propagator)

    Reference: Markdown §1 (Statement) -/
theorem proposition_0_0_17ac :
    -- (a) Holonomy mode count
    holonomyModes 3 = 12 ∧
    -- (b) Local (running) mode count
    localModes 3 = 52 ∧
    -- (c) Decomposition preserves total
    localModes 3 + holonomyModes 3 = totalChannels 3 ∧
    -- (d) Uniqueness: N_c = 3, V = 4
    uniqueness_numerator 3 = 4 * uniqueness_denominator 3 ∧
    -- (e) Hodge Laplacian diagonal entry = 4 (all eigenvalues equal)
    hodgeLaplacian1 0 0 = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a): 6 × rank(SU(3)) = 6 × 2 = 12
    rfl
  · -- (b): 64 − 12 = 52
    rfl
  · -- (c): 52 + 12 = 64
    unfold localModes totalChannels holonomyModes suRank; rfl
  · -- (d): 16 = 4 × 4
    unfold uniqueness_numerator uniqueness_denominator; norm_num
  · -- (e): L₁(0,0) = dot4(d1 0, d1 0) + dot4(d2 0, d2 0) = 2 + 2 = 4
    native_decide

end ChiralGeometrogenesis.Foundations.Proposition_0_0_17ac
