/-
  Constants/Geometry.lean — Stella octangula geometry, FCC honeycomb,
  and Wilson fermion parameters.

  Section 5 from the original Constants.lean.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import ChiralGeometrogenesis.Constants.Core

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Constants

open Real

/-- Stella octangula characteristic radius R_stella = ℏc/√σ ≈ 0.44847 fm.

    **Physical meaning:**
    This is the single phenomenological input at the QCD level.
    All QCD scales (√σ, f_π, Λ_QCD) derive from this single value.

    **Value determination:**
    R_stella = ℏc/√σ = 197.327 MeV·fm / 440 MeV = 0.44847 fm
    This ensures exact agreement with observed string tension.

    **Citation:** Proposition 0.0.17j -/
noncomputable def R_stella_fm : ℝ := 0.44847

/-- R_stella > 0 -/
theorem R_stella_pos : R_stella_fm > 0 := by unfold R_stella_fm; norm_num

/-- Historical value R_stella = 0.45 fm (for reference)

    This was the original approximation. The precise value 0.44847 fm
    is derived from matching √σ = 440 MeV exactly. -/
noncomputable def R_stella_approx_fm : ℝ := 0.45

/-- Order of W(F₄) Weyl group: |W(F₄)| = 1152.

    **Citation:** Humphreys, "Reflection Groups" (1990), Table 2.4 -/
def WF4_order : ℕ := 1152

/-- Order of stella octangula symmetry group: |S₄ × Z₂| = 48.

    **Breakdown:**
    - S₄ (tetrahedral rotations): order 24
    - Z₂ (antipodal/parity swap): order 2
    - Total: 24 × 2 = 48

    **Citation:** Coxeter, "Regular Polytopes" (1973), §2.3 -/
def stella_symmetry_order : ℕ := 48

/-- Number of 24-cell vertices (enhancement factor) -/
def cell24_vertices : ℕ := 24

/-- W(F₄) factorization: 1152 = 24 × 48 -/
theorem WF4_factorization : WF4_order = cell24_vertices * stella_symmetry_order := rfl

/-- Order of W(B₄) Weyl group: |W(B₄)| = 384.

    **Physical meaning:**
    The Weyl group of B₄ (16-cell symmetry) has order 2⁴ × 4! = 384.
    The ratio |W(F₄)|/|W(B₄)| = 1152/384 = 3 is the triality factor.

    **Citation:** Humphreys, "Reflection Groups" (1990), Table 2.4 -/
def WB4_order : ℕ := 384

/-- |W(B₄)| = 384 (value check) -/
theorem WB4_order_value : WB4_order = 384 := rfl

/-- |W(B₄)| > 0 -/
theorem WB4_order_pos : WB4_order > 0 := by decide

/-- Order of H₄ symmetry group (600-cell): |H₄| = 14400.

    **Physical meaning:**
    The 600-cell is the 4D analog of the icosahedron. Its symmetry group H₄
    has order 14400 = 120 × 120, where 120 is the order of the icosahedral
    group. The 600-cell contains 5 copies of the 24-cell.

    **Usage in Proposition 0.0.18:**
    The electroweak scale enhancement factor √(|H₄|/|F₄|) = √(14400/1152) = √12.5 ≈ 3.54

    **Citation:** Coxeter, "Regular Polytopes" (1973), Ch. 14 -/
def H4_order : ℕ := 14400

/-- |H₄| = 14400 (value check) -/
theorem H4_order_value : H4_order = 14400 := rfl

/-- |H₄| > 0 -/
theorem H4_order_pos : H4_order > 0 := by decide

/-- Number of 600-cell vertices -/
def cell600_vertices : ℕ := 120

/-- The 600-cell contains exactly 5 copies of the 24-cell: 120 = 5 × 24 -/
theorem cell600_24_cell_copies : cell600_vertices = 5 * cell24_vertices := rfl

/-- D₄ triality factor: |W(F₄)|/|W(B₄)| = 3.

    **Physical meaning:**
    The D₄ root system has a unique outer automorphism group S₃ ("triality")
    that permutes three 8-dimensional representations. The 24-cell (F₄)
    enhances the 16-cell (B₄) by this triality factor.

    **Derivation:** triality = 1152/384 = 3

    **Citation:** Proposition 0.0.18 §8.4 -/
def triality : ℕ := WF4_order / WB4_order

/-- triality = 3 -/
theorem triality_value : triality = 3 := rfl

/-- triality > 0 -/
theorem triality_pos : triality > 0 := by decide

/-- Triality from Weyl group ratio -/
theorem triality_from_weyl_ratio : WF4_order = triality * WB4_order := rfl

/-- Intrinsic edge length in natural units (normalized to 1) -/
noncomputable def intrinsicEdgeLength : ℝ := 1

/-- Intrinsic center-to-vertex distance -/
noncomputable def intrinsicCenterToVertex : ℝ := 1

/-- Intrinsic diagonal distance: 2/√3 -/
noncomputable def intrinsicDiagonalDistance : ℝ := 2 / Real.sqrt 3

/-! ### Stella Octangula Boundary Geometry (Definition 0.1.1)

    The stella octangula boundary ∂S = ∂T₊ ⊔ ∂T₋ is the disjoint union
    of two interpenetrating tetrahedra (NOT an octahedron):
    - V = 8 vertices (4 + 4), E = 12 edges (6 + 6), F = 8 faces (4 + 4)
    - Connected components: 2 (topologically two S²)
    - Euler characteristic χ = 4 (two S², each χ = 2)
    - Edge length a = 2R√6/3 (each tetrahedron, circumradius R)
    - Surface area A = (16√3/3) R² (total for both tetrahedra)

    IMPORTANT: The stella octangula is a compound of two tetrahedra,
    not a regular octahedron. See CLAUDE.md for canonical reference.

    Reference: Definition 0.1.1, Proposition 0.0.17z1
-/

/-- Number of faces of the stella octangula boundary (4 per tetrahedron × 2) -/
def stella_boundary_faces : ℕ := 8

/-- Number of edges of the stella octangula boundary -/
def stella_boundary_edges : ℕ := 12

/-- Number of vertices of the stella octangula boundary (4 per tetrahedron × 2) -/
def stella_boundary_vertices : ℕ := 8

/-- Euler characteristic of the stella boundary: χ(∂S) = χ(∂T₊) + χ(∂T₋) = 2 + 2 = 4.
    Direct count: V - E + F = 8 - 12 + 8 = 4. (Definition 0.1.1) -/
def stella_boundary_euler_char : ℤ := 4

/-- Euler characteristic from vertex/edge/face count -/
theorem stella_boundary_euler_from_VEF :
    (stella_boundary_vertices : ℤ) - stella_boundary_edges + stella_boundary_faces
    = stella_boundary_euler_char := by
  unfold stella_boundary_vertices stella_boundary_edges stella_boundary_faces
    stella_boundary_euler_char
  norm_num

/-- Tetrahedral dihedral angle: arccos(1/3) ≈ 70.53°.

    **Citation:** Coxeter, Regular Polytopes §2.3 -/
noncomputable def theta_T : ℝ := Real.arccos (1/3)

/-- Octahedral dihedral angle: arccos(-1/3) = π - arccos(1/3) ≈ 109.47°. -/
noncomputable def theta_O : ℝ := Real.pi - theta_T

/-- Effective edge length coefficient: L_eff / R = 12 × (2√6/3) × (π - arccos(1/3))/(2π) ≈ 5.960.

    Two disjoint tetrahedra with edge length a = 2R√6/3, dihedral angle θ_T = arccos(1/3).
    Reference: Proposition 0.0.17z1, §2.3 -/
noncomputable def L_eff_over_R : ℝ :=
  12 * (2 * Real.sqrt 6 / 3) * (Real.pi - Real.arccos (1/3)) / (2 * Real.pi)

/-- Surface area coefficient: A / R² = 16√3/3 ≈ 9.238.

    Two tetrahedra with circumradius R, edge a = 2R√6/3.
    Each face: (√3/4)a² = (2√3/3)R². Per tetrahedron: (8√3/3)R². Total: (16√3/3)R².
    Reference: Definition 0.1.1 -/
noncomputable def stella_surface_area_coeff : ℝ := 16 * Real.sqrt 3 / 3

/-- Stella volume coefficient: V_stella / R³ = 2√2/3 ≈ 0.943.

    Reference: Proposition 0.0.17z1, §2.5 -/
noncomputable def stella_volume_coeff : ℝ := 2 * Real.sqrt 2 / 3

/-! ### FCC Honeycomb Combinatorics (Theorem 0.0.6, Proposition 2.5.2b)

    The tetrahedral-octahedral honeycomb (FCC dual) has per primitive unit cell:
    - V = 1 vertex (FCC lattice point)
    - E = 6 edges
    - F = 8 distinct triangular faces
    - C = 3 cells (2 tetrahedra + 1 octahedron)

    For N unit cells: V = N, E = 6N, F = 8N, C = 3N
    2-skeleton Euler characteristic: χ₂ = V - E + F = 3N (i.e., 3 per cell)
    3D Euler characteristic: χ₃ = V - E + F - C = 0 (consistent with T³)

    Reference: Proposition 2.5.2b §3.5, §3.9; Theorem 0.0.6
-/

/-- FCC vertices per primitive unit cell -/
def fcc_vertices_per_cell : ℕ := 1

/-- FCC edges per primitive unit cell -/
def fcc_edges_per_cell : ℕ := 6

/-- FCC distinct triangular faces per primitive unit cell -/
def fcc_faces_per_cell : ℕ := 8

/-- FCC cells per primitive unit cell (2 tetrahedra + 1 octahedron) -/
def fcc_cells_per_cell : ℕ := 3

/-- Tetrahedra per primitive unit cell -/
def fcc_tetrahedra_per_cell : ℕ := 2

/-- Octahedra per primitive unit cell -/
def fcc_octahedra_per_cell : ℕ := 1

/-- Cell composition: 2 tet + 1 oct = 3 cells per unit cell -/
theorem fcc_cell_composition :
    fcc_tetrahedra_per_cell + fcc_octahedra_per_cell = fcc_cells_per_cell := rfl

/-- FCC 2-skeleton Euler characteristic per unit cell: 1 - 6 + 8 = 3 -/
def fcc_chi2_per_cell : ℤ := 3

/-- Euler characteristic from V, E, F per cell -/
theorem fcc_chi2_from_VEF :
    (fcc_vertices_per_cell : ℤ) - fcc_edges_per_cell + fcc_faces_per_cell
    = fcc_chi2_per_cell := by
  unfold fcc_vertices_per_cell fcc_edges_per_cell fcc_faces_per_cell
    fcc_chi2_per_cell
  norm_num

/-- 3D Euler characteristic per cell: V - E + F - C = 1 - 6 + 8 - 3 = 0 -/
theorem fcc_chi3_per_cell :
    (fcc_vertices_per_cell : ℤ) - fcc_edges_per_cell + fcc_faces_per_cell
    - fcc_cells_per_cell = 0 := by
  unfold fcc_vertices_per_cell fcc_edges_per_cell fcc_faces_per_cell
    fcc_cells_per_cell
  norm_num

/-- Face count from cell-face incidences.
    Each tet has 4 faces, each oct has 8 faces, each face shared by 2 cells.
    (4 × 2 + 8 × 1) / 2 = 8 per unit cell. -/
theorem fcc_face_count_from_incidences :
    (4 * fcc_tetrahedra_per_cell + 8 * fcc_octahedra_per_cell) / 2
    = fcc_faces_per_cell := by
  unfold fcc_tetrahedra_per_cell fcc_octahedra_per_cell fcc_faces_per_cell
  norm_num

/-! ### FCC Wilson Fermion Parameters (Proposition 7.9.1)

    Wilson fermion construction on the FCC lattice.
    The critical hopping parameter κ_c = 1/(2d) where d is the number
    of positive direction pairs (6 for FCC, 4 for hypercubic).

    Reference: Proposition 7.9.1 §1 Part (a); Wilson (1977)
-/

/-- Number of positive FCC direction pairs: 6 (from 12 nearest neighbors).

    The FCC lattice has 12 nearest neighbors per site, giving 6 positive
    direction pairs α = 1,...,6. The Wilson-Dirac operator sums over these.

    **Comparison:** Hypercubic lattice has 4 positive directions (d=4).

    **Citation:** Proposition 7.9.1, Eq. (1.1) -/
def fcc_positive_direction_pairs : ℕ := 6

/-- fcc_positive_direction_pairs = 6 -/
theorem fcc_positive_direction_pairs_value : fcc_positive_direction_pairs = 6 := rfl

/-- FCC coordination = 2 × positive directions -/
theorem fcc_coordination_from_directions :
    2 * fcc_positive_direction_pairs = 12 := rfl

/-- Critical hopping parameter for FCC lattice: κ_c = 1/12.

    **Derivation:** κ_c = 1/(2d) where d = 6 positive FCC direction pairs.
    At κ = κ_c, the bare fermion mass vanishes (chiral limit).

    **Comparison:** Hypercubic (d=4): κ_c = 1/8 = 0.125.
    Ratio: κ_c^FCC / κ_c^hyp = (1/12)/(1/8) = 2/3.

    **Citation:** Proposition 7.9.1 §1 Part (a)(ii); Wilson (1977) -/
noncomputable def kappa_c_FCC : ℝ := 1 / 12

/-- κ_c^FCC > 0 -/
theorem kappa_c_FCC_pos : kappa_c_FCC > 0 := by
  unfold kappa_c_FCC; norm_num

/-- κ_c^FCC = 1/(2 × 6) -/
theorem kappa_c_FCC_from_directions : kappa_c_FCC = 1 / (2 * fcc_positive_direction_pairs) := by
  unfold kappa_c_FCC fcc_positive_direction_pairs; norm_num

/-- Critical hopping parameter for hypercubic lattice: κ_c = 1/8.

    **Derivation:** κ_c = 1/(2d) where d = 4 positive directions in D=4.

    **Citation:** Wilson (1977); Montvay & Münster (1994) Ch. 4 -/
noncomputable def kappa_c_hypercubic : ℝ := 1 / 8

/-- κ_c^hyp > 0 -/
theorem kappa_c_hypercubic_pos : kappa_c_hypercubic > 0 := by
  unfold kappa_c_hypercubic; norm_num

/-- Ratio κ_c^FCC / κ_c^hyp = 2/3 (FCC has smaller κ_c due to more neighbors).

    **Physical meaning:** More neighbors means the hopping expansion converges
    at a smaller κ value, so the chiral limit is reached earlier.

    **Citation:** Proposition 7.9.1 §1 Part (a)(ii); ADV-7 -/
theorem kappa_c_ratio :
    kappa_c_FCC / kappa_c_hypercubic = 2 / 3 := by
  unfold kappa_c_FCC kappa_c_hypercubic; norm_num

/-- FCC shortest closed loop has 3 links (triangular plaquette).

    **Comparison:** Hypercubic shortest loop has 4 links (square plaquette).
    This affects the leading term in the hopping expansion: κ^3 vs κ^4.

    **Citation:** Proposition 7.9.1 §1 Part (b)(iii) -/
def fcc_shortest_loop_length : ℕ := 3

/-- Hypercubic shortest loop has 4 links -/
def hypercubic_shortest_loop_length : ℕ := 4

/-- Asymptotic freedom boundary: N_f < 11N_c/2.

    For SU(3): N_f < 16.5, so N_f ≤ 16 (integer).
    β₀ > 0 ⟺ 11N_c - 2N_f > 0 ⟺ N_f < 11N_c/2.

    **Citation:** Gross & Wilczek (1973); Proposition 7.9.1 Eq. (1.6) -/
noncomputable def AF_boundary_Nf : ℝ := 11 * (N_c : ℝ) / 2

/-- AF boundary for SU(3) = 16.5 -/
theorem AF_boundary_Nf_value : AF_boundary_Nf = 16.5 := by
  unfold AF_boundary_Nf N_c; norm_num

/-- Maximum integer N_f preserving asymptotic freedom for SU(3) -/
def AF_max_integer_Nf : ℕ := 16

/-- Gluon condensate in GeV⁴ (SVZ convention: ⟨g²G²⟩).

    **Value:** 0.012 ± 0.006 GeV⁴
    **Citation:** SVZ 1979, lattice QCD confirmations -/
noncomputable def gluon_condensate_GeV4 : ℝ := 0.012

/-- Gluon condensate > 0 -/
theorem gluon_condensate_pos : gluon_condensate_GeV4 > 0 := by
  unfold gluon_condensate_GeV4; norm_num

/-- One-loop beta function coefficient numerator: b₀ = 11N_c/3 - 2N_f/3.

    For SU(3) with N_f = 3: b₀ = 11 - 2 = 9.
    This is the coefficient appearing in the instanton measure as ρ^{b₀-5}.

    The full beta function coefficient is b₀/(16π²).

    Reference: Proposition 0.0.17z1, §9.2; Gross & Wilczek 1973 -/
def b0_integer : ℕ := 11 * N_c / 3 - 2 * N_f / 3

/-- b₀ = 9 for SU(3) with N_f = 3 -/
theorem b0_integer_value : b0_integer = 9 := by
  unfold b0_integer N_c N_f; norm_num

end ChiralGeometrogenesis.Constants
