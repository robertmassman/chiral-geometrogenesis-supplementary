#!/usr/bin/env python3
"""
Candidate 2 Investigation: Direct Stella → Gravity Path
========================================================

Investigates whether a direct route from the stella octangula's discrete
geometry to gravitational physics exists, BYPASSING the QCD intermediate step.

Five concrete mechanisms are tested:
  2a. Regge calculus on stella boundary
  2b. Ponzano-Regge / Turaev-Viro partition function
  2c. Spectral geometry of stella graph
  2d. Conical defect interpretation (3D gravity)
  2e. Inter-tetrahedral coupling as gravitational seed

Related Documents:
- Research: docs/proofs/supporting/Research-Absolute-Scale-Determination-Paths.md
- Thm 5.2.1: Emergent metric
- Thm 5.2.4: Newton's constant from chiral parameters
- Thm 5.2.6: Planck mass emergence

Date: 2026-03-29
"""

import numpy as np
import json
from datetime import datetime

# =============================================================================
# SECTION 0: Stella Octangula Geometry (Explicit Coordinates)
# =============================================================================

def stella_coordinates(edge_length=1.0):
    """
    Compute explicit vertex coordinates for stella octangula.

    Two regular tetrahedra T₊ and T₋ inscribed in a cube of side s.
    Tetrahedron edge length a = s√2, so s = a/√2.
    """
    a = edge_length
    s = a / np.sqrt(2)  # cube side length

    # T₊ vertices (one tetrahedron inscribed in cube)
    T_plus = np.array([
        [0, 0, 0],
        [s, s, 0],
        [s, 0, s],
        [0, s, s]
    ], dtype=float)

    # T₋ vertices (dual tetrahedron)
    T_minus = np.array([
        [s, 0, 0],
        [0, s, 0],
        [0, 0, s],
        [s, s, s]
    ], dtype=float)

    # Edges (vertex index pairs) for each tetrahedron
    tet_edges = [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

    # Faces (vertex index triples) for each tetrahedron
    tet_faces = [(0,1,2), (0,1,3), (0,2,3), (1,2,3)]

    # Verify edge lengths
    for i, j in tet_edges:
        d_plus = np.linalg.norm(T_plus[i] - T_plus[j])
        d_minus = np.linalg.norm(T_minus[i] - T_minus[j])
        assert abs(d_plus - a) < 1e-10, f"T₊ edge ({i},{j}) length {d_plus} ≠ {a}"
        assert abs(d_minus - a) < 1e-10, f"T₋ edge ({i},{j}) length {d_minus} ≠ {a}"

    return {
        'T_plus': T_plus,
        'T_minus': T_minus,
        'edges': tet_edges,
        'faces': tet_faces,
        'edge_length': a,
        'cube_side': s
    }


def intersection_octahedron(stella):
    """
    Compute the regular octahedron formed by T₊ ∩ T₋.

    The intersection of two dual tetrahedra inscribed in a cube
    is a regular octahedron with vertices at edge midpoints of the cube.
    """
    s = stella['cube_side']
    a = stella['edge_length']

    # Octahedron vertices: midpoints of cube edges where tetrahedra intersect
    # These are the 6 face-centers of the cube
    oct_vertices = np.array([
        [s/2, 0, s/2],    # midpoint of cube edge
        [s/2, s, s/2],
        [0, s/2, s/2],
        [s, s/2, s/2],
        [s/2, s/2, 0],
        [s/2, s/2, s]
    ])

    # Octahedron edge length
    a_oct = np.linalg.norm(oct_vertices[0] - oct_vertices[2])

    # Volumes
    V_tet = a**3 / (6 * np.sqrt(2))                  # single tetrahedron
    V_oct = np.sqrt(2) / 3 * a_oct**3                 # octahedron
    V_cube = s**3
    V_union = 2 * V_tet - V_oct                       # inclusion-exclusion

    return {
        'oct_vertices': oct_vertices,
        'oct_edge_length': a_oct,
        'ratio_a_oct_to_a_tet': a_oct / a,
        'V_tetrahedron': V_tet,
        'V_octahedron': V_oct,
        'V_cube': V_cube,
        'V_union': V_union,
        'V_overlap_over_V_tet': V_oct / V_tet,
        'V_overlap_over_V_union': V_oct / V_union,
        'V_union_over_V_cube': V_union / V_cube,
    }


# =============================================================================
# SECTION 2a: Regge Calculus on Stella Boundary
# =============================================================================

def regge_calculus_stella():
    """
    2D Regge calculus on the stella boundary ∂S = ∂T₊ ⊔ ∂T₋.

    Each tetrahedron triangulates S². The 2D Regge action equals
    the total deficit angle, which by discrete Gauss-Bonnet equals 2πχ.

    Key result: The Regge action is TOPOLOGICAL (independent of edge length a).
    """
    print("=" * 70)
    print("INVESTIGATION 2a: Regge Calculus on Stella Boundary")
    print("=" * 70)

    # For each regular tetrahedron triangulating S²:
    # - 4 vertices, 6 edges, 4 equilateral triangular faces
    # - Internal angle of equilateral triangle: π/3
    # - At each vertex: 3 faces meet, each contributing angle π/3
    # - Angle sum at each vertex: 3 × π/3 = π
    # - Deficit angle at each vertex: ε_v = 2π - π = π

    n_vertices_per_tet = 4
    faces_per_vertex = 3
    angle_per_face = np.pi / 3

    angle_sum_at_vertex = faces_per_vertex * angle_per_face
    deficit_angle = 2 * np.pi - angle_sum_at_vertex

    print(f"\nPer tetrahedron (triangulation of S²):")
    print(f"  Angle sum at each vertex: {faces_per_vertex} × π/3 = π = {angle_sum_at_vertex:.6f}")
    print(f"  Deficit angle at each vertex: 2π - π = π = {deficit_angle:.6f}")

    # Total curvature per tetrahedron
    total_curvature_per_tet = n_vertices_per_tet * deficit_angle
    print(f"  Total curvature: 4 × π = 4π = {total_curvature_per_tet:.6f}")
    print(f"  Expected (2πχ(S²) = 4π): {2 * np.pi * 2:.6f}")
    print(f"  Match: {abs(total_curvature_per_tet - 4*np.pi) < 1e-10}")

    # For the stella (two tetrahedra):
    total_curvature_stella = 2 * total_curvature_per_tet
    chi_stella = 4
    expected_curvature = 2 * np.pi * chi_stella

    print(f"\nFor stella octangula (∂T₊ ⊔ ∂T₋):")
    print(f"  Total deficit angle: 2 × 4π = 8π = {total_curvature_stella:.6f}")
    print(f"  Expected (2πχ = 2π×4 = 8π): {expected_curvature:.6f}")
    print(f"  Match: {abs(total_curvature_stella - expected_curvature) < 1e-10}")

    # 2D Einstein-Hilbert action
    # S_2D = (1/16πG_2D) ∫ R √g d²x = (1/16πG_2D) × 4πχ = χ/(4G_2D)
    # Setting S_2D = Σ ε_v = 2πχ:
    # χ/(4G_2D) = 2πχ → G_2D = 1/(8π)
    G_2D = 1 / (8 * np.pi)

    print(f"\n2D Newton's constant from Regge action:")
    print(f"  G_2D = 1/(8π) = {G_2D:.6f}")
    print(f"  This is DIMENSIONLESS — purely topological, no scale information.")

    # Dihedral angles of the tetrahedron (for 3D Regge calculus context)
    dihedral_angle = np.arccos(1/3)
    print(f"\nDihedral angle of regular tetrahedron: arccos(1/3) = {np.degrees(dihedral_angle):.4f}°")
    print(f"  = {dihedral_angle:.6f} rad")

    result = {
        'deficit_angle_per_vertex': deficit_angle,
        'total_curvature_per_tet': total_curvature_per_tet,
        'total_curvature_stella': total_curvature_stella,
        'gauss_bonnet_check': abs(total_curvature_stella - expected_curvature) < 1e-10,
        'G_2D': G_2D,
        'dihedral_angle_rad': dihedral_angle,
        'dihedral_angle_deg': np.degrees(dihedral_angle),
        'conclusion': 'TOPOLOGICAL ONLY — 2D Regge gravity on ∂S gives '
                      'G_2D = 1/(8π), a pure number. No absolute scale information.',
        'breaks_projective_ambiguity': False
    }

    print(f"\n  CONCLUSION: {result['conclusion']}")
    return result


# =============================================================================
# SECTION 2b: Ponzano-Regge / Turaev-Viro Partition Function
# =============================================================================

def quantum_6j_symbol_symmetric(j):
    """
    Compute the totally symmetric 6j symbol {j j j; j j j} for small j.

    Uses explicit formulas for low spins.
    """
    if j == 0:
        return 1.0
    elif j == 0.5:
        # {1/2 1/2 1/2; 1/2 1/2 1/2} = 1/(2√2) (Varshalovich, Table 9.7)
        return 1 / (2 * np.sqrt(2))
    elif j == 1:
        # {1 1 1; 1 1 1} = 1/6 (Varshalovich)
        return 1 / 6
    elif j == 1.5:
        # {3/2 3/2 3/2; 3/2 3/2 3/2} = -1/(5√(70)) ≈ -0.0239 (Varshalovich)
        return -1 / (5 * np.sqrt(70))
    elif j == 2:
        # {2 2 2; 2 2 2} = 1/70
        return 1 / 70
    else:
        # Asymptotic form for large j (Ponzano-Regge):
        # {j j j; j j j} ~ (1/(12π V)) cos(S_Regge + π/4)
        # For regular tetrahedron: V = a³/(6√2) with a = 2j+1
        a_eff = 2 * j + 1
        V = a_eff**3 / (6 * np.sqrt(2))
        # Regge action for regular tetrahedron
        dihedral = np.arccos(1/3)
        S_regge = 6 * a_eff * dihedral  # 6 edges × length × deficit at each
        return (1 / (12 * np.pi * V)) * np.cos(S_regge + np.pi / 4)


def ponzano_regge_stella():
    """
    Ponzano-Regge partition function for the stella octangula.

    The PR model is a state sum model for 3D quantum gravity:
    Z_PR = Σ_j Π_edges (2j+1) × Π_tetrahedra {6j}

    For the stella with all edges carrying spin j:
    Z_stella(j) = (2j+1)^12 × [{j j j; j j j}]²

    The Turaev-Viro model regulates the divergence by setting q = exp(2πi/(k+2)).
    """
    print("\n" + "=" * 70)
    print("INVESTIGATION 2b: Ponzano-Regge / Turaev-Viro Partition Function")
    print("=" * 70)

    # Compute PR amplitudes for small spins
    print("\nPonzano-Regge amplitudes Z_stella(j) = (2j+1)^12 × [{6j}]²:")
    print(f"{'j':>5} {'(2j+1)^12':>15} {'{6j}':>15} {'Z_stella(j)':>15}")
    print("-" * 55)

    pr_amplitudes = {}
    for j_half in range(0, 9):  # j = 0, 0.5, 1, ..., 4
        j = j_half / 2
        dim = 2 * j + 1
        sixj = quantum_6j_symbol_symmetric(j)
        Z_j = dim**12 * sixj**2
        pr_amplitudes[j] = Z_j
        print(f"{j:5.1f} {dim**12:15.4f} {sixj:15.6f} {Z_j:15.6f}")

    # The key observation: ALL amplitudes are PURE NUMBERS
    print(f"\n  Key observation: Every Z_stella(j) is a pure number.")
    print(f"  The Ponzano-Regge model computes DIMENSIONLESS amplitudes.")

    # Turaev-Viro at level k = χ = 4
    k = 4
    print(f"\nTuraev-Viro model at k = χ = {k}:")
    print(f"  q = exp(2πi/(k+2)) = exp(2πi/6) = exp(iπ/3)")
    print(f"  Allowed spins: j ∈ {{0, 1/2, 1, 3/2, 2}} (k/2 = 2 max)")

    # Quantum dimensions [2j+1]_q at q = exp(iπ/3)
    q = np.exp(1j * np.pi / 3)

    def quantum_dim(j, q):
        """Compute quantum dimension [2j+1]_q = sin((2j+1)π/(k+2)) / sin(π/(k+2))"""
        n = int(2 * j + 1)
        kp2 = k + 2  # = 6
        return np.sin(n * np.pi / kp2) / np.sin(np.pi / kp2)

    print(f"\n  Quantum dimensions [2j+1]_q:")
    total_qdim_sq = 0
    for j_half in range(0, 5):
        j = j_half / 2
        qd = quantum_dim(j, q)
        total_qdim_sq += qd**2
        print(f"    j = {j:.1f}: [2j+1]_q = {qd:.6f}")

    # Total quantum dimension
    D_squared = total_qdim_sq
    D = np.sqrt(D_squared)
    print(f"\n  Total quantum dimension D² = Σ [2j+1]_q² = {D_squared:.6f}")
    print(f"  D = {D:.6f}")

    # Compare with k+2 / (2 sin²(π/(k+2)))
    D_sq_formula = (k + 2) / (2 * np.sin(np.pi / (k + 2))**2)
    print(f"  Formula: (k+2)/(2sin²(π/(k+2))) = {D_sq_formula:.6f}")
    print(f"  Match: {abs(D_squared - D_sq_formula) < 1e-6}")

    # TV partition function for stella
    # Z_TV = D^(2(V-1)) × Σ_j [quantum dims and quantum 6j symbols]
    V_stella = 8
    normalization_power = 2 * (V_stella - 1)
    print(f"\n  Normalization factor: D^(2(V-1)) = D^{normalization_power} = {D**normalization_power:.6f}")

    print(f"\n  The Turaev-Viro invariant Z_TV(∂S; k=4) is a TOPOLOGICAL INVARIANT.")
    print(f"  It depends only on χ=4 and the Chern-Simons level k=4.")
    print(f"  It is a pure number — NO scale information.")

    # Connection to cosmological constant
    Lambda_TV = (2 * np.pi / (k + 2))**2  # in Planck units
    print(f"\n  Effective cosmological constant: Λ_TV = (2π/(k+2))² = {Lambda_TV:.6f} (Planck units)")
    print(f"  This sets Λ in PLANCK units — l_P is still needed as input!")

    result = {
        'pr_amplitudes': {str(k): float(v) for k, v in pr_amplitudes.items()},
        'tv_level': k,
        'total_quantum_dimension_sq': float(D_squared),
        'total_quantum_dimension': float(D),
        'Lambda_TV_planck_units': float(Lambda_TV),
        'conclusion': 'ALL quantities are dimensionless. The Ponzano-Regge and '
                      'Turaev-Viro models compute topological invariants that '
                      'cannot fix an absolute scale. The cosmological constant '
                      'Λ_TV is in Planck units, requiring l_P as input.',
        'breaks_projective_ambiguity': False
    }

    print(f"\n  CONCLUSION: {result['conclusion']}")
    return result


# =============================================================================
# SECTION 2c: Spectral Geometry of Stella Graph
# =============================================================================

def spectral_geometry_stella():
    """
    Compute the graph Laplacian spectrum of the stella octangula.

    The graph Laplacian L = D - A (degree matrix minus adjacency matrix)
    encodes how information propagates on the stella. Its eigenvalues
    are related to effective dimension, connectivity, and (in some models)
    gravitational parameters.
    """
    print("\n" + "=" * 70)
    print("INVESTIGATION 2c: Spectral Geometry of Stella Graph")
    print("=" * 70)

    stella = stella_coordinates()
    T_plus = stella['T_plus']
    T_minus = stella['T_minus']

    # Full stella graph: 8 vertices, edges within each tetrahedron
    # Vertices 0-3 = T₊, vertices 4-7 = T₋
    # Each tetrahedron is a complete graph K₄

    # Adjacency matrix (8×8)
    A = np.zeros((8, 8))

    # T₊ edges (vertices 0-3): complete graph
    for i in range(4):
        for j in range(i+1, 4):
            A[i, j] = 1
            A[j, i] = 1

    # T₋ edges (vertices 4-7): complete graph
    for i in range(4, 8):
        for j in range(i+1, 8):
            A[i, j] = 1
            A[j, i] = 1

    # NOTE: No edges between T₊ and T₋ (disjoint boundary components)

    # Degree matrix
    D = np.diag(A.sum(axis=1))

    # Graph Laplacian
    L = D - A

    print("\nGraph Laplacian of stella octangula (combinatorial, no inter-tet edges):")

    # Eigenvalues
    eigenvalues = np.linalg.eigvalsh(L)
    print(f"\n  Eigenvalues: {np.round(eigenvalues, 6)}")

    # For two disjoint K₄ graphs:
    # K₄ eigenvalues of Laplacian: 0, 4, 4, 4 (0 with multiplicity 1, 4 with multiplicity 3)
    # So stella = K₄ ⊔ K₄: eigenvalues are {0, 0, 4, 4, 4, 4, 4, 4}
    print(f"  Expected (K₄ ⊔ K₄): [0, 0, 4, 4, 4, 4, 4, 4]")

    # Number of zero eigenvalues = number of connected components
    n_zeros = np.sum(np.abs(eigenvalues) < 1e-10)
    print(f"  Number of zero eigenvalues: {n_zeros} (= number of connected components)")

    # Spectral gap (smallest nonzero eigenvalue)
    nonzero_eigs = eigenvalues[eigenvalues > 1e-10]
    spectral_gap = nonzero_eigs[0] if len(nonzero_eigs) > 0 else 0
    print(f"  Spectral gap: λ₁ = {spectral_gap:.6f}")

    # Heat kernel trace: K(t) = Σ exp(-λ_i t)
    # Related to spectral dimension: d_s(t) = -2 d(ln K)/d(ln t)
    print(f"\nHeat kernel analysis:")
    t_values = np.logspace(-2, 2, 50)
    heat_kernel = np.array([np.sum(np.exp(-eigenvalues * t)) for t in t_values])

    # Spectral dimension
    log_t = np.log(t_values)
    log_K = np.log(heat_kernel)
    d_spectral = -2 * np.gradient(log_K, log_t)

    print(f"  Spectral dimension at small t (UV): d_s → {d_spectral[0]:.4f}")
    print(f"  Spectral dimension at large t (IR): d_s → {d_spectral[-1]:.4f}")
    print(f"  Peak spectral dimension: {np.max(d_spectral):.4f}")

    # Now consider the AUGMENTED graph with inter-tetrahedral connections
    # based on geometric proximity (nearest-neighbor between T₊ and T₋)
    print(f"\n--- Augmented graph (with inter-tetrahedral edges) ---")

    A_aug = A.copy()

    # Connect each T₊ vertex to nearest T₋ vertices
    # In the stella, each T₊ vertex faces a T₋ face (3 vertices)
    # Geometric distances:
    for i in range(4):
        for j in range(4):
            d = np.linalg.norm(T_plus[i] - T_minus[j])
            # Nearest-neighbor distance = edge_length / √2 (for adjacent vertices)
            if d < stella['edge_length'] * 0.8:  # nearest neighbors
                A_aug[i, j+4] = 1
                A_aug[j+4, i] = 1

    n_inter_edges = int((A_aug.sum() - A.sum()) / 2)
    print(f"  Inter-tetrahedral edges added: {n_inter_edges}")

    D_aug = np.diag(A_aug.sum(axis=1))
    L_aug = D_aug - A_aug
    eigs_aug = np.linalg.eigvalsh(L_aug)
    print(f"  Augmented eigenvalues: {np.round(eigs_aug, 6)}")

    n_zeros_aug = np.sum(np.abs(eigs_aug) < 1e-10)
    print(f"  Connected components: {n_zeros_aug}")

    # Spectral dimension of augmented graph
    heat_kernel_aug = np.array([np.sum(np.exp(-eigs_aug * t)) for t in t_values])
    log_K_aug = np.log(np.maximum(heat_kernel_aug, 1e-100))
    d_spectral_aug = -2 * np.gradient(log_K_aug, log_t)

    print(f"  Spectral dimension (UV): {d_spectral_aug[0]:.4f}")
    print(f"  Peak spectral dimension: {np.max(d_spectral_aug):.4f}")

    # The key point: ALL eigenvalues are pure numbers (integers for K₄)
    print(f"\n  Key observation:")
    print(f"  All Laplacian eigenvalues are INTEGERS: {sorted(set(np.round(eigenvalues).astype(int)))}")
    print(f"  The spectrum encodes CONNECTIVITY, not metric size.")
    print(f"  Under rescaling a → λa, the Laplacian scales as L → L/λ² if")
    print(f"  we use the metric Laplacian. But the combinatorial Laplacian is")
    print(f"  scale-independent — it sees only topology.")

    result = {
        'eigenvalues_disjoint': eigenvalues.tolist(),
        'eigenvalues_augmented': eigs_aug.tolist(),
        'spectral_gap': float(spectral_gap),
        'n_connected_components_disjoint': int(n_zeros),
        'n_connected_components_augmented': int(n_zeros_aug),
        'spectral_dimension_UV': float(d_spectral[0]),
        'spectral_dimension_IR': float(d_spectral[-1]),
        'n_inter_tet_edges': n_inter_edges,
        'conclusion': 'Graph Laplacian eigenvalues are integers (pure numbers). '
                      'The combinatorial spectrum encodes connectivity/topology, '
                      'not metric size. No absolute scale information.',
        'breaks_projective_ambiguity': False
    }

    print(f"\n  CONCLUSION: {result['conclusion']}")
    return result


# =============================================================================
# SECTION 2d: Conical Defect Interpretation (3D Gravity)
# =============================================================================

def conical_defect_stella():
    """
    Interpret the stella octangula as a conical defect in 3D gravity.

    In 2+1D gravity, point particles create conical defects:
      deficit angle = 8πGm (in units where c=1)

    The stella's boundary has total curvature 8π (from Gauss-Bonnet with χ=4).
    If we interpret this as a gravitational defect, we get G × m_total = 1.
    """
    print("\n" + "=" * 70)
    print("INVESTIGATION 2d: Conical Defect in 3D Gravity")
    print("=" * 70)

    chi = 4
    total_deficit = 2 * np.pi * chi  # = 8π

    print(f"\nTotal deficit angle of stella boundary: 2πχ = 2π×{chi} = 8π = {total_deficit:.6f}")

    # In 3D gravity: deficit angle = 8πG₃m at each point source
    # Total: Σ ε_v = 8πG₃ × m_total
    # So: 8π = 8πG₃ × m_total → G₃ × m_total = 1

    print(f"\n  In 2+1D gravity with point particles:")
    print(f"  Σ ε_v = 8πG₃ × m_total")
    print(f"  8π = 8πG₃ × m_total")
    print(f"  → G₃ × m_total = 1")

    print(f"\n  This constrains the PRODUCT G₃m, not G₃ or m individually.")
    print(f"  Under rescaling: G₃ → λG₃, m → m/λ preserves G₃m = 1.")

    # In 3+1D, the situation is different
    # The Regge action for 4D gravity has deficit angles at TRIANGLES (codim-2 hinges)
    # Not at vertices
    print(f"\n  In 3+1D gravity:")
    print(f"  The stella boundary is 2-dimensional → relevant for 2+1D gravity.")
    print(f"  For 3+1D, we'd need a 3-dimensional triangulation (deficit at 2-faces).")
    print(f"  The stella provides a BOUNDARY, not a bulk triangulation.")

    # Maximum deficit angle constraint
    # In 3D gravity: total deficit < 4π for single surface
    # Stella: total deficit = 8π = 2 × 4π (two S² components)
    # Each component has deficit 4π, which is the MAXIMUM for a closed surface in 3D
    # (a closed surface with χ=2 has exactly 4π total curvature)
    print(f"\n  Each S² component has curvature 4π (the maximum for a closed 2-surface).")
    print(f"  This means each tetrahedron represents a MAXIMALLY CURVED 2-sphere.")

    # Deficit at individual vertices
    deficit_per_vertex = np.pi  # each vertex has deficit π
    # In 3D gravity: ε_v = 8πG₃m_v
    # So: π = 8πG₃m_v → G₃m_v = 1/8

    print(f"\n  Per vertex: deficit = π → G₃m_v = 1/8")
    print(f"  8 vertices × 1/8 = 1 ✓ (consistent with G₃m_total = 1)")

    # The N_c dependence
    N_c = 3
    print(f"\n  Possible N_c connection:")
    print(f"  Vertices = 2N_c + 2 = 8 for N_c = 3")
    print(f"  G₃m per vertex = 1/(2N_c + 2) = 1/8")
    print(f"  This gives G₃ × m_total = 1 for ANY N_c → UNIVERSAL, not SU(3)-specific")

    result = {
        'total_deficit': float(total_deficit),
        'G3_times_m_total': 1.0,
        'G3_times_m_per_vertex': 1/8,
        'n_vertices': 8,
        'chi': chi,
        'conclusion': 'The conical defect interpretation gives G₃m = 1, '
                      'constraining only the PRODUCT of G and m. The projective '
                      'ambiguity (G→λG, m→m/λ) is an exact symmetry. '
                      'Furthermore, the result G₃m=1 follows from Gauss-Bonnet '
                      'and is universal for ANY 2-surface with χ=4.',
        'breaks_projective_ambiguity': False,
        'novel_insight': 'Each vertex carries G₃m_v = 1/8 = 1/(2N_c+2). '
                         'This is a potentially interesting relation between '
                         'vertex count (topology) and gravitational charge, but '
                         'it follows trivially from χ=4 and uniform distribution.'
    }

    print(f"\n  CONCLUSION: {result['conclusion']}")
    return result


# =============================================================================
# SECTION 2e: Inter-Tetrahedral Coupling as Gravitational Seed
# =============================================================================

def inter_tetrahedral_coupling():
    """
    Investigate whether gravity emerges from the INTERACTION between T₊ and T₋,
    independent of the QCD dynamics on each tetrahedron.

    Idea: T₊ and T₋ represent two chiralities. Their geometric interpenetration
    defines an interaction energy. If this energy depends on the stella's size
    in a non-homogeneous way, it could break the projective ambiguity.
    """
    print("\n" + "=" * 70)
    print("INVESTIGATION 2e: Inter-Tetrahedral Coupling")
    print("=" * 70)

    stella = stella_coordinates(edge_length=1.0)
    oct_data = intersection_octahedron(stella)

    a = stella['edge_length']
    s = stella['cube_side']

    print(f"\nStella geometry (a = {a}):")
    print(f"  Cube side: s = a/√2 = {s:.6f}")
    print(f"  Octahedron edge: a_oct = {oct_data['oct_edge_length']:.6f}")
    print(f"  Ratio a_oct/a = {oct_data['ratio_a_oct_to_a_tet']:.6f}")

    print(f"\nVolume fractions:")
    print(f"  V(T₊ ∩ T₋)/V(T₊) = {oct_data['V_overlap_over_V_tet']:.6f}")
    print(f"  V(T₊ ∩ T₋)/V(T₊ ∪ T₋) = {oct_data['V_overlap_over_V_union']:.6f}")
    print(f"  V(T₊ ∪ T₋)/V(cube) = {oct_data['V_union_over_V_cube']:.6f}")

    # Overlap fraction
    f_overlap = oct_data['V_overlap_over_V_union']
    print(f"\n  Overlap fraction f = V(∩)/V(∪) = {f_overlap:.6f} = 1/3")
    print(f"  Check 1/3: {abs(f_overlap - 1/3) < 1e-10}")

    # Scaling analysis
    print(f"\nScaling analysis:")
    print(f"  Under a → λa:")
    print(f"  V(T₊) → λ³ V(T₊)")
    print(f"  V(T₊ ∩ T₋) → λ³ V(T₊ ∩ T₋)")
    print(f"  Overlap fraction f → f (INVARIANT)")
    print(f"  → All volume ratios are scale-invariant.")

    # Surface area of intersection (shared boundary)
    # The octahedral intersection has 8 triangular faces
    # Each face has area (√3/4) × a_oct²
    a_oct = oct_data['oct_edge_length']
    area_oct_face = np.sqrt(3) / 4 * a_oct**2
    total_area_oct = 8 * area_oct_face

    # Surface areas of tetrahedra
    area_tet_face = np.sqrt(3) / 4 * a**2
    total_area_tet = 4 * area_tet_face  # per tetrahedron

    area_ratio = total_area_oct / (2 * total_area_tet)  # oct area / stella area

    print(f"\n  Area of intersection boundary (octahedron): {total_area_oct:.6f} a²")
    print(f"  Total stella surface area: {2 * total_area_tet:.6f} a²")
    print(f"  Area ratio: {area_ratio:.6f}")

    # Entanglement entropy between T₊ and T₋
    # If we place quantum fields on ∂S = ∂T₊ ⊔ ∂T₋, the entanglement
    # between the two components depends on the overlap region
    print(f"\n  Entanglement between T₊ and T₋:")
    print(f"  The two boundary components are TOPOLOGICALLY DISJOINT (∂T₊ ⊔ ∂T₋).")
    print(f"  Entanglement arises from the geometric overlap (interpenetration in ℝ³).")
    print(f"  The entanglement area = area of intersection octahedron ∝ a²")
    print(f"  S_entanglement ∝ A_oct / ε² (UV cutoff ε)")
    print(f"  This has the form S ∝ a²/ε² — homogeneous degree 0 in dimensionful quantities")
    print(f"  (when ε ∝ a, which is the natural scaling).")

    # Check: does the interaction between T₊ and T₋ give Newton's constant?
    print(f"\nCan inter-tetrahedral interaction fix G independently?")
    print(f"  Overlap volume: V_oct = {oct_data['V_octahedron']:.6f} a³")
    print(f"  If interaction energy E_int ∝ V_oct / a^d (some power d):")
    print(f"    E_int ∝ a^(3-d)")
    print(f"    Under rescaling a → λa: E_int → λ^(3-d) E_int")
    print(f"    For ANY d, this is homogeneous → projective ambiguity preserved.")

    # Novel dimensionless ratios
    print(f"\nDimensionless ratios from inter-tetrahedral geometry:")
    ratios = {
        'V_oct/V_tet': oct_data['V_overlap_over_V_tet'],
        'a_oct/a_tet': oct_data['ratio_a_oct_to_a_tet'],
        'A_oct/(2×A_tet)': area_ratio,
        'V_oct/V_cube': oct_data['V_octahedron'] / oct_data['V_cube'],
    }
    for name, val in ratios.items():
        print(f"  {name} = {val:.6f}")

    # Check if any match known gravitational ratios
    print(f"\n  Comparison with framework quantities:")
    print(f"  V_oct/V_tet = {oct_data['V_overlap_over_V_tet']:.6f}")
    print(f"  1/2 = 0.500000  (exact match!)")
    print(f"  This is GEOMETRIC, not dynamical — it's just V(octahedron)/V(tetrahedron)")
    print(f"  for dual-inscribed regular tetrahedra.")

    # The 1/3 overlap fraction
    print(f"\n  The overlap fraction V(∩)/V(∪) = 1/3 = 1/N_c")
    print(f"  Coincidence with N_c = 3? Let's check for general N_c:")
    print(f"  For a compound of two dual regular tetrahedra, the overlap fraction")
    print(f"  is ALWAYS 1/3, regardless of size or N_c.")
    print(f"  This is a geometric fact about tetrahedra, not about SU(3).")

    result = {
        'overlap_fraction': float(f_overlap),
        'area_ratio': float(area_ratio),
        'volume_ratios': {k: float(v) for k, v in ratios.items()},
        'conclusion': 'All inter-tetrahedral quantities (volumes, areas, overlaps) '
                      'are either dimensionless ratios (scale-invariant) or '
                      'homogeneous in the edge length a. No mechanism found '
                      'that breaks the projective ambiguity. The overlap '
                      'fraction V(∩)/V(∪) = 1/3 is a geometric coincidence '
                      'with 1/N_c, not a dynamical constraint.',
        'breaks_projective_ambiguity': False,
        'novel_insight': 'V(T₊∩T₋)/V(T₊∪T₋) = 1/3 = 1/N_c is geometrically '
                         'exact for dual tetrahedra. While this is a geometric '
                         'identity (not SU(3)-dependent), it is a curious '
                         'coincidence worth noting. The octahedral intersection '
                         'region, where both chiralities overlap, occupies exactly '
                         '1/N_c of the total stella volume.'
    }

    print(f"\n  CONCLUSION: {result['conclusion']}")
    return result


# =============================================================================
# SECTION 3: Synthesis — What Direct Stella → Gravity CAN Provide
# =============================================================================

def synthesis():
    """
    Synthesize findings from all five investigations.
    """
    print("\n" + "=" * 70)
    print("SYNTHESIS: What Direct Stella → Gravity Can and Cannot Provide")
    print("=" * 70)

    print("""
CANNOT provide (confirmed by investigation):
  ✗ Absolute value of Newton's constant G
  ✗ Absolute value of Planck length l_P
  ✗ Breaking of the projective ambiguity λ → λ(all scales)
  ✗ An independent equation relating G to stella geometry without QCD

CAN provide (novel results from this investigation):
  ✓ Topological gravitational content: Regge action = 8π (from χ=4)
  ✓ 2D Newton's constant: G_2D = 1/(8π) (dimensionless)
  ✓ Conical defect mass: Gm per vertex = 1/(2N_c + 2) = 1/8
  ✓ Turaev-Viro invariant at k = χ = 4 (topological partition function)
  ✓ Spectral gap of stella graph: λ₁ = 4 (complete graph K₄ per component)
  ✓ Overlap fraction: V(T₊∩T₋)/V(T₊∪T₋) = 1/3 = 1/N_c
  ✓ Confirmation that gravity CANNOT bypass QCD in this framework

WHY the projective ambiguity survives all five mechanisms:
  The fundamental reason is that the stella octangula is a FINITE
  COMBINATORIAL OBJECT. Its properties are:

  1. Topological numbers: χ=4, V=8, E=12, F=8 (all integers)
  2. Geometric ratios: dihedral angles, volume fractions (all dimensionless)
  3. Spectral data: Laplacian eigenvalues (integers for regular polyhedra)

  None of these carry DIMENSIONS. To get a dimensionful quantity (G, l_P,
  R_stella), one must combine topological numbers with a dimensionful input.
  The framework does this via dimensional transmutation:

    R_stella = (ℏc/√σ)  ←  one dimensionful input (√σ)

  The stella provides the STRUCTURE (which gauge group, which ratios),
  and one measurement provides the SCALE.

REMAINING VALUE of this investigation:
  The inter-tetrahedral geometry provides CONSISTENCY CHECKS:
  - The overlap fraction 1/3 is compatible with (but not derived from) N_c=3
  - The conical defect structure Gm_v = 1/8 per vertex is consistent with
    the framework's 8-vertex stella
  - The TV invariant at k=χ provides a quantum-gravitational partition
    function that could constrain radiative corrections to G

  These are NOT new equations that break the ambiguity, but they ARE
  cross-checks that the framework's gravitational sector is consistent
  with its topological input.
""")

    return {
        'all_mechanisms_tested': 5,
        'mechanisms_breaking_ambiguity': 0,
        'novel_dimensionless_results': [
            'G_2D = 1/(8π)',
            'Gm_per_vertex = 1/8 = 1/(2N_c+2)',
            'Overlap fraction = 1/3 = 1/N_c',
            'Spectral gap λ₁ = 4 (=N_c+1 for K_{N_c+1})',
            'TV level k = χ = 4',
        ],
        'overall_conclusion': 'CANDIDATE 2 CLOSED. No direct stella → gravity '
                              'path can bypass QCD for absolute scale determination. '
                              'All five mechanisms produce dimensionless quantities. '
                              'The projective ambiguity is confirmed robust against '
                              'discrete-geometric approaches to gravity.'
    }


# =============================================================================
# MAIN
# =============================================================================

def main():
    results = {
        'investigation': 'Candidate 2: Direct Stella → Gravity Path',
        'timestamp': datetime.now().isoformat(),
        'date': '2026-03-29',
        'sections': {}
    }

    # Run all investigations
    results['sections']['2a_regge'] = regge_calculus_stella()
    results['sections']['2b_ponzano_regge'] = ponzano_regge_stella()
    results['sections']['2c_spectral'] = spectral_geometry_stella()
    results['sections']['2d_conical_defect'] = conical_defect_stella()
    results['sections']['2e_inter_tetrahedral'] = inter_tetrahedral_coupling()
    results['sections']['synthesis'] = synthesis()

    # Overall assessment
    any_breaks = any(
        s.get('breaks_projective_ambiguity', False)
        for s in results['sections'].values()
        if isinstance(s, dict)
    )
    results['overall_status'] = 'AMBIGUITY BROKEN' if any_breaks else 'AMBIGUITY CONFIRMED ROBUST'

    # Save results
    output_file = 'candidate_2_direct_stella_gravity_results.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2, default=str)

    print(f"\n{'='*70}")
    print(f"OVERALL STATUS: {results['overall_status']}")
    print(f"Results saved to {output_file}")
    print(f"{'='*70}")

    return results


if __name__ == '__main__':
    main()
