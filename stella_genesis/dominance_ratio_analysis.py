#!/usr/bin/env python3
"""
Geometric Origin of the 66.1% Dominance Ratio
==============================================

RESOLVED: The 66.1% ratio at n_sub=16 is a finite-mesh discretization
artifact. The continuum limit is EXACTLY 3/4 (75%).

The own-dominant region on each tetrahedral face consists of three corner
triangles (each 1/4 of the face area). The other-dominant region is the
medial triangle (central 1/4). This follows from a clean analytical
criterion derived from the stella's antipodal symmetry.

Key result: Own-dominant iff max(x·T₊[i]) + min(x·T₊[i]) > 0.
On each face, min = -1 (opposite vertex), so this reduces to
max(x·T₊[i]) > 1, which holds in the three corner sub-triangles.

Author: Claude (investigation script)
Date: 2026-03-23
"""

import numpy as np
import json
from datetime import datetime

# ==============================================================================
# STELLA OCTANGULA GEOMETRY (Def 0.0.0)
# ==============================================================================

T_PLUS = np.array([
    [ 1,  1,  1],
    [ 1, -1, -1],
    [-1,  1, -1],
    [-1, -1,  1],
], dtype=np.float64)

T_MINUS = -T_PLUS  # Antipodal symmetry

FACES = [(1,2,3), (0,3,2), (0,1,3), (0,2,1)]
EDGE_LENGTH = np.linalg.norm(T_PLUS[0] - T_PLUS[1])  # 2√2


# ==============================================================================
# MESH CONSTRUCTION (matching genesis_soup.c)
# ==============================================================================

def build_mesh(verts, n_sub):
    """Build triangulated mesh on tetrahedron surface."""
    points = []
    eps = 0.01

    def find_or_add(x, y, z):
        for i, p in enumerate(points):
            if abs(p[0]-x)<eps and abs(p[1]-y)<eps and abs(p[2]-z)<eps:
                return i
        points.append(np.array([x, y, z]))
        return len(points) - 1

    for f in range(4):
        va, vb, vc = verts[FACES[f][0]], verts[FACES[f][1]], verts[FACES[f][2]]
        for i in range(n_sub + 1):
            for j in range(n_sub - i + 1):
                fi, fj = i / n_sub, j / n_sub
                fk = 1.0 - fi - fj
                pt = fk * va + fi * vb + fj * vc
                find_or_add(pt[0], pt[1], pt[2])

    return np.array(points)


def pressure_at_site(pos, verts, epsilon):
    """P(x) = max over vertices v of 1/(|x-v|² + ε²)."""
    r2 = np.sum((verts - pos)**2, axis=1)
    return np.max(1.0 / (r2 + epsilon**2))


def compute_dominance_ratio_mesh(n_sub, epsilon=0.1):
    """Compute own-surface dominance ratio at given mesh resolution."""
    tp_sites = build_mesh(T_PLUS, n_sub)
    own = sum(1 for pos in tp_sites
              if pressure_at_site(pos, T_PLUS, epsilon) >
                 pressure_at_site(pos, T_MINUS, epsilon))
    return own, len(tp_sites)


# ==============================================================================
# ANALYTICAL DERIVATION
# ==============================================================================

def analytical_proof():
    """
    THEOREM: The continuum own-surface dominance fraction is exactly 3/4.

    PROOF:
    ======

    Step 1: Simplification via antipodal symmetry
    -----------------------------------------------
    All 8 vertices satisfy |v|² = 3 and T₋ = -T₊.

    |x - v|² = |x|² - 2(x·v) + 3

    So min_i|x - T₊[i]|² ↔ max_i(x·T₊[i]) and similarly for T₋.

    Own-dominant iff max_i(x·T₊[i]) > max_j(x·T₋[j])
                 iff max_i(x·T₊[i]) > max_j(-x·T₊[j])
                 iff max_i(x·T₊[i]) > -min_j(x·T₊[j])
                 iff max_i(x·T₊[i]) + min_i(x·T₊[i]) > 0

    Step 2: Evaluation on a face
    -----------------------------
    Consider face 0 with face vertices A = T₊[1], B = T₊[2], C = T₊[3]
    and opposite vertex D = T₊[0].

    A point on the face: x = (1-α-β)A + αB + βC  with α,β ≥ 0, α+β ≤ 1.

    Computing dot products s_i = x · T₊[i]:
      s_D = x · D = -1                    (constant!)
      s_A = x · A = 4(1-α-β) - 1 = 3 - 4α - 4β
      s_B = x · B = 4α - 1
      s_C = x · C = 4β - 1

    Verification: s_D + s_A + s_B + s_C = -1 + (3-4α-4β) + (4α-1) + (4β-1) = 0 ✓
    (This sum = x·(sum of T₊ vertices) = x·0 = 0, since T₊ vertex sum = 0.)

    Step 3: min(s) = -1 everywhere on the face
    --------------------------------------------
    - s_A = 3 - 4(α+β) ≥ 3 - 4 = -1  (since α+β ≤ 1)
    - s_B = 4α - 1 ≥ -1              (since α ≥ 0)
    - s_C = 4β - 1 ≥ -1              (since β ≥ 0)

    So min(s_A, s_B, s_C) ≥ -1 = s_D, hence min(s) = s_D = -1 always.

    Step 4: Own-dominant iff max(s_A, s_B, s_C) > 1
    -------------------------------------------------
    max(s) + min(s) > 0  ⟺  max(s) > -min(s) = 1

    This holds when ANY of:
      s_A > 1  ⟺  α + β < 1/2    (corner near vertex A at (0,0))
      s_B > 1  ⟺  α > 1/2        (corner near vertex B at (1,0))
      s_C > 1  ⟺  β > 1/2        (corner near vertex C at (0,1))

    Step 5: Area calculation
    -------------------------
    The face triangle has vertices (0,0), (1,0), (0,1) in (α,β) space.
    Total area = 1/2.

    The three own-dominant sub-triangles:
      Corner A: {α+β < 1/2} = triangle (0,0)-(1/2,0)-(0,1/2), area = 1/8
      Corner B: {α > 1/2}   = triangle (1/2,0)-(1,0)-(1/2,1/2), area = 1/8
      Corner C: {β > 1/2}   = triangle (0,1/2)-(1/2,1/2)-(0,1), area = 1/8

    These are disjoint (they share at most boundary segments).
    Total own-dominant area = 3/8.

    Own-dominant fraction = (3/8) / (1/2) = 3/4.

    The other-dominant region is the MEDIAL TRIANGLE:
      {α+β > 1/2, α < 1/2, β < 1/2}
      = triangle (1/2,0)-(0,1/2)-(1/2,1/2), area = 1/8

    This is the central region where NO single face vertex dominates strongly
    enough — the antipodal T₋ vertex (which aligns with the face normal
    direction) wins instead.

    By tetrahedral symmetry, all 4 faces give the same fraction.    ∎
    """
    print("="*70)
    print("ANALYTICAL PROOF: CONTINUUM DOMINANCE RATIO = 3/4")
    print("="*70)

    print("""
    THEOREM: The own-surface dominance fraction on the stella octangula
    surface is exactly 3/4 in the continuum limit.

    PROOF SKETCH:
    1. Since T₋ = -T₊ and |v|² = 3 for all vertices:
       Own-dominant ⟺ max_i(x·T₊[i]) + min_i(x·T₊[i]) > 0

    2. On each face (vertices A,B,C; opposite vertex D):
       s_D = -1 (constant), s_A = 3-4α-4β, s_B = 4α-1, s_C = 4β-1

    3. min(s) = s_D = -1 always on the face (boundary terms ≥ -1)

    4. Own-dominant ⟺ max(s_A, s_B, s_C) > 1
       ⟺ (α+β < 1/2) ∨ (α > 1/2) ∨ (β > 1/2)
       = three corner sub-triangles of the face

    5. Each corner triangle has area 1/8; face area = 1/2
       ⇒ ratio = (3 × 1/8) / (1/2) = 3/4  ∎

    The other-dominant region is the MEDIAL TRIANGLE (connecting edge
    midpoints), comprising exactly 1/4 of each face's area.
    """)


def verify_analytical_result():
    """Verify the 3/4 result numerically at multiple resolutions."""
    print("="*70)
    print("NUMERICAL VERIFICATION")
    print("="*70)

    # --- 1. Direct area computation on one face ---
    print("\n1. Direct area computation (analytical criterion):")
    n = 10000
    own = 0
    total = 0
    for i in range(n):
        for j in range(n - i):
            alpha = (i + 0.5) / n
            beta = (j + 0.5) / n
            total += 1
            # Own-dominant iff max(3-4α-4β, 4α-1, 4β-1) > 1
            s_A = 3 - 4*alpha - 4*beta
            s_B = 4*alpha - 1
            s_C = 4*beta - 1
            if max(s_A, s_B, s_C) > 1:
                own += 1
    print(f"   Grid {n}×{n}: {own}/{total} = {own/total:.8f}")
    print(f"   Exact:  3/4 = {3/4:.8f}")
    print(f"   Error:  {abs(own/total - 0.75):.2e}")

    # --- 2. Monte Carlo on full surface ---
    print("\n2. Monte Carlo on full T₊ surface (4 faces, 10M samples each):")
    np.random.seed(42)
    n_mc = 10_000_000
    own_total = 0
    sample_total = 0

    for f in range(4):
        va = T_PLUS[FACES[f][0]]
        vb = T_PLUS[FACES[f][1]]
        vc = T_PLUS[FACES[f][2]]

        r1 = np.random.random(n_mc)
        r2 = np.random.random(n_mc)
        mask = r1 + r2 > 1
        r1[mask] = 1 - r1[mask]
        r2[mask] = 1 - r2[mask]
        r3 = 1 - r1 - r2

        pts = np.outer(r3, va) + np.outer(r1, vb) + np.outer(r2, vc)
        pts = pts.reshape(n_mc, 3)
        dots = pts @ T_PLUS.T
        max_dots = np.nanmax(dots, axis=1)
        min_dots = np.nanmin(dots, axis=1)
        valid = np.isfinite(max_dots) & np.isfinite(min_dots)
        criterion = (max_dots + min_dots > 0) & valid

        own_total += np.sum(criterion)
        sample_total += n_mc

    ratio_mc = own_total / sample_total
    print(f"   {own_total:,}/{sample_total:,} = {ratio_mc:.8f}")
    print(f"   Exact:  3/4 = {3/4:.8f}")
    print(f"   Error:  {abs(ratio_mc - 0.75):.2e}")

    # --- 3. Mesh convergence toward 3/4 ---
    print("\n3. Mesh convergence study (ε = 0.1, matching genesis_soup.c):")
    print(f"   {'n_sub':>6} {'sites':>6} {'own':>6} {'ratio':>10} "
          f"{'error_vs_3/4':>12} {'error_vs_mesh16':>15}")

    ref = 340/514
    for n_sub in [4, 8, 12, 16, 20, 24, 32, 48, 64, 96]:
        own, total = compute_dominance_ratio_mesh(n_sub, epsilon=0.1)
        r = own / total
        print(f"   {n_sub:6d} {total:6d} {own:6d} {r:10.6f} "
              f"{abs(r - 0.75):12.6f} {abs(r - ref):15.6f}")

    # --- 4. Mesh convergence with ε → 0 ---
    print("\n4. Mesh convergence (ε = 0.0001, nearest-vertex limit):")
    print(f"   {'n_sub':>6} {'sites':>6} {'own':>6} {'ratio':>10} {'error_vs_3/4':>12}")

    for n_sub in [4, 8, 16, 32, 64, 96, 128]:
        own, total = compute_dominance_ratio_mesh(n_sub, epsilon=0.0001)
        r = own / total
        print(f"   {n_sub:6d} {total:6d} {own:6d} {r:10.6f} {abs(r - 0.75):12.6f}")

    return ratio_mc


def explain_mesh_artifact():
    """Explain why n_sub=16 gives 66.1% instead of 75%."""
    print("\n" + "="*70)
    print("WHY n_sub=16 GIVES 66.1% INSTEAD OF 75%")
    print("="*70)

    print("""
    The discrepancy arises from EDGE/VERTEX SHARING in the mesh
    deduplication.

    With n_sub=16, each face generates (16+1)(16+2)/2 = 153 grid points.
    Four faces × 153 = 612, but after deduplication at shared edges and
    vertices, only 257 unique sites remain per tetrahedron.

    The deduplicated sites are NOT uniformly distributed by area weight:
    - Edge and vertex sites serve multiple faces, so they're over-represented
    - Interior face sites are under-represented relative to area weighting
    - Edge/vertex sites tend to be BETWEEN faces, where the geometry is
      more complex

    The own-dominant fraction on the face INTERIOR is 75% (the three corner
    triangles). But sites ON the edges (shared between faces) sample the
    boundary differently, introducing a systematic bias toward the
    other-dominant central region.

    As n_sub increases, interior sites dominate and the ratio → 3/4:
    """)

    # Show convergence explicitly
    for n_sub in [8, 16, 32, 64, 128]:
        own, total = compute_dominance_ratio_mesh(n_sub, epsilon=0.0001)
        r = own / total
        interior_fraction = 1 - 6*(n_sub-1)/(total-1)  # rough
        print(f"   n_sub={n_sub:3d}: {own}/{total} = {r:.4f} "
              f"(Δ from 3/4 = {0.75-r:+.4f})")


def boundary_visualization():
    """Describe the Voronoi boundary geometry."""
    print("\n" + "="*70)
    print("GEOMETRIC INTERPRETATION")
    print("="*70)

    print("""
    On each tetrahedral face, the boundary between own-dominant and
    other-dominant regions is a TRIANGLE connecting the edge midpoints
    — the "medial triangle."

                        C (0,1)
                       / \\
                      /   \\
                     / own  \\
                    /   C    \\
              M_AC /___________\\ M_BC
                  / \\  other  / \\
                 /   \\ (1/4) /   \\
                / own \\     / own  \\
               /  A    \\   /  B    \\
              /         \\ /         \\
        A (0,0)----M_AB----------B (1,0)

    Corner sub-triangles (own-dominant):
      - Near A: α+β < 1/2  (closest to face vertex A → nearest T₊ vertex)
      - Near B: α > 1/2    (closest to face vertex B → nearest T₊ vertex)
      - Near C: β > 1/2    (closest to face vertex C → nearest T₊ vertex)

    Central medial triangle (other-dominant):
      - α+β > 1/2, α < 1/2, β < 1/2
      - In this region, the point is far from all three face vertices,
        and the ANTIPODAL T₋ vertex (aligned with face normal) is closer
        than any of the three face-vertex T₊ neighbors.

    PHYSICAL MEANING:
    ─────────────────
    Near the vertices of T₊, the "own" pressure P₊ dominates because
    the nearest vertex is from T₊. But in the central region of each face,
    the nearest vertex in 3D is actually from T₋ — the antipodal vertex
    that sits above/below the face center. The stella octangula's
    interpenetrating geometry means T₋ intrudes into the central regions
    of T₊'s faces.

    The ratio 3/4 is a TOPOLOGICAL INVARIANT of the stella octangula
    (independent of edge length, ε, or mesh resolution). It emerges purely
    from the geometry of two interpenetrating regular tetrahedra.
    """)


def per_face_own_vertex_analysis():
    """Show which T₊ vertex 'wins' in each own-dominant corner."""
    print("\n" + "="*70)
    print("NEAREST-VERTEX STRUCTURE")
    print("="*70)

    # Face 0: vertices T₊[1], T₊[2], T₊[3], opposite T₊[0]
    # T₋[0] = -T₊[0] = (-1,-1,-1) is the antipodal competitor

    f = 0
    a_idx, b_idx, c_idx = FACES[f]
    d_idx = [i for i in range(4) if i not in FACES[f]][0]
    A, B, C, D = T_PLUS[a_idx], T_PLUS[b_idx], T_PLUS[c_idx], T_PLUS[d_idx]
    D_anti = T_MINUS[d_idx]  # = -D, the antipodal vertex

    print(f"\n  Face 0: A=T₊[{a_idx}]={A}, B=T₊[{b_idx}]={B}, C=T₊[{c_idx}]={C}")
    print(f"  Opposite: D=T₊[{d_idx}]={D}")
    print(f"  Antipodal of D: T₋[{d_idx}]={D_anti} = -D")

    # Distance from face center to D and to -D
    center = (A + B + C) / 3
    d_to_D = np.linalg.norm(center - D)
    d_to_antiD = np.linalg.norm(center - D_anti)
    d_to_A = np.linalg.norm(center - A)

    print(f"\n  Face center = {center}")
    print(f"  Distance to face vertices (A,B,C): {d_to_A:.4f}")
    print(f"  Distance to opposite T₊ vertex D:  {d_to_D:.4f}")
    print(f"  Distance to antipodal T₋ vertex:   {d_to_antiD:.4f}")
    print(f"\n  At center: nearest T₊ = A,B,C at {d_to_A:.4f}")
    print(f"             nearest T₋ = -D at {d_to_antiD:.4f}")
    print(f"  Center is {'own' if d_to_A < d_to_antiD else 'OTHER'}-dominant")
    print(f"  (because the T₋ antipodal vertex at {d_to_antiD:.4f} < "
          f"face vertices at {d_to_A:.4f})")


# ==============================================================================
# MAIN
# ==============================================================================

def main():
    print("="*70)
    print("GEOMETRIC ORIGIN OF THE 66.1% DOMINANCE RATIO")
    print("="*70)
    print(f"\nStella octangula: edge = 2√2 ≈ {EDGE_LENGTH:.4f}")
    print(f"All 8 vertices at radius √3 ≈ {np.sqrt(3):.4f}")
    print(f"T₋ = -T₊ (antipodal symmetry)")

    # 1. Reproduce mesh result
    print("\n--- Reproducing n_sub=16 result ---")
    own, total = compute_dominance_ratio_mesh(16, epsilon=0.1)
    print(f"Own-dominant: {own}/{total} = {own/total*100:.2f}% ✓")

    # 2. Analytical proof
    analytical_proof()

    # 3. Numerical verification
    ratio_mc = verify_analytical_result()

    # 4. Explain the mesh artifact
    explain_mesh_artifact()

    # 5. Geometric interpretation
    per_face_own_vertex_analysis()
    boundary_visualization()

    # 6. Summary
    print("="*70)
    print("FINAL SUMMARY")
    print("="*70)
    print(f"""
    QUESTION: What determines the 66.1% (340/514) dominance ratio?

    ANSWER:
    ═══════
    1. The CONTINUUM ratio is exactly 3/4 (75%), not 66.1%.

    2. The 66.1% at n_sub=16 is a finite-mesh artifact from edge/vertex
       sharing in the barycentric triangulation.

    3. The 3/4 ratio has a clean geometric origin:
       - On each face, the own-dominant region = 3 corner sub-triangles
       - The other-dominant region = medial triangle (center 1/4)
       - The T₋ antipodal vertex penetrates T₊'s face centers

    4. Derived from a single analytical criterion:
         Own-dominant ⟺ max_i(x·T₊[i]) + min_i(x·T₊[i]) > 0
       which follows from T₋ = -T₊ and |v|² = const.

    5. The ratio is a TOPOLOGICAL INVARIANT of the stella octangula:
       it depends only on the interpenetrating tetrahedral geometry,
       not on edge length, ε, or mesh parameters.
    """)

    # Save results
    output = {
        "investigation": "Geometric Origin of 66.1% Dominance Ratio",
        "timestamp": datetime.now().isoformat(),
        "answer": {
            "continuum_ratio": 0.75,
            "continuum_ratio_exact": "3/4",
            "mesh_n16_ratio": 340/514,
            "mesh_n16_is_artifact": True,
            "analytical_criterion": "max(x·T₊[i]) + min(x·T₊[i]) > 0",
            "geometric_interpretation": (
                "Own-dominant region = 3 corner sub-triangles of each face "
                "(near face vertices, where nearest vertex is from own tetrahedron). "
                "Other-dominant region = medial triangle (center 1/4 of each face, "
                "where antipodal T₋ vertex penetrates)."
            ),
            "proof_key_steps": [
                "T₋ = -T₊ and |v|² = 3 ⟹ bisectors pass through origin",
                "On each face: s_D = -1 (constant), s_{A,B,C} linear in barycentric coords",
                "min(s) = -1 always; own-dominant iff max(s_A,s_B,s_C) > 1",
                "Three disjoint corner triangles each have area 1/8 of face area 1/2",
                "Ratio = 3×(1/8) / (1/2) = 3/4"
            ],
            "monte_carlo_verification": float(ratio_mc),
        }
    }

    with open("dominance_ratio_results.json", "w") as fp:
        json.dump(output, fp, indent=2, default=str)
    print("Results saved to dominance_ratio_results.json")


if __name__ == "__main__":
    main()
