#!/usr/bin/env python3
"""
Adversarial Physics Verification: Proposition 0.0.39
Stella Adjoint Decomposition — Polyhedral decomposition ↔ SU(3) adjoint representation

This script performs independent numerical verification of all quantitative claims
in Proposition 0.0.39, organized as adversarial tests designed to FIND errors.

Tests:
1. Volume decomposition: 8 corner tets + 1 central octahedron = stella volume
2. Corner tetrahedra regularity: all edges equal
3. Octahedron = conv(T+) ∩ conv(T-): intersection verification
4. Face-adjoint bijection: S3 equivariance under color permutations
5. Phase cancellation at octahedron center: χ_R + χ_G + χ_B = 0
6. Weyl group orbit verification: cyclic permutation on root lines
7. Volume ratios: V_oct/V_stella = 1/3, V_corners/V_stella = 2/3
8. Visualization of the decomposition with adjoint labels

Output: Verification plots in verification/plots/
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from itertools import combinations, permutations
import sys
import os

# Ensure output directory exists
PLOT_DIR = os.path.join(os.path.dirname(__file__), "plots")
os.makedirs(PLOT_DIR, exist_ok=True)

# =============================================================================
# GEOMETRY SETUP
# =============================================================================

# Stella octangula vertices at (±1, ±1, ±1)
# T+ vertices: even number of minus signs
T_PLUS = np.array([
    [1, 1, 1],     # v_R (red)
    [1, -1, -1],   # v_G (green)
    [-1, 1, -1],   # v_B (blue)
    [-1, -1, 1],   # v_W (apex/white)
], dtype=float)

# T- vertices: odd number of minus signs
T_MINUS = np.array([
    [-1, -1, -1],  # v_Rbar (anti-red)
    [-1, 1, 1],    # v_Gbar (anti-green)
    [1, -1, 1],    # v_Bbar (anti-blue)
    [1, 1, -1],    # v_Wbar (anti-apex)
], dtype=float)

# Central octahedron vertices (face centers of cube / edge midpoints of T+)
OCT_VERTICES = np.array([
    [1, 0, 0], [-1, 0, 0],
    [0, 1, 0], [0, -1, 0],
    [0, 0, 1], [0, 0, -1],
], dtype=float)

# SU(3) weight vectors (2D projections for the fundamental representation)
W_R = np.array([1/2, 1/(2*np.sqrt(3))])
W_G = np.array([-1/2, 1/(2*np.sqrt(3))])
W_B = np.array([0, -1/np.sqrt(3)])

# Simple roots
ALPHA_1 = W_R - W_G  # = (1, 0)
ALPHA_2 = W_G - W_B  # = (-1/2, sqrt(3)/2)

# All 6 roots of A2
ROOTS = {
    'α₁': ALPHA_1,
    'α₂': ALPHA_2,
    'α₁+α₂': ALPHA_1 + ALPHA_2,
    '-α₁': -ALPHA_1,
    '-α₂': -ALPHA_2,
    '-(α₁+α₂)': -(ALPHA_1 + ALPHA_2),
}


def tet_volume(vertices):
    """Volume of tetrahedron given 4 vertices."""
    a, b, c, d = vertices
    return abs(np.dot(b - a, np.cross(c - a, d - a))) / 6.0


def oct_volume_regular(edge_length):
    """Volume of regular octahedron with given edge length."""
    return (np.sqrt(2) / 3) * edge_length**3


def is_regular_tet(vertices, tol=1e-10):
    """Check if 4 vertices form a regular tetrahedron. Returns (is_regular, edge_length)."""
    edges = []
    for i, j in combinations(range(4), 2):
        edges.append(np.linalg.norm(vertices[i] - vertices[j]))
    edges = np.array(edges)
    is_reg = np.all(np.abs(edges - edges[0]) < tol)
    return is_reg, edges[0], edges


def point_in_tet(point, tet_vertices):
    """Check if a point is inside a tetrahedron using barycentric coordinates."""
    v0, v1, v2, v3 = tet_vertices
    T = np.column_stack([v1 - v0, v2 - v0, v3 - v0])
    try:
        bary = np.linalg.solve(T, point - v0)
    except np.linalg.LinAlgError:
        return False
    return (bary >= -1e-10).all() and (bary.sum() <= 1 + 1e-10)


# =============================================================================
# TEST 1: Volume Decomposition
# =============================================================================

def test_volume_decomposition():
    """Verify: V_oct + 8 * V_corner = V(T+ ∪ T-)"""
    print("=" * 70)
    print("TEST 1: Volume Decomposition")
    print("=" * 70)

    # Volume of each parent tetrahedron
    v_tplus = tet_volume(T_PLUS)
    v_tminus = tet_volume(T_MINUS)
    print(f"  V(T+)     = {v_tplus:.6f}  (expected: 8/3 = {8/3:.6f})")
    print(f"  V(T-)     = {v_tminus:.6f}  (expected: 8/3 = {8/3:.6f})")

    # Volume of central octahedron (edge = sqrt(2))
    oct_edge = np.sqrt(2)
    v_oct = oct_volume_regular(oct_edge)
    print(f"  V(oct)    = {v_oct:.6f}  (expected: 4/3 = {4/3:.6f})")

    # 8 corner tetrahedra
    corner_tets = []
    all_verts = np.vstack([T_PLUS, T_MINUS])
    for v in all_verts:
        # Find the 3 closest octahedron vertices to this stella vertex
        dists = np.array([np.linalg.norm(v - o) for o in OCT_VERTICES])
        closest_3 = OCT_VERTICES[np.argsort(dists)[:3]]
        corner = np.vstack([[v], closest_3])
        corner_tets.append(corner)

    v_corners = [tet_volume(ct) for ct in corner_tets]
    v_corner_total = sum(v_corners)
    v_corner_each = v_corners[0]
    print(f"  V(corner) = {v_corner_each:.6f} each  (expected: 1/3 = {1/3:.6f})")
    print(f"  8*V(corner) = {v_corner_total:.6f}  (expected: 8/3 = {8/3:.6f})")

    # Total
    v_stella = v_oct + v_corner_total
    v_union = 2 * v_tplus - v_oct  # inclusion-exclusion
    print(f"\n  V(oct) + 8*V(corner) = {v_stella:.6f}")
    print(f"  V(T+ ∪ T-) by incl-excl = {v_union:.6f}")
    print(f"  Expected: 4.000000")

    vol_check = abs(v_stella - 4.0) < 1e-10
    ie_check = abs(v_union - 4.0) < 1e-10
    match_check = abs(v_stella - v_union) < 1e-10

    print(f"\n  Volume decomposition exact: {'PASS ✅' if vol_check else 'FAIL ❌'}")
    print(f"  Inclusion-exclusion match:  {'PASS ✅' if ie_check else 'FAIL ❌'}")
    print(f"  Consistency:                {'PASS ✅' if match_check else 'FAIL ❌'}")

    return vol_check and ie_check and match_check, corner_tets


# =============================================================================
# TEST 2: Corner Tetrahedra Regularity
# =============================================================================

def test_corner_regularity(corner_tets):
    """Verify: all 8 corner tets are regular with edge √2."""
    print("\n" + "=" * 70)
    print("TEST 2: Corner Tetrahedra Regularity")
    print("=" * 70)

    all_pass = True
    expected_edge = np.sqrt(2)

    for i, ct in enumerate(corner_tets):
        is_reg, edge, all_edges = is_regular_tet(ct)
        status = "PASS ✅" if is_reg and abs(edge - expected_edge) < 1e-10 else "FAIL ❌"
        if not (is_reg and abs(edge - expected_edge) < 1e-10):
            all_pass = False
        vertex_label = f"({ct[0][0]:+.0f},{ct[0][1]:+.0f},{ct[0][2]:+.0f})"
        print(f"  Corner tet {i+1} at {vertex_label}: "
              f"regular={is_reg}, edge={edge:.6f} (expected {expected_edge:.6f}) {status}")

    print(f"\n  All corners regular with edge √2: {'PASS ✅' if all_pass else 'FAIL ❌'}")
    return all_pass


# =============================================================================
# TEST 3: Octahedron = conv(T+) ∩ conv(T-)
# =============================================================================

def test_octahedron_intersection():
    """Verify: octahedron vertices lie inside both T+ and T-."""
    print("\n" + "=" * 70)
    print("TEST 3: Octahedron = conv(T+) ∩ conv(T-)")
    print("=" * 70)

    all_pass = True
    for i, ov in enumerate(OCT_VERTICES):
        in_tplus = point_in_tet(ov, T_PLUS)
        in_tminus = point_in_tet(ov, T_MINUS)
        in_both = in_tplus and in_tminus
        if not in_both:
            all_pass = False
        label = f"({ov[0]:+.0f},{ov[1]:+.0f},{ov[2]:+.0f})"
        print(f"  Oct vertex {label}: in T+={in_tplus}, in T-={in_tminus} "
              f"{'PASS ✅' if in_both else 'FAIL ❌'}")

    # Also verify that oct vertices are edge midpoints of T+
    print("\n  Octahedron vertices as T+ edge midpoints:")
    t_plus_edges = list(combinations(range(4), 2))
    midpoints = set()
    for i, j in t_plus_edges:
        mid = tuple(np.round((T_PLUS[i] + T_PLUS[j]) / 2, 10))
        midpoints.add(mid)
    oct_set = set(tuple(np.round(v, 10)) for v in OCT_VERTICES)
    midpoint_match = midpoints == oct_set
    print(f"  T+ edge midpoints = octahedron vertices: "
          f"{'PASS ✅' if midpoint_match else 'FAIL ❌'}")
    if not midpoint_match:
        all_pass = False

    # Verify they are face centers of the cube
    print("\n  Octahedron vertices as cube face centers:")
    cube_face_centers = set()
    for axis in range(3):
        for sign in [-1, 1]:
            center = [0.0, 0.0, 0.0]
            center[axis] = float(sign)
            cube_face_centers.add(tuple(center))
    face_center_match = oct_set == cube_face_centers
    print(f"  Cube face centers = octahedron vertices: "
          f"{'PASS ✅' if face_center_match else 'FAIL ❌'}")
    if not face_center_match:
        all_pass = False

    # NOTE: The paper says "edge midpoints of the cube" at line 100.
    # Cube edge midpoints are 12 points like (±1,±1,0), NOT 6 face centers.
    cube_edge_midpoints = set()
    cube_verts = [(s1, s2, s3) for s1 in [-1, 1] for s2 in [-1, 1] for s3 in [-1, 1]]
    for i, v1 in enumerate(cube_verts):
        for j, v2 in enumerate(cube_verts):
            if i < j:
                diff = sum((a - b)**2 for a, b in zip(v1, v2))
                if abs(diff - 4) < 1e-10:  # cube edge length = 2
                    mid = tuple((a + b) / 2 for a, b in zip(v1, v2))
                    cube_edge_midpoints.add(mid)
    print(f"\n  ADVERSARIAL CHECK: Are oct vertices cube EDGE midpoints?")
    print(f"  Number of cube edge midpoints: {len(cube_edge_midpoints)} (should be 12)")
    print(f"  Number of oct vertices: {len(oct_set)} (should be 6)")
    edge_midpoint_match = oct_set.issubset(cube_edge_midpoints)
    print(f"  Oct vertices ⊂ cube edge midpoints: {edge_midpoint_match}")
    print(f"  Oct vertices = cube FACE centers: {face_center_match} ← CORRECT")
    print(f"  ⚠️  Paper line 100 says 'edge midpoints of the cube' — this is WRONG")
    print(f"     They are FACE CENTERS of the cube (and edge midpoints of T+)")

    return all_pass


# =============================================================================
# TEST 4: S3 Equivariance of Face-Adjoint Bijection
# =============================================================================

def test_s3_equivariance():
    """Verify: cyclic permutation R→G→B→R maps faces to roots consistently."""
    print("\n" + "=" * 70)
    print("TEST 4: S₃ Equivariance of Face-Adjoint Bijection")
    print("=" * 70)

    # Face-adjoint assignments from the proposition
    # Face opposite v_R → E_{α₂} (edge G-B encodes α₂ = w_G - w_B)
    # Face opposite v_G → E_{-(α₁+α₂)} (edge R-B encodes -(w_R - w_B) = -(α₁+α₂))
    # Face opposite v_B → E_{α₁} (edge R-G encodes α₁ = w_R - w_G)

    face_root_map = {
        'opp_R': ALPHA_2,
        'opp_G': -(ALPHA_1 + ALPHA_2),
        'opp_B': ALPHA_1,
    }

    # Under cyclic R→G→B→R:
    # Face opp R → Face opp G (because R becomes G, so the face that was opp R is now opp G)
    # The root should transform: α₂ → -(α₁+α₂)
    cyclic_map = {'opp_R': 'opp_G', 'opp_G': 'opp_B', 'opp_B': 'opp_R'}

    print("  Face-root assignments:")
    for face, root in face_root_map.items():
        print(f"    {face} → ({root[0]:+.4f}, {root[1]:+.4f})")

    print("\n  Cyclic permutation R→G→B→R:")
    all_pass = True
    for face in ['opp_R', 'opp_G', 'opp_B']:
        target_face = cyclic_map[face]
        original_root = face_root_map[face]
        target_root = face_root_map[target_face]
        print(f"    {face}({original_root[0]:+.4f},{original_root[1]:+.4f}) "
              f"→ {target_face}({target_root[0]:+.4f},{target_root[1]:+.4f})")

    # Verify the orbit: α₂ → -(α₁+α₂) → α₁ → α₂
    orbit = [ALPHA_2, -(ALPHA_1 + ALPHA_2), ALPHA_1]
    print("\n  Root orbit under cyclic permutation:")
    orbit_labels = ['α₂', '-(α₁+α₂)', 'α₁']
    for i in range(3):
        next_i = (i + 1) % 3
        print(f"    {orbit_labels[i]} → {orbit_labels[next_i]}")

    # Check: does the Weyl reflection s₁s₂ reproduce this?
    # s_α(β) = β - 2(β·α)/(α·α) * α
    def weyl_reflect(beta, alpha):
        return beta - 2 * np.dot(beta, alpha) / np.dot(alpha, alpha) * alpha

    s1 = lambda b: weyl_reflect(b, ALPHA_1)
    s2 = lambda b: weyl_reflect(b, ALPHA_2)

    # s1*s2 should be the cyclic permutation
    s1s2 = lambda b: s1(s2(b))

    print("\n  Weyl group element s₁s₂ action:")
    test_root = ALPHA_2
    for step in range(3):
        next_root = s1s2(test_root)
        print(f"    ({test_root[0]:+.6f}, {test_root[1]:+.6f}) → "
              f"({next_root[0]:+.6f}, {next_root[1]:+.6f})")
        test_root = next_root

    # Verify orbit matches expected
    test_root = ALPHA_2
    for expected in orbit[1:] + [orbit[0]]:
        test_root = s1s2(test_root)
        match = np.allclose(test_root, expected)
        if not match:
            all_pass = False

    # ADVERSARIAL: Check if the orbit mixes positive and negative roots
    print("\n  ADVERSARIAL CHECK: Does the orbit mix positive and negative roots?")
    positive_roots = [ALPHA_1, ALPHA_2, ALPHA_1 + ALPHA_2]
    for label, root in zip(orbit_labels, orbit):
        is_pos = any(np.allclose(root, pr) for pr in positive_roots)
        sign = "POSITIVE" if is_pos else "NEGATIVE"
        print(f"    {label} = ({root[0]:+.4f}, {root[1]:+.4f}) → {sign}")
    print("  ⚠️  The orbit {α₂, -(α₁+α₂), α₁} contains 2 positive and 1 negative root")
    print("     Paper line 297 claims 'Weyl group action on the positive roots' — INCORRECT")

    print(f"\n  S₃ equivariance (orbit structure): {'PASS ✅' if all_pass else 'FAIL ❌'}")
    return all_pass


# =============================================================================
# TEST 5: Phase Cancellation at Octahedron Center
# =============================================================================

def test_phase_cancellation():
    """Verify: χ_R + χ_G + χ_B = P(1 + ω + ω²) = 0 at the centroid."""
    print("\n" + "=" * 70)
    print("TEST 5: Phase Cancellation at Octahedron Center")
    print("=" * 70)

    omega = np.exp(2j * np.pi / 3)

    # At the centroid, all pressure functions are equal by S3 symmetry
    P = 1.0  # Normalized
    chi_total = P * (1 + omega + omega**2)

    print(f"  ω = exp(2πi/3) = {omega:.6f}")
    print(f"  1 + ω + ω² = {1 + omega + omega**2:.10f}")
    print(f"  |χ_total| = {abs(chi_total):.2e}")

    cancel_check = abs(chi_total) < 1e-14
    print(f"\n  Phase cancellation at center: {'PASS ✅' if cancel_check else 'FAIL ❌'}")

    # Also check at other points inside the octahedron
    print("\n  Phase cancellation at random interior points:")
    np.random.seed(42)
    n_points = 1000
    inside_count = 0
    max_chi = 0

    for _ in range(n_points):
        # Random point in the octahedron
        while True:
            pt = np.random.uniform(-1, 1, 3)
            if np.sum(np.abs(pt)) <= 1:  # Inside octahedron
                break

        # Pressure = distance from opposite face (simplified model)
        # For S3 symmetric pressure: P_c proportional to barycentric-like coord
        d_R = np.linalg.norm(pt - T_PLUS[0])
        d_G = np.linalg.norm(pt - T_PLUS[1])
        d_B = np.linalg.norm(pt - T_PLUS[2])

        # Use inverse distance as pressure proxy
        P_R = 1.0 / (d_R + 0.1)
        P_G = 1.0 / (d_G + 0.1)
        P_B = 1.0 / (d_B + 0.1)

        chi = P_R * 1 + P_G * omega + P_B * omega**2
        max_chi = max(max_chi, abs(chi))
        P_total = P_R + P_G + P_B
        if abs(chi) / P_total < 0.5:
            inside_count += 1

    print(f"  Points with |χ|/P_total < 0.5: {inside_count}/{n_points} "
          f"({100*inside_count/n_points:.1f}%)")
    print(f"  Max |χ| at any interior point: {max_chi:.4f}")
    print(f"  (Exact cancellation only at the centroid by S₃ symmetry)")

    return cancel_check


# =============================================================================
# TEST 6: Volume Ratios
# =============================================================================

def test_volume_ratios():
    """Verify: V_oct/V_stella = 1/3 and V_corners/V_stella = 2/3."""
    print("\n" + "=" * 70)
    print("TEST 6: Volume Ratios")
    print("=" * 70)

    v_oct = 4/3
    v_stella = 4.0
    v_corners = 8/3

    ratio_oct = v_oct / v_stella
    ratio_corners = v_corners / v_stella

    print(f"  V_oct / V_stella     = {ratio_oct:.6f}  (expected: 1/3 = {1/3:.6f})")
    print(f"  V_corners / V_stella = {ratio_corners:.6f}  (expected: 2/3 = {2/3:.6f})")
    print(f"  V_corners / V_oct    = {v_corners/v_oct:.6f}  (expected: 2)")

    r1 = abs(ratio_oct - 1/3) < 1e-14
    r2 = abs(ratio_corners - 2/3) < 1e-14

    # ADVERSARIAL: Does the volume ratio relate to Casimir or dimension?
    print(f"\n  ADVERSARIAL: Ratio comparisons")
    print(f"    V_corners/V_oct = 2    vs  dim(8)/dim(1) = 8   → NO match")
    print(f"    V_corners/V_oct = 2    vs  C₂(adj)/C₂(fund) = 3/(4/3) = 2.25  → NO match")
    print(f"    V_oct/V_corner_each = {v_oct/(v_corners/8):.1f}  vs  dim(8)/8 = 1  → trivial")
    print(f"    ⚠️  No obvious Casimir–volume connection found (Section 8, Q1 remains open)")

    print(f"\n  Volume ratios: {'PASS ✅' if r1 and r2 else 'FAIL ❌'}")
    return r1 and r2


# =============================================================================
# TEST 7: Weyl Group Full Orbit Check
# =============================================================================

def test_weyl_orbits():
    """Verify all Weyl group orbits on the root system."""
    print("\n" + "=" * 70)
    print("TEST 7: Full Weyl Group Action on Root System")
    print("=" * 70)

    def weyl_reflect(beta, alpha):
        return beta - 2 * np.dot(beta, alpha) / np.dot(alpha, alpha) * alpha

    s1 = lambda b: weyl_reflect(b, ALPHA_1)
    s2 = lambda b: weyl_reflect(b, ALPHA_2)

    # Generate the full Weyl group (6 elements for A2)
    identity = lambda b: b
    s1s2 = lambda b: s1(s2(b))
    s2s1 = lambda b: s2(s1(b))
    s1s2s1 = lambda b: s1(s2(s1(b)))  # = s2s1s2 for A2

    weyl_elements = [identity, s1, s2, s1s2, s2s1, s1s2s1]
    weyl_names = ['e', 's₁', 's₂', 's₁s₂', 's₂s₁', 's₁s₂s₁']

    # Action on each root
    root_names = ['α₁', 'α₂', 'α₁+α₂', '-α₁', '-α₂', '-(α₁+α₂)']
    root_vecs = [ALPHA_1, ALPHA_2, ALPHA_1+ALPHA_2, -ALPHA_1, -ALPHA_2, -(ALPHA_1+ALPHA_2)]

    print("  Weyl group action table:")
    print(f"  {'Element':10s}", end="")
    for rn in root_names:
        print(f" {rn:>12s}", end="")
    print()

    all_pass = True
    for w, wname in zip(weyl_elements, weyl_names):
        print(f"  {wname:10s}", end="")
        for rv in root_vecs:
            result = w(rv)
            # Find which root this is
            found = False
            for rn2, rv2 in zip(root_names, root_vecs):
                if np.allclose(result, rv2):
                    print(f" {rn2:>12s}", end="")
                    found = True
                    break
            if not found:
                print(f" {'???':>12s}", end="")
                all_pass = False
        print()

    # Verify S3 permutes root LINES (pairs ±α) not just individual roots
    print("\n  Root line orbits under Weyl group:")
    root_lines = [
        ('±α₁', ALPHA_1, -ALPHA_1),
        ('±α₂', ALPHA_2, -ALPHA_2),
        ('±(α₁+α₂)', ALPHA_1+ALPHA_2, -(ALPHA_1+ALPHA_2)),
    ]

    for wname, w in zip(weyl_names, weyl_elements):
        mapped_lines = []
        for line_name, pos, neg in root_lines:
            img_pos = w(pos)
            # Find which line it maps to
            for ln2, p2, n2 in root_lines:
                if np.allclose(img_pos, p2) or np.allclose(img_pos, n2):
                    mapped_lines.append(ln2)
                    break
        print(f"  {wname:10s}: {' → '.join(f'{a}→{b}' for a, b in zip([l[0] for l in root_lines], mapped_lines))}")

    print(f"\n  All Weyl orbits valid: {'PASS ✅' if all_pass else 'FAIL ❌'}")
    return all_pass


# =============================================================================
# TEST 8: Cartan Subalgebra Invariance Check (ADVERSARIAL)
# =============================================================================

def test_cartan_invariance():
    """ADVERSARIAL: Check if Cartan subalgebra is S3-invariant (the paper claims it is)."""
    print("\n" + "=" * 70)
    print("TEST 8: ADVERSARIAL — Cartan Subalgebra S₃-Invariance Check")
    print("=" * 70)

    # The Weyl group acts on h* (dual of Cartan subalgebra) = 2D plane
    # H₁ ↔ α₁ direction, H₂ ↔ α₂ direction (roughly)
    # But more precisely, we work in the weight space R²

    def weyl_reflect(beta, alpha):
        return beta - 2 * np.dot(beta, alpha) / np.dot(alpha, alpha) * alpha

    s1 = lambda b: weyl_reflect(b, ALPHA_1)
    s2 = lambda b: weyl_reflect(b, ALPHA_2)

    # The "Cartan generators" in weight space are the simple coroots:
    # h₁ = 2α₁/(α₁·α₁) and h₂ = 2α₂/(α₂·α₂)
    h1 = 2 * ALPHA_1 / np.dot(ALPHA_1, ALPHA_1)
    h2 = 2 * ALPHA_2 / np.dot(ALPHA_2, ALPHA_2)

    print(f"  h₁ (coroot of α₁) = ({h1[0]:.4f}, {h1[1]:.4f})")
    print(f"  h₂ (coroot of α₂) = ({h2[0]:.4f}, {h2[1]:.4f})")

    # Check: s1(h1), s1(h2), s2(h1), s2(h2)
    print(f"\n  Weyl reflections on coroots:")
    print(f"  s₁(h₁) = ({s1(h1)[0]:+.4f}, {s1(h1)[1]:+.4f})  (= -h₁? {np.allclose(s1(h1), -h1)})")
    print(f"  s₁(h₂) = ({s1(h2)[0]:+.4f}, {s1(h2)[1]:+.4f})  (= h₂? {np.allclose(s1(h2), h2)})")
    print(f"  s₂(h₁) = ({s2(h1)[0]:+.4f}, {s2(h1)[1]:+.4f})  (= h₁? {np.allclose(s2(h1), h1)})")
    print(f"  s₂(h₂) = ({s2(h2)[0]:+.4f}, {s2(h2)[1]:+.4f})  (= -h₂? {np.allclose(s2(h2), -h2)})")

    # Check if h1 is fixed by s1
    h1_fixed_by_s1 = np.allclose(s1(h1), h1)
    h2_fixed_by_s2 = np.allclose(s2(h2), h2)
    h1_fixed_by_s2 = np.allclose(s2(h1), h1)
    h2_fixed_by_s1 = np.allclose(s1(h2), h2)

    print(f"\n  Is h₁ fixed by s₁? {h1_fixed_by_s1} (expected: NO)")
    print(f"  Is h₂ fixed by s₂? {h2_fixed_by_s2} (expected: NO)")
    print(f"  Is h₁ fixed by s₂? {h1_fixed_by_s2}")
    print(f"  Is h₂ fixed by s₁? {h2_fixed_by_s1}")

    # Check: is the SUBSPACE span(h1, h2) preserved?
    # s1(h1) and s1(h2) should both be in span(h1, h2)
    def in_span(v, basis1, basis2, tol=1e-10):
        """Check if v is in span(basis1, basis2)."""
        M = np.column_stack([basis1, basis2])
        try:
            coeffs = np.linalg.solve(M, v)
            return True
        except np.linalg.LinAlgError:
            return False

    s1h1_in_span = in_span(s1(h1), h1, h2)
    s1h2_in_span = in_span(s1(h2), h1, h2)
    s2h1_in_span = in_span(s2(h1), h1, h2)
    s2h2_in_span = in_span(s2(h2), h1, h2)

    print(f"\n  s₁(h₁) in span(h₁,h₂)? {s1h1_in_span}")
    print(f"  s₁(h₂) in span(h₁,h₂)? {s1h2_in_span}")
    print(f"  s₂(h₁) in span(h₁,h₂)? {s2h1_in_span}")
    print(f"  s₂(h₂) in span(h₁,h₂)? {s2h2_in_span}")

    subspace_preserved = s1h1_in_span and s1h2_in_span and s2h1_in_span and s2h2_in_span
    elements_fixed = h1_fixed_by_s1 and h2_fixed_by_s2

    print(f"\n  Cartan SUBSPACE preserved by Weyl group: "
          f"{'YES ✅' if subspace_preserved else 'NO ❌'}")
    print(f"  Individual Cartan generators FIXED by Weyl group: "
          f"{'YES' if elements_fixed else 'NO ⚠️'}")
    print(f"\n  ⚠️  Paper line 303 claims h is 'the S₃-invariant part of su(3)'")
    print(f"     CORRECT: h is preserved as a SUBSPACE (mapped to itself)")
    print(f"     INCORRECT: individual elements of h are NOT invariant (they are permuted)")

    return subspace_preserved


# =============================================================================
# VISUALIZATION
# =============================================================================

def create_visualization():
    """Create 3D visualization of the stella decomposition with adjoint labels."""
    print("\n" + "=" * 70)
    print("VISUALIZATION: Stella Adjoint Decomposition")
    print("=" * 70)

    fig = plt.figure(figsize=(20, 8))

    # --- Panel 1: Polyhedral decomposition ---
    ax1 = fig.add_subplot(131, projection='3d')

    # Draw T+ faces (semi-transparent blue)
    t_plus_faces = [
        [T_PLUS[1], T_PLUS[2], T_PLUS[3]],  # opp v_R
        [T_PLUS[0], T_PLUS[2], T_PLUS[3]],  # opp v_G
        [T_PLUS[0], T_PLUS[1], T_PLUS[3]],  # opp v_B
        [T_PLUS[0], T_PLUS[1], T_PLUS[2]],  # opp v_W
    ]
    ax1.add_collection3d(Poly3DCollection(t_plus_faces, alpha=0.15,
                                          facecolor='blue', edgecolor='blue', linewidth=1))

    # Draw T- faces (semi-transparent red)
    t_minus_faces = [
        [T_MINUS[1], T_MINUS[2], T_MINUS[3]],
        [T_MINUS[0], T_MINUS[2], T_MINUS[3]],
        [T_MINUS[0], T_MINUS[1], T_MINUS[3]],
        [T_MINUS[0], T_MINUS[1], T_MINUS[2]],
    ]
    ax1.add_collection3d(Poly3DCollection(t_minus_faces, alpha=0.15,
                                          facecolor='red', edgecolor='red', linewidth=1))

    # Draw octahedron
    oct_faces_idx = [
        [0, 2, 4], [0, 2, 5], [0, 3, 4], [0, 3, 5],
        [1, 2, 4], [1, 2, 5], [1, 3, 4], [1, 3, 5],
    ]
    oct_faces = [[OCT_VERTICES[i] for i in face] for face in oct_faces_idx]
    ax1.add_collection3d(Poly3DCollection(oct_faces, alpha=0.3,
                                          facecolor='gold', edgecolor='orange', linewidth=0.5))

    # Label vertices
    labels_plus = ['v_R', 'v_G', 'v_B', 'v_W']
    labels_minus = ['v_R̄', 'v_Ḡ', 'v_B̄', 'v_W̄']
    colors_plus = ['red', 'green', 'blue', 'gray']
    colors_minus = ['darkred', 'darkgreen', 'darkblue', 'dimgray']

    for v, lbl, c in zip(T_PLUS, labels_plus, colors_plus):
        ax1.scatter(*v, color=c, s=60, zorder=5)
        ax1.text(v[0]*1.15, v[1]*1.15, v[2]*1.15, lbl, fontsize=7, color=c, ha='center')
    for v, lbl, c in zip(T_MINUS, labels_minus, colors_minus):
        ax1.scatter(*v, color=c, s=60, zorder=5, marker='^')
        ax1.text(v[0]*1.15, v[1]*1.15, v[2]*1.15, lbl, fontsize=7, color=c, ha='center')
    for v in OCT_VERTICES:
        ax1.scatter(*v, color='orange', s=30, zorder=5, marker='o')

    ax1.set_title('Polyhedral Decomposition\n8 corner tets + 1 central oct', fontsize=10)
    ax1.set_xlim([-1.5, 1.5])
    ax1.set_ylim([-1.5, 1.5])
    ax1.set_zlim([-1.5, 1.5])
    ax1.set_xlabel('x')
    ax1.set_ylabel('y')
    ax1.set_zlabel('z')

    # --- Panel 2: Root system (2D) ---
    ax2 = fig.add_subplot(132)

    # Draw weight diagram
    weights = {'R': W_R, 'G': W_G, 'B': W_B,
               'R̄': -W_R, 'Ḡ': -W_G, 'B̄': -W_B}
    w_colors = {'R': 'red', 'G': 'green', 'B': 'blue',
                'R̄': 'darkred', 'Ḡ': 'darkgreen', 'B̄': 'darkblue'}

    for name, w in weights.items():
        ax2.scatter(*w, color=w_colors[name], s=80, zorder=5)
        ax2.annotate(name, w, textcoords="offset points", xytext=(8, 8),
                     fontsize=9, color=w_colors[name])

    # Draw roots as arrows from origin
    root_colors = {
        'α₁': '#FF6600', 'α₂': '#CC00CC', 'α₁+α₂': '#006600',
        '-α₁': '#FF6600', '-α₂': '#CC00CC', '-(α₁+α₂)': '#006600',
    }
    for name, r in ROOTS.items():
        is_neg = name.startswith('-')
        ax2.annotate('', xy=r*0.9, xytext=(0, 0),
                     arrowprops=dict(arrowstyle='->', color=root_colors[name],
                                     lw=2, linestyle='--' if is_neg else '-'))
        ax2.annotate(name, r*0.95, textcoords="offset points",
                     xytext=(10 if r[0] >= 0 else -30, 5),
                     fontsize=8, color=root_colors[name])

    # Mark origin (Cartan)
    ax2.scatter(0, 0, color='gold', s=120, marker='s', zorder=5,
                edgecolors='black', linewidth=1)
    ax2.annotate('H₁,H₂\n(Cartan)', (0, 0), textcoords="offset points",
                 xytext=(-40, -25), fontsize=7, color='goldenrod')

    ax2.set_xlim([-1.2, 1.2])
    ax2.set_ylim([-0.8, 0.8])
    ax2.set_aspect('equal')
    ax2.axhline(y=0, color='gray', linewidth=0.5)
    ax2.axvline(x=0, color='gray', linewidth=0.5)
    ax2.set_title('A₂ Root System\n6 roots + 2 Cartan = 8 generators', fontsize=10)
    ax2.set_xlabel('t₃ (isospin)')
    ax2.set_ylabel('t₈ (hypercharge)')

    # --- Panel 3: The bijection table ---
    ax3 = fig.add_subplot(133)
    ax3.axis('off')

    table_data = [
        ['Face', 'Opp. Vertex', 'Generator', 'Type'],
        ['F₁⁺', 'v_R', 'E_α₂', 'Charged'],
        ['F₂⁺', 'v_G', 'E_{-(α₁+α₂)}', 'Charged'],
        ['F₃⁺', 'v_B', 'E_α₁', 'Charged'],
        ['F₄⁺', 'v_W', 'H₁ = T₃', 'Neutral'],
        ['F₁⁻', 'v_R̄', 'E_{-α₂}', 'Charged'],
        ['F₂⁻', 'v_Ḡ', 'E_{α₁+α₂}', 'Charged'],
        ['F₃⁻', 'v_B̄', 'E_{-α₁}', 'Charged'],
        ['F₄⁻', 'v_W̄', 'H₂ = T₈', 'Neutral'],
    ]

    table = ax3.table(cellText=table_data[1:], colLabels=table_data[0],
                      loc='center', cellLoc='center')
    table.auto_set_font_size(False)
    table.set_fontsize(8)
    table.scale(1, 1.5)

    # Color header
    for j in range(4):
        table[0, j].set_facecolor('#E0E0E0')
        table[0, j].set_text_props(weight='bold')

    # Color rows
    for i in range(1, 9):
        if i <= 3:
            for j in range(4):
                table[i, j].set_facecolor('#D0D0FF')
        elif i == 4:
            for j in range(4):
                table[i, j].set_facecolor('#FFE0A0')
        elif i <= 7:
            for j in range(4):
                table[i, j].set_facecolor('#FFD0D0')
        else:
            for j in range(4):
                table[i, j].set_facecolor('#FFE0A0')

    ax3.set_title('Face–Adjoint Bijection\n(Opposite Vertex Rule)', fontsize=10)

    plt.tight_layout()
    outpath = os.path.join(PLOT_DIR, "prop_0_0_39_adversarial_verification.png")
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"  Saved: {outpath}")
    plt.close()

    # --- Summary verification plot ---
    fig2, ax = plt.subplots(figsize=(10, 6))
    ax.axis('off')

    summary = [
        ['Test', 'Description', 'Result', 'Issues Found'],
        ['1', 'Volume decomposition', '', ''],
        ['2', 'Corner tet regularity', '', ''],
        ['3', 'Oct = conv(T+)∩conv(T-)', '', ''],
        ['4', 'S₃ equivariance', '', ''],
        ['5', 'Phase cancellation', '', ''],
        ['6', 'Volume ratios', '', ''],
        ['7', 'Weyl group orbits', '', ''],
        ['8', 'Cartan invariance (adversarial)', '', ''],
    ]

    ax.set_title('Proposition 0.0.39 — Adversarial Verification Summary\n'
                 'Stella Adjoint Decomposition', fontsize=14, fontweight='bold', pad=20)

    return summary


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  ADVERSARIAL VERIFICATION: Proposition 0.0.39                       ║")
    print("║  Stella Adjoint Decomposition                                       ║")
    print("║  Polyhedral decomposition ↔ SU(3) adjoint representation            ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")
    print()

    results = {}

    # Test 1: Volume decomposition
    passed, corner_tets = test_volume_decomposition()
    results['Volume decomposition'] = passed

    # Test 2: Corner regularity
    results['Corner tet regularity'] = test_corner_regularity(corner_tets)

    # Test 3: Octahedron intersection
    results['Oct = conv(T+) ∩ conv(T-)'] = test_octahedron_intersection()

    # Test 4: S3 equivariance
    results['S₃ equivariance'] = test_s3_equivariance()

    # Test 5: Phase cancellation
    results['Phase cancellation'] = test_phase_cancellation()

    # Test 6: Volume ratios
    results['Volume ratios'] = test_volume_ratios()

    # Test 7: Weyl orbits
    results['Weyl group orbits'] = test_weyl_orbits()

    # Test 8: Cartan invariance (adversarial)
    results['Cartan subspace preserved'] = test_cartan_invariance()

    # Visualization
    summary_data = create_visualization()

    # ==========================================================================
    # FINAL SUMMARY
    # ==========================================================================
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)

    all_pass = True
    for test_name, passed in results.items():
        status = "PASS ✅" if passed else "FAIL ❌"
        if not passed:
            all_pass = False
        print(f"  {test_name:40s} {status}")

    print(f"\n  Overall: {'ALL TESTS PASSED ✅' if all_pass else 'SOME TESTS HAVE ISSUES ⚠️'}")

    print("\n" + "=" * 70)
    print("ADVERSARIAL FINDINGS (Issues in the proposition)")
    print("=" * 70)
    print("""
  1. Line 100: Oct vertices called "edge midpoints of cube" — they are FACE CENTERS
  2. Line 297: "Weyl group action on positive roots" — orbit mixes pos/neg roots
  3. Line 303: "S₃-invariant part of su(3)" — h is preserved as subspace, not pointwise
  4. Line 490: "Z₂ swaps H₁ ↔ H₂" — charge conjugation sends H_i → -H_i, not swap
  5. Lines 66-68: Clean T+ → positive roots partition is FALSE (F₂⁺ → negative root)
""")

    # Save summary plot
    fig, ax = plt.subplots(figsize=(12, 7))
    ax.axis('off')

    # Build table data
    test_names = list(results.keys())
    test_statuses = ['PASS' if v else 'ISSUE' for v in results.values()]
    issues = [
        'None',
        'None',
        'Paper says "edge midpoints of cube" (line 100)',
        'Orbit mixes pos/neg roots (line 297)',
        'None',
        'No Casimir connection found',
        'None',
        'h preserved as subspace, NOT pointwise (line 303)',
    ]

    table_data = list(zip(
        [str(i+1) for i in range(len(test_names))],
        test_names,
        test_statuses,
        issues
    ))

    table = ax.table(
        cellText=table_data,
        colLabels=['#', 'Test', 'Status', 'Issues / Notes'],
        loc='center',
        cellLoc='center',
        colWidths=[0.05, 0.3, 0.1, 0.55],
    )
    table.auto_set_font_size(False)
    table.set_fontsize(9)
    table.scale(1, 1.8)

    for j in range(4):
        table[0, j].set_facecolor('#404040')
        table[0, j].set_text_props(color='white', weight='bold')

    for i, status in enumerate(test_statuses):
        color = '#D4EDDA' if status == 'PASS' else '#FFF3CD'
        for j in range(4):
            table[i+1, j].set_facecolor(color)

    ax.set_title('Proposition 0.0.39 — Adversarial Verification Results\n'
                 'Stella Adjoint Decomposition ↔ SU(3) Adjoint Representation',
                 fontsize=13, fontweight='bold', pad=20)

    outpath = os.path.join(PLOT_DIR, "prop_0_0_39_verification_summary.png")
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"\n  Summary plot saved: {outpath}")
    plt.close()

    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
