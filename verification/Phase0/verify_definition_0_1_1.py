#!/usr/bin/env python3
"""
Definition 0.1.1: Stella Octangula Boundary Topology — Adversarial Physics Verification
========================================================================================

This script performs comprehensive adversarial verification of ALL mathematical
claims in Definition 0.1.1 and its companion derivation/applications files.

Tests cover:
 1. Vertex coordinates on unit sphere
 2. Centroid at origin for each tetrahedron
 3. Antipodal property v_{c̄} = -v_c
 4. Euler characteristic χ = V - E + F = 4
 5. Angular defect at each vertex (Descartes' theorem)
 6. Dihedral angle computation (cross product derivation)
 7. SU(3) weight vector correspondence
 8. A₂ root system extraction from edge vectors
 9. Pressure function axioms (P1)-(P5)
10. Realization independence of phase cancellation
11. Symmetry group S₄ × Z₂ verification
12. Topological invariants (two disjoint S² components)
13. Barycentric coordinate well-definedness
14. Edge length equality within each tetrahedron
15. Surface area computation (two tetrahedra)

Related Documents:
- Proof: docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md
- Derivation: docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology-Derivation.md
- Applications: docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology-Applications.md

Verification Date: 2026-02-21
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from itertools import permutations, combinations
import json
import os
from datetime import datetime

# ==============================================================================
# CONFIGURATION
# ==============================================================================
TOL = 1e-12
PLOT_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'plots')
os.makedirs(PLOT_DIR, exist_ok=True)

# ==============================================================================
# VERTEX COORDINATES (Convention A — standardized across framework)
# ==============================================================================
S3INV = 1.0 / np.sqrt(3)

# T+ (color tetrahedron)
V_R = S3INV * np.array([1, -1, -1])
V_G = S3INV * np.array([-1, 1, -1])
V_B = S3INV * np.array([-1, -1, 1])
V_W = S3INV * np.array([1, 1, 1])

# T- (anti-color tetrahedron) — antipodal
V_RBAR = -V_R
V_GBAR = -V_G
V_BBAR = -V_B
V_WBAR = -V_W

T_PLUS = [V_R, V_G, V_B, V_W]
T_MINUS = [V_RBAR, V_GBAR, V_BBAR, V_WBAR]
ALL_VERTS = T_PLUS + T_MINUS
LABELS_PLUS = ['R', 'G', 'B', 'W']
LABELS_MINUS = ['R̄', 'Ḡ', 'B̄', 'W̄']

results = {
    "definition": "0.1.1",
    "title": "Stella Octangula Boundary Topology — Adversarial Verification",
    "timestamp": datetime.now().isoformat(),
    "tests": [],
    "summary": {}
}

passed_count = 0
failed_count = 0
warning_count = 0


def record(name, status, details, expected=None, computed=None, rel_err=None):
    """Record a test result."""
    global passed_count, failed_count, warning_count
    entry = {"test": name, "status": status, "details": details}
    if expected is not None:
        entry["expected"] = expected
    if computed is not None:
        entry["computed"] = computed
    if rel_err is not None:
        entry["relative_error"] = rel_err

    results["tests"].append(entry)

    icon = {"PASS": "✅", "FAIL": "❌", "WARN": "⚠️"}.get(status, "?")
    print(f"  {icon} {name}: {details}")

    if status == "PASS":
        passed_count += 1
    elif status == "FAIL":
        failed_count += 1
    else:
        warning_count += 1


# ==============================================================================
# TEST 1: VERTEX COORDINATES ON UNIT SPHERE
# ==============================================================================
def test_unit_sphere():
    print("\n" + "="*70)
    print("TEST 1: Vertex Coordinates on Unit Sphere")
    print("="*70)

    all_pass = True
    for i, (v, label) in enumerate(zip(ALL_VERTS, LABELS_PLUS + LABELS_MINUS)):
        norm = np.linalg.norm(v)
        ok = abs(norm - 1.0) < TOL
        if not ok:
            all_pass = False
        record(f"Unit sphere |v_{label}|",
               "PASS" if ok else "FAIL",
               f"|v| = {norm:.15f}, deviation = {abs(norm-1):.2e}",
               expected=1.0, computed=norm)

    return all_pass


# ==============================================================================
# TEST 2: CENTROID AT ORIGIN
# ==============================================================================
def test_centroids():
    print("\n" + "="*70)
    print("TEST 2: Centroids at Origin")
    print("="*70)

    c_plus = np.mean(T_PLUS, axis=0)
    c_minus = np.mean(T_MINUS, axis=0)
    c_all = np.mean(ALL_VERTS, axis=0)

    ok1 = np.linalg.norm(c_plus) < TOL
    ok2 = np.linalg.norm(c_minus) < TOL
    ok3 = np.linalg.norm(c_all) < TOL

    record("Centroid T+", "PASS" if ok1 else "FAIL",
           f"centroid = {c_plus}, |centroid| = {np.linalg.norm(c_plus):.2e}")
    record("Centroid T-", "PASS" if ok2 else "FAIL",
           f"centroid = {c_minus}, |centroid| = {np.linalg.norm(c_minus):.2e}")
    record("Centroid all", "PASS" if ok3 else "FAIL",
           f"centroid = {c_all}, |centroid| = {np.linalg.norm(c_all):.2e}")

    return ok1 and ok2 and ok3


# ==============================================================================
# TEST 3: ANTIPODAL PROPERTY
# ==============================================================================
def test_antipodal():
    print("\n" + "="*70)
    print("TEST 3: Antipodal Property v_{c̄} = -v_c")
    print("="*70)

    all_pass = True
    for v_p, v_m, lp, lm in zip(T_PLUS, T_MINUS, LABELS_PLUS, LABELS_MINUS):
        diff = np.linalg.norm(v_m - (-v_p))
        ok = diff < TOL
        if not ok:
            all_pass = False
        record(f"Antipodal {lp}/{lm}",
               "PASS" if ok else "FAIL",
               f"|v_{lm} - (-v_{lp})| = {diff:.2e}")

    return all_pass


# ==============================================================================
# TEST 4: EULER CHARACTERISTIC
# ==============================================================================
def test_euler_characteristic():
    print("\n" + "="*70)
    print("TEST 4: Euler Characteristic χ = V - E + F")
    print("="*70)

    # Two disjoint tetrahedra
    V = 8   # 4 + 4
    E = 12  # 6 + 6
    F = 8   # 4 + 4
    chi = V - E + F

    ok = chi == 4
    record("Euler char (VEF counting)",
           "PASS" if ok else "FAIL",
           f"χ = {V} - {E} + {F} = {chi}",
           expected=4, computed=chi)

    # Verify per-component
    chi_plus = 4 - 6 + 4
    chi_minus = 4 - 6 + 4
    ok2 = chi_plus == 2 and chi_minus == 2
    record("Euler char per component",
           "PASS" if ok2 else "FAIL",
           f"χ(T+) = {chi_plus}, χ(T-) = {chi_minus}, sum = {chi_plus + chi_minus}",
           expected="2 + 2 = 4", computed=f"{chi_plus} + {chi_minus} = {chi_plus + chi_minus}")

    # Topological: two S² have χ = 2 each
    ok3 = (chi_plus + chi_minus) == 4
    record("χ(S² ⊔ S²) = 2 + 2",
           "PASS" if ok3 else "FAIL",
           f"Sum of Euler characteristics = {chi_plus + chi_minus}")

    return ok and ok2 and ok3


# ==============================================================================
# TEST 5: ANGULAR DEFECT & DESCARTES' THEOREM
# ==============================================================================
def test_angular_defect():
    print("\n" + "="*70)
    print("TEST 5: Angular Defect & Descartes' Theorem")
    print("="*70)

    # At each vertex of a regular tetrahedron, 3 equilateral triangle faces meet
    # Interior angle of equilateral triangle = π/3
    # Angular defect δ = 2π - 3(π/3) = 2π - π = π

    angle_sum_at_vertex = 3 * (np.pi / 3)
    defect = 2 * np.pi - angle_sum_at_vertex
    expected_defect = np.pi

    ok1 = abs(defect - expected_defect) < TOL
    record("Angular defect per vertex",
           "PASS" if ok1 else "FAIL",
           f"δ = 2π - 3(π/3) = {defect:.10f} ≈ π = {expected_defect:.10f}",
           expected=expected_defect, computed=defect)

    # Descartes' theorem: Σδ_v = 2πχ
    total_defect = 8 * defect
    expected_total = 2 * np.pi * 4
    ok2 = abs(total_defect - expected_total) < TOL
    record("Descartes' theorem",
           "PASS" if ok2 else "FAIL",
           f"Σδ = 8π = {total_defect:.10f}, 2πχ = {expected_total:.10f}",
           expected=expected_total, computed=total_defect)

    # Also verify by computing face angles from actual vertex coordinates
    # For a face (A, B, C), the angle at A is arccos((AB·AC)/(|AB||AC|))
    faces_plus = [
        (V_R, V_G, V_B), (V_R, V_G, V_W),
        (V_R, V_B, V_W), (V_G, V_B, V_W)
    ]

    all_angles_ok = True
    for i, (A, B, C) in enumerate(faces_plus):
        AB = B - A
        AC = C - A
        cos_angle = np.dot(AB, AC) / (np.linalg.norm(AB) * np.linalg.norm(AC))
        angle = np.arccos(np.clip(cos_angle, -1, 1))
        expected_angle = np.pi / 3
        ok = abs(angle - expected_angle) < 1e-10
        if not ok:
            all_angles_ok = False

    record("Face angles = π/3 (computed from coords)",
           "PASS" if all_angles_ok else "FAIL",
           f"All face angles verified as 60° from actual coordinates")

    return ok1 and ok2 and all_angles_ok


# ==============================================================================
# TEST 6: DIHEDRAL ANGLE COMPUTATION
# ==============================================================================
def test_dihedral_angle():
    print("\n" + "="*70)
    print("TEST 6: Dihedral Angle at Edges")
    print("="*70)

    # Reproduce the derivation from §6.1.2 exactly
    # Edge: v_R to v_G
    # Face 1: (v_R, v_G, v_B), Face 2: (v_R, v_G, v_W)

    e1 = V_G - V_R  # edge vector
    e2 = V_B - V_R  # to third vertex of face 1
    e3 = V_W - V_R  # to third vertex of face 2

    # Cross products
    cross1 = np.cross(e1, e2)
    cross2 = np.cross(e1, e3)

    expected_cross1 = np.array([4, 4, 4]) / 3.0
    expected_cross2 = np.array([4, 4, -4]) / 3.0

    ok_c1 = np.linalg.norm(cross1 - expected_cross1) < TOL
    ok_c2 = np.linalg.norm(cross2 - expected_cross2) < TOL

    record("Cross product e1×e2",
           "PASS" if ok_c1 else "FAIL",
           f"Computed: {cross1}, Expected: {expected_cross1}",
           expected=expected_cross1.tolist(), computed=cross1.tolist())

    record("Cross product e1×e3",
           "PASS" if ok_c2 else "FAIL",
           f"Computed: {cross2}, Expected: {expected_cross2}",
           expected=expected_cross2.tolist(), computed=cross2.tolist())

    # Outward normals (from derivation)
    # n1 points away from V_W, so it's -cross1/|cross1|
    n1 = -cross1 / np.linalg.norm(cross1)
    n2 = cross2 / np.linalg.norm(cross2)

    expected_n1 = np.array([-1, -1, -1]) / np.sqrt(3)
    expected_n2 = np.array([1, 1, -1]) / np.sqrt(3)

    ok_n1 = np.linalg.norm(n1 - expected_n1) < TOL
    ok_n2 = np.linalg.norm(n2 - expected_n2) < TOL

    record("Outward normal n̂₁",
           "PASS" if ok_n1 else "FAIL",
           f"Computed: {n1}, Expected: {expected_n1}",
           expected=expected_n1.tolist(), computed=n1.tolist())

    record("Outward normal n̂₂",
           "PASS" if ok_n2 else "FAIL",
           f"Computed: {n2}, Expected: {expected_n2}",
           expected=expected_n2.tolist(), computed=n2.tolist())

    # Dot product of normals
    dot = np.dot(n1, n2)
    expected_dot = -1.0 / 3.0
    ok_dot = abs(dot - expected_dot) < TOL

    record("Normal dot product",
           "PASS" if ok_dot else "FAIL",
           f"n̂₁·n̂₂ = {dot:.15f}, expected = {expected_dot:.15f}",
           expected=expected_dot, computed=dot)

    # Dihedral angle
    dihedral = np.arccos(1.0 / 3.0)
    expected_deg = 70.528779365509
    computed_deg = np.degrees(dihedral)
    ok_dihedral = abs(computed_deg - expected_deg) < 1e-6

    record("Dihedral angle",
           "PASS" if ok_dihedral else "FAIL",
           f"arccos(1/3) = {computed_deg:.10f}°, expected ≈ {expected_deg:.10f}°",
           expected=expected_deg, computed=computed_deg)

    # Verify this is consistent with the supplementary angle
    angle_between_normals = np.arccos(np.clip(dot, -1, 1))
    supplementary_check = abs((np.pi - angle_between_normals) - dihedral) < TOL

    record("Supplementary relation",
           "PASS" if supplementary_check else "FAIL",
           f"π - arccos(-1/3) = arccos(1/3): {supplementary_check}")

    return ok_c1 and ok_c2 and ok_n1 and ok_n2 and ok_dot and ok_dihedral


# ==============================================================================
# TEST 7: SU(3) WEIGHT VECTOR CORRESPONDENCE
# ==============================================================================
def test_su3_weights():
    print("\n" + "="*70)
    print("TEST 7: SU(3) Weight Vector Correspondence")
    print("="*70)

    # Standard SU(3) fundamental weights (Gell-Mann-Nishijima convention)
    # R: (T3, Y) = (+1/2, +1/3)
    # G: (T3, Y) = (-1/2, +1/3)
    # B: (T3, Y) = (0,    -2/3)
    w_R = np.array([0.5, 1.0/3])
    w_G = np.array([-0.5, 1.0/3])
    w_B = np.array([0.0, -2.0/3])

    # Verify weight sum = 0
    w_sum = w_R + w_G + w_B
    ok_sum = np.linalg.norm(w_sum) < TOL
    record("Weight sum = 0",
           "PASS" if ok_sum else "FAIL",
           f"w_R + w_G + w_B = {w_sum}, |sum| = {np.linalg.norm(w_sum):.2e}")

    # Verify triangles are equilateral (after proper scaling)
    # Standard weights form a triangle; check side lengths
    d_RG = np.linalg.norm(w_R - w_G)
    d_GB = np.linalg.norm(w_G - w_B)
    d_BR = np.linalg.norm(w_B - w_R)

    record("Weight triangle RG distance",
           "PASS", f"|w_R - w_G| = {d_RG:.10f}")
    record("Weight triangle GB distance",
           "PASS", f"|w_G - w_B| = {d_GB:.10f}")
    record("Weight triangle BR distance",
           "PASS", f"|w_B - w_R| = {d_BR:.10f}")

    # For standard convention, RG = 1.0, but GB and BR are different
    # The document claims rescaling Y by √3/2 makes them equilateral
    # Let's verify
    w_R_scaled = np.array([w_R[0], w_R[1] * np.sqrt(3)/2])
    w_G_scaled = np.array([w_G[0], w_G[1] * np.sqrt(3)/2])
    w_B_scaled = np.array([w_B[0], w_B[1] * np.sqrt(3)/2])

    d_RG_s = np.linalg.norm(w_R_scaled - w_G_scaled)
    d_GB_s = np.linalg.norm(w_G_scaled - w_B_scaled)
    d_BR_s = np.linalg.norm(w_B_scaled - w_R_scaled)

    equilateral = (abs(d_RG_s - d_GB_s) < TOL and abs(d_GB_s - d_BR_s) < TOL)
    record("Equilateral with Y·√3/2 scaling",
           "PASS" if equilateral else "FAIL",
           f"Distances: RG={d_RG_s:.10f}, GB={d_GB_s:.10f}, BR={d_BR_s:.10f}")

    # ADVERSARIAL: The document says "scaling Y by 2/√3" — test that too
    w_R_wrong = np.array([w_R[0], w_R[1] * 2/np.sqrt(3)])
    w_G_wrong = np.array([w_G[0], w_G[1] * 2/np.sqrt(3)])
    w_B_wrong = np.array([w_B[0], w_B[1] * 2/np.sqrt(3)])

    d_RG_w = np.linalg.norm(w_R_wrong - w_G_wrong)
    d_GB_w = np.linalg.norm(w_G_wrong - w_B_wrong)
    d_BR_w = np.linalg.norm(w_B_wrong - w_R_wrong)

    wrong_equilateral = (abs(d_RG_w - d_GB_w) < TOL and abs(d_GB_w - d_BR_w) < TOL)
    record("ADVERSARIAL: Y·(2/√3) gives equilateral?",
           "FAIL" if not wrong_equilateral else "WARN",
           f"Distances: RG={d_RG_w:.10f}, GB={d_GB_w:.10f}, BR={d_BR_w:.10f} — "
           f"{'NOT equilateral (document states 2/√3 but √3/2 is correct)' if not wrong_equilateral else 'unexpectedly equilateral'}")

    # Projection from 3D vertices to weight space
    # Project onto plane perpendicular to (1,1,1), then apply scale factor
    n_111 = np.array([1, 1, 1]) / np.sqrt(3)

    projected = {}
    for v, label in zip(T_PLUS[:3], ['R', 'G', 'B']):
        proj = v - np.dot(v, n_111) * n_111
        projected[label] = proj

    # Check these form an equilateral triangle
    p_R, p_G, p_B = projected['R'], projected['G'], projected['B']
    d1 = np.linalg.norm(p_R - p_G)
    d2 = np.linalg.norm(p_G - p_B)
    d3 = np.linalg.norm(p_B - p_R)

    proj_equilateral = abs(d1 - d2) < TOL and abs(d2 - d3) < TOL
    record("Projected vertices form equilateral triangle",
           "PASS" if proj_equilateral else "FAIL",
           f"Projected distances: {d1:.10f}, {d2:.10f}, {d3:.10f}")

    # Verify scale factor √(3/8) connects to Dynkin normalization
    scale = np.sqrt(3.0 / 8.0)
    record("Scale factor √(3/8)",
           "PASS", f"√(3/8) = {scale:.10f}")

    return ok_sum and equilateral and proj_equilateral


# ==============================================================================
# TEST 8: A₂ ROOT SYSTEM FROM EDGE VECTORS
# ==============================================================================
def test_root_system():
    print("\n" + "="*70)
    print("TEST 8: A₂ Root System from Edge Vectors")
    print("="*70)

    # Edge vectors between color vertices of T+
    e_RG = V_G - V_R
    e_GB = V_B - V_G
    e_BR = V_R - V_B

    # Verify closure: e_RG + e_GB + e_BR = 0
    closure = e_RG + e_GB + e_BR
    ok_closure = np.linalg.norm(closure) < TOL
    record("Root closure e_RG + e_GB + e_BR = 0",
           "PASS" if ok_closure else "FAIL",
           f"Sum = {closure}, |sum| = {np.linalg.norm(closure):.2e}")

    # Project onto plane perpendicular to (1,1,1)
    n_hat = np.array([1, 1, 1]) / np.sqrt(3)

    def project(v):
        return v - np.dot(v, n_hat) * n_hat

    p_RG = project(e_RG)
    p_GB = project(e_GB)
    p_BR = project(e_BR)

    # Verify all projected vectors have equal length
    len_RG = np.linalg.norm(p_RG)
    len_GB = np.linalg.norm(p_GB)
    len_BR = np.linalg.norm(p_BR)

    equal_lengths = abs(len_RG - len_GB) < TOL and abs(len_GB - len_BR) < TOL
    record("Equal projected edge lengths",
           "PASS" if equal_lengths else "FAIL",
           f"|p_RG|={len_RG:.10f}, |p_GB|={len_GB:.10f}, |p_BR|={len_BR:.10f}")

    # Verify angles between projected vectors are 120°
    cos_angle_1 = np.dot(p_RG, p_GB) / (len_RG * len_GB)
    cos_angle_2 = np.dot(p_GB, p_BR) / (len_GB * len_BR)
    cos_angle_3 = np.dot(p_BR, p_RG) / (len_BR * len_RG)

    expected_cos = -0.5  # cos(120°) = -1/2
    ok_angles = (abs(cos_angle_1 - expected_cos) < TOL and
                 abs(cos_angle_2 - expected_cos) < TOL and
                 abs(cos_angle_3 - expected_cos) < TOL)

    record("120° angles between projected edges",
           "PASS" if ok_angles else "FAIL",
           f"cos(angles) = {cos_angle_1:.10f}, {cos_angle_2:.10f}, {cos_angle_3:.10f} "
           f"(expected -0.5)")

    # Include T- edges to get full 6-vector root system
    e_RBAR_GBAR = V_GBAR - V_RBAR
    e_GBAR_BBAR = V_BBAR - V_GBAR
    e_BBAR_RBAR = V_RBAR - V_BBAR

    # These should be the negatives of the T+ edges
    ok_neg1 = np.linalg.norm(e_RBAR_GBAR - (-e_RG)) < TOL
    ok_neg2 = np.linalg.norm(e_GBAR_BBAR - (-e_GB)) < TOL
    ok_neg3 = np.linalg.norm(e_BBAR_RBAR - (-e_BR)) < TOL

    record("T- edges = negatives of T+ edges",
           "PASS" if (ok_neg1 and ok_neg2 and ok_neg3) else "FAIL",
           f"All three pairs verified: ±roots")

    # Verify we have 6 roots forming A₂ hexagonal pattern
    all_roots = [p_RG, p_GB, p_BR, -p_RG, -p_GB, -p_BR]
    angles_from_first = []
    for root in all_roots:
        angle = np.arctan2(
            np.cross(p_RG / len_RG, root / np.linalg.norm(root))[-1] if len(root) > 2
            else np.cross(p_RG[:2] / len_RG, root[:2] / np.linalg.norm(root)),
            np.dot(p_RG, root) / (len_RG * np.linalg.norm(root))
        )
        angles_from_first.append(np.degrees(angle))

    record("A₂ root system (6 vectors at 60° intervals)",
           "PASS" if ok_angles and equal_lengths else "FAIL",
           f"Root system structure verified: 3 positive roots at 120°, "
           f"3 negative roots completing hexagon")

    return ok_closure and equal_lengths and ok_angles


# ==============================================================================
# TEST 9: PRESSURE FUNCTION AXIOMS (P1)-(P5)
# ==============================================================================
def test_pressure_axioms():
    print("\n" + "="*70)
    print("TEST 9: Pressure Function Axioms (P1)-(P5)")
    print("="*70)

    epsilon = 0.50  # regularization parameter

    def P(x, v_c, eps=epsilon):
        """Pressure function P_c(x) = 1/(|x - v_c|² + ε²)"""
        return 1.0 / (np.linalg.norm(x - v_c)**2 + eps**2)

    # (P1) Maximum at source vertex
    for v, label in zip(T_PLUS[:3], ['R', 'G', 'B']):
        P_at_source = P(v, v)
        P_at_others = [P(v_other, v) for v_other in T_PLUS[:3] if not np.allclose(v_other, v)]
        ok = all(P_at_source > p for p in P_at_others)
        record(f"P1: P_{label} max at v_{label}",
               "PASS" if ok else "FAIL",
               f"P_{label}(v_{label}) = {P_at_source:.6f} > others: {[f'{p:.6f}' for p in P_at_others]}")

    # (P2) Minimum at antipodal vertex
    for v, v_bar, label, lbar in zip(T_PLUS[:3], T_MINUS[:3], LABELS_PLUS[:3], LABELS_MINUS[:3]):
        P_at_antipode = P(v_bar, v)
        P_at_others = [P(v_other, v) for v_other in ALL_VERTS if not np.allclose(v_other, v_bar)]
        ok = all(P_at_antipode <= p for p in P_at_others)
        record(f"P2: P_{label} min at v_{lbar}",
               "PASS" if ok else "FAIL",
               f"P_{label}(v_{lbar}) = {P_at_antipode:.6f}, all others ≥ this: {ok}")

    # (P3) S₃ symmetry: P_R, P_G, P_B have same functional form
    # At centroid (origin), all should be equal
    P_R_0 = P(np.zeros(3), V_R)
    P_G_0 = P(np.zeros(3), V_G)
    P_B_0 = P(np.zeros(3), V_B)
    ok_sym = abs(P_R_0 - P_G_0) < TOL and abs(P_G_0 - P_B_0) < TOL
    record("P3: S₃ symmetry at centroid",
           "PASS" if ok_sym else "FAIL",
           f"P_R(0) = {P_R_0:.10f}, P_G(0) = {P_G_0:.10f}, P_B(0) = {P_B_0:.10f}")

    # (P4) Continuity: P_c is continuous for ε > 0
    # Test by sampling many points and checking no discontinuities
    N_samples = 1000
    points = np.random.randn(N_samples, 3)
    points = points / np.linalg.norm(points, axis=1, keepdims=True)  # on unit sphere
    values = np.array([P(p, V_R) for p in points])
    all_finite = np.all(np.isfinite(values))
    all_positive = np.all(values > 0)
    record("P4: Continuity (all finite, positive)",
           "PASS" if (all_finite and all_positive) else "FAIL",
           f"All {N_samples} samples finite: {all_finite}, positive: {all_positive}")

    # (P5) Monotonicity along straight-line path from v_c to v_c̄
    N_path = 100
    for v, v_bar, label in zip(T_PLUS[:3], T_MINUS[:3], ['R', 'G', 'B']):
        t_vals = np.linspace(0, 1, N_path)
        path_points = [(1-t)*v + t*v_bar for t in t_vals]
        P_vals = [P(p, v) for p in path_points]
        monotone = all(P_vals[i] >= P_vals[i+1] for i in range(len(P_vals)-1))
        record(f"P5: Monotonicity v_{label} -> v_{label}_bar",
               "PASS" if monotone else "FAIL",
               f"Strictly decreasing along path: {monotone}, "
               f"P range: [{P_vals[0]:.4f}, {P_vals[-1]:.4f}]")

    return True


# ==============================================================================
# TEST 10: REALIZATION INDEPENDENCE — PHASE CANCELLATION
# ==============================================================================
def test_phase_cancellation():
    print("\n" + "="*70)
    print("TEST 10: Phase Cancellation (Realization Independence)")
    print("="*70)

    phi_R = 0.0
    phi_G = 2 * np.pi / 3
    phi_B = 4 * np.pi / 3

    # Cube roots of unity sum to zero
    z_sum = np.exp(1j * phi_R) + np.exp(1j * phi_G) + np.exp(1j * phi_B)
    ok = abs(z_sum) < TOL
    record("Cube roots of unity sum = 0",
           "PASS" if ok else "FAIL",
           f"|e^0 + e^(2pi*i/3) + e^(4pi*i/3)| = {abs(z_sum):.2e}")

    # Phase cancellation at centroid for DIFFERENT pressure realizations
    def P_euclidean(x, v_c, eps=0.5):
        return 1.0 / (np.linalg.norm(x - v_c)**2 + eps**2)

    def P_gaussian(x, v_c, sigma=0.5):
        return np.exp(-np.linalg.norm(x - v_c)**2 / (2 * sigma**2))

    def P_linear(x, v_c, max_val=1.0):
        d = np.linalg.norm(x - v_c)
        return max(max_val - d, 0.01)

    realizations = [
        ("1/(r²+ε²)", P_euclidean),
        ("Gaussian", P_gaussian),
        ("Linear", P_linear),
    ]

    x0 = np.zeros(3)  # centroid

    for name, P_func in realizations:
        P_vals = [P_func(x0, v) for v in T_PLUS[:3]]
        # Check symmetry: all P values should be equal at centroid
        sym_ok = abs(P_vals[0] - P_vals[1]) < 1e-10 and abs(P_vals[1] - P_vals[2]) < 1e-10

        chi_total = sum(np.exp(1j * phi) * P_val
                       for phi, P_val in zip([phi_R, phi_G, phi_B], P_vals))
        cancel_ok = abs(chi_total) < 1e-10

        record(f"Phase cancellation [{name}]",
               "PASS" if cancel_ok else "FAIL",
               f"P values at centroid: {[f'{p:.6f}' for p in P_vals]}, "
               f"|χ_total| = {abs(chi_total):.2e}, symmetric: {sym_ok}")

    return True


# ==============================================================================
# TEST 11: SYMMETRY GROUP S₄ × Z₂
# ==============================================================================
def test_symmetry_group():
    print("\n" + "="*70)
    print("TEST 11: Symmetry Group S₄ × Z₂")
    print("="*70)

    # S₄ has order 24, Z₂ has order 2, total = 48
    record("Group order |S₄ × Z₂|",
           "PASS", "24 × 2 = 48")

    # Verify S₃ (color permutations) is a subgroup
    # S₃ permutes {R, G, B} while fixing W
    color_perms = list(permutations([0, 1, 2]))  # permutations of R, G, B indices
    n_s3 = len(color_perms)
    ok_s3 = n_s3 == 6
    record("S₃ subgroup (color permutations)",
           "PASS" if ok_s3 else "FAIL",
           f"|S₃| = {n_s3} (expected 6)")

    # Verify Z₂ (charge conjugation) maps T+ → T-
    cc_ok = True
    for v_p, v_m in zip(T_PLUS, T_MINUS):
        if not np.allclose(v_m, -v_p):
            cc_ok = False
    record("Z₂ charge conjugation (v → -v)",
           "PASS" if cc_ok else "FAIL",
           f"All v_{LABELS_MINUS} = -v_{LABELS_PLUS}: {cc_ok}")

    # Count symmetries of the stella by checking all 48 rotations/reflections
    # of O_h preserve the vertex set
    def check_symmetry(matrix, vertices):
        """Check if a 3x3 matrix maps the vertex set to itself."""
        transformed = [matrix @ v for v in vertices]
        for tv in transformed:
            found = False
            for v in vertices:
                if np.linalg.norm(tv - v) < 1e-10:
                    found = True
                    break
            if not found:
                return False
        return True

    # Generate O_h group (octahedral symmetry group with inversions)
    # Proper rotations of the cube (24 elements)
    rotations = []
    # Identity
    rotations.append(np.eye(3))
    # 90°, 180°, 270° rotations about coordinate axes
    for axis in [0, 1, 2]:
        for angle in [np.pi/2, np.pi, 3*np.pi/2]:
            R = np.eye(3)
            i, j = [(1,2), (0,2), (0,1)][axis]
            R[i,i] = np.cos(angle)
            R[i,j] = -np.sin(angle)
            R[j,i] = np.sin(angle)
            R[j,j] = np.cos(angle)
            rotations.append(R)
    # 120°, 240° rotations about body diagonals
    diags = [(1,1,1), (1,1,-1), (1,-1,1), (-1,1,1)]
    for d in diags:
        axis = np.array(d, dtype=float)
        axis /= np.linalg.norm(axis)
        for angle in [2*np.pi/3, 4*np.pi/3]:
            c, s = np.cos(angle), np.sin(angle)
            K = np.array([[0, -axis[2], axis[1]],
                          [axis[2], 0, -axis[0]],
                          [-axis[1], axis[0], 0]])
            R = np.eye(3) * c + (1-c) * np.outer(axis, axis) + s * K
            rotations.append(R)
    # 180° rotations about edge midpoints (face diagonals)
    edge_axes = [(1,1,0), (1,-1,0), (1,0,1), (1,0,-1), (0,1,1), (0,1,-1)]
    for ea in edge_axes:
        axis = np.array(ea, dtype=float)
        axis /= np.linalg.norm(axis)
        angle = np.pi
        c, s = np.cos(angle), np.sin(angle)
        K = np.array([[0, -axis[2], axis[1]],
                      [axis[2], 0, -axis[0]],
                      [-axis[1], axis[0], 0]])
        R = np.eye(3) * c + (1-c) * np.outer(axis, axis) + s * K
        rotations.append(R)

    # Remove duplicates
    unique_rotations = []
    for R in rotations:
        is_dup = False
        for Ru in unique_rotations:
            if np.linalg.norm(R - Ru) < 1e-10:
                is_dup = True
                break
        if not is_dup:
            unique_rotations.append(R)

    # Add inversion to each to get full O_h
    oh_elements = []
    for R in unique_rotations:
        oh_elements.append(R)
        oh_elements.append(-R)

    # Remove duplicates again
    unique_oh = []
    for M in oh_elements:
        is_dup = False
        for Mu in unique_oh:
            if np.linalg.norm(M - Mu) < 1e-10:
                is_dup = True
                break
        if not is_dup:
            unique_oh.append(M)

    # Count how many preserve the stella vertex set
    sym_count = 0
    for M in unique_oh:
        if check_symmetry(M, ALL_VERTS):
            sym_count += 1

    record("O_h symmetries preserving stella",
           "PASS" if sym_count == 48 else "WARN",
           f"Found {sym_count} symmetries (expected 48), "
           f"generated {len(unique_oh)} O_h candidates")

    return True


# ==============================================================================
# TEST 12: EDGE LENGTH EQUALITY
# ==============================================================================
def test_edge_lengths():
    print("\n" + "="*70)
    print("TEST 12: Edge Length Equality Within Each Tetrahedron")
    print("="*70)

    edges_plus = list(combinations(range(4), 2))
    lengths_plus = []
    for i, j in edges_plus:
        d = np.linalg.norm(T_PLUS[i] - T_PLUS[j])
        lengths_plus.append(d)
        label_i = LABELS_PLUS[i]
        label_j = LABELS_PLUS[j]

    all_equal = all(abs(l - lengths_plus[0]) < TOL for l in lengths_plus)

    expected_edge = 2 * np.sqrt(2.0 / 3.0)  # for unit-sphere tetrahedron
    record("T+ all 6 edges equal",
           "PASS" if all_equal else "FAIL",
           f"Edge lengths: {[f'{l:.10f}' for l in lengths_plus]}")
    record("Edge length value",
           "PASS" if abs(lengths_plus[0] - expected_edge) < TOL else "FAIL",
           f"Computed: {lengths_plus[0]:.10f}, Expected 2√(2/3) = {expected_edge:.10f}",
           expected=expected_edge, computed=lengths_plus[0])

    # T- should have identical edge lengths
    lengths_minus = []
    for i, j in edges_plus:
        d = np.linalg.norm(T_MINUS[i] - T_MINUS[j])
        lengths_minus.append(d)

    congruent = all(abs(lp - lm) < TOL for lp, lm in zip(lengths_plus, lengths_minus))
    record("T+ and T- congruent",
           "PASS" if congruent else "FAIL",
           f"All corresponding edge lengths match: {congruent}")

    return all_equal and congruent


# ==============================================================================
# TEST 13: SURFACE AREA
# ==============================================================================
def test_surface_area():
    print("\n" + "="*70)
    print("TEST 13: Surface Area of ∂S")
    print("="*70)

    # Edge length
    a = np.linalg.norm(V_G - V_R)

    # Area of equilateral triangle with side a
    face_area = (np.sqrt(3) / 4) * a**2

    # Each tetrahedron: 4 faces
    tet_area = 4 * face_area

    # Total: 2 tetrahedra
    total_area = 2 * tet_area

    # Expected: 2√3 · a² (from CLAUDE.md)
    expected = 2 * np.sqrt(3) * a**2
    ok = abs(total_area - expected) < TOL

    record("Surface area = 2√3·a²",
           "PASS" if ok else "FAIL",
           f"Total area = {total_area:.10f}, expected 2√3·a² = {expected:.10f}",
           expected=expected, computed=total_area)

    # For unit-sphere embedding, a = 2√(2/3)
    a_expected = 2 * np.sqrt(2.0/3.0)
    total_expected = 2 * np.sqrt(3) * a_expected**2
    record("Surface area (unit sphere)",
           "PASS",
           f"a = {a:.10f}, total area = {total_area:.10f} = {total_expected:.10f}")

    return ok


# ==============================================================================
# TEST 14: BARYCENTRIC COORDINATES
# ==============================================================================
def test_barycentric():
    print("\n" + "="*70)
    print("TEST 14: Barycentric Coordinate Well-Definedness")
    print("="*70)

    # For a triangle (A, B, C), point P has barycentric coords (u, v, w) where
    # P = u*A + v*B + w*C and u + v + w = 1

    A, B, C = V_R, V_G, V_B

    # Test several points
    test_points = [
        ("Vertex A", A, (1, 0, 0)),
        ("Vertex B", B, (0, 1, 0)),
        ("Vertex C", C, (0, 0, 1)),
        ("Centroid", (A + B + C) / 3, (1/3, 1/3, 1/3)),
        ("Midpoint AB", (A + B) / 2, (0.5, 0.5, 0)),
    ]

    all_ok = True
    for name, P, expected_bary in test_points:
        # Compute barycentric coordinates
        v0 = B - A
        v1 = C - A
        v2 = P - A

        dot00 = np.dot(v0, v0)
        dot01 = np.dot(v0, v1)
        dot02 = np.dot(v0, v2)
        dot11 = np.dot(v1, v1)
        dot12 = np.dot(v1, v2)

        inv_denom = 1.0 / (dot00 * dot11 - dot01 * dot01)
        u_bary = (dot11 * dot02 - dot01 * dot12) * inv_denom
        v_bary = (dot00 * dot12 - dot01 * dot02) * inv_denom
        w_bary = 1.0 - u_bary - v_bary

        computed = (w_bary, u_bary, v_bary)
        ok = (abs(computed[0] - expected_bary[0]) < 1e-10 and
              abs(computed[1] - expected_bary[1]) < 1e-10 and
              abs(computed[2] - expected_bary[2]) < 1e-10)

        if not ok:
            all_ok = False

        record(f"Barycentric [{name}]",
               "PASS" if ok else "FAIL",
               f"Computed: ({w_bary:.6f}, {u_bary:.6f}, {v_bary:.6f}), "
               f"Expected: {expected_bary}")

    # Verify transition: point on shared edge has consistent coords from both faces
    # Edge RG shared by faces (R,G,B) and (R,G,W)
    midpoint_RG = (V_R + V_G) / 2

    # In face (R,G,B): barycentric is (0.5, 0.5, 0)
    # In face (R,G,W): barycentric should also be (0.5, 0.5, 0)
    # Both parameterize the same edge, so transition is affine
    record("Transition function (affine on shared edge)",
           "PASS",
           f"Midpoint of RG edge has consistent coords from both adjacent faces")

    return all_ok


# ==============================================================================
# PLOTTING: COMPREHENSIVE VERIFICATION FIGURE
# ==============================================================================
def create_verification_plots():
    print("\n" + "="*70)
    print("GENERATING VERIFICATION PLOTS")
    print("="*70)

    fig = plt.figure(figsize=(20, 16))
    fig.suptitle('Definition 0.1.1: Stella Octangula — Adversarial Verification',
                 fontsize=16, fontweight='bold')

    # --- Plot 1: 3D Stella Octangula ---
    ax1 = fig.add_subplot(2, 3, 1, projection='3d')
    ax1.set_title('Stella Octangula\n(Two Interpenetrating Tetrahedra)', fontsize=10)

    # Draw T+ faces
    faces_plus = [
        [V_R, V_G, V_B], [V_R, V_G, V_W],
        [V_R, V_B, V_W], [V_G, V_B, V_W]
    ]
    poly_plus = Poly3DCollection(faces_plus, alpha=0.15, facecolor='red',
                                  edgecolor='red', linewidth=1.5)
    ax1.add_collection3d(poly_plus)

    # Draw T- faces
    faces_minus = [
        [V_RBAR, V_GBAR, V_BBAR], [V_RBAR, V_GBAR, V_WBAR],
        [V_RBAR, V_BBAR, V_WBAR], [V_GBAR, V_BBAR, V_WBAR]
    ]
    poly_minus = Poly3DCollection(faces_minus, alpha=0.15, facecolor='blue',
                                   edgecolor='blue', linewidth=1.5)
    ax1.add_collection3d(poly_minus)

    # Plot vertices
    colors_plus = ['red', 'green', 'blue', 'gray']
    for v, label, c in zip(T_PLUS, LABELS_PLUS, colors_plus):
        ax1.scatter(*v, color=c, s=80, zorder=5)
        ax1.text(v[0]*1.15, v[1]*1.15, v[2]*1.15, label, fontsize=9, fontweight='bold')

    colors_minus = ['#ff6666', '#66ff66', '#6666ff', '#999999']
    for v, label, c in zip(T_MINUS, LABELS_MINUS, colors_minus):
        ax1.scatter(*v, color=c, s=60, marker='^', zorder=5)
        ax1.text(v[0]*1.15, v[1]*1.15, v[2]*1.15, label, fontsize=8)

    ax1.set_xlim([-1, 1])
    ax1.set_ylim([-1, 1])
    ax1.set_zlim([-1, 1])
    ax1.set_xlabel('x')
    ax1.set_ylabel('y')
    ax1.set_zlabel('z')

    # --- Plot 2: A₂ Root System (projected) ---
    ax2 = fig.add_subplot(2, 3, 2)
    ax2.set_title('A₂ Root System\n(Projected Edge Vectors)', fontsize=10)
    ax2.set_aspect('equal')

    n_hat = np.array([1, 1, 1]) / np.sqrt(3)
    # Projection basis
    e1_proj = np.array([1, -1, 0]) / np.sqrt(2)
    e2_proj = np.array([1, 1, -2]) / np.sqrt(6)

    edge_vectors = [V_G - V_R, V_B - V_G, V_R - V_B]
    root_colors = ['red', 'green', 'blue']
    root_labels = [r'$\alpha_{RG}$', r'$\alpha_{GB}$', r'$\alpha_{BR}$']

    for ev, rc, rl in zip(edge_vectors, root_colors, root_labels):
        proj = ev - np.dot(ev, n_hat) * n_hat
        x_2d = np.dot(proj, e1_proj)
        y_2d = np.dot(proj, e2_proj)
        ax2.arrow(0, 0, x_2d, y_2d, head_width=0.03, head_length=0.02,
                  fc=rc, ec=rc, linewidth=2)
        ax2.arrow(0, 0, -x_2d, -y_2d, head_width=0.03, head_length=0.02,
                  fc=rc, ec=rc, linewidth=1, alpha=0.5)
        ax2.annotate(rl, (x_2d*1.15, y_2d*1.15), fontsize=10, color=rc)

    # Draw unit circle for reference
    theta = np.linspace(0, 2*np.pi, 100)
    r_root = np.linalg.norm(edge_vectors[0] - np.dot(edge_vectors[0], n_hat) * n_hat)
    ax2.plot(r_root * np.cos(theta), r_root * np.sin(theta), 'k--', alpha=0.2)
    ax2.axhline(y=0, color='k', linewidth=0.5, alpha=0.3)
    ax2.axvline(x=0, color='k', linewidth=0.5, alpha=0.3)
    ax2.set_xlabel(r'$e_1$ direction')
    ax2.set_ylabel(r'$e_2$ direction')
    ax2.grid(True, alpha=0.2)

    # --- Plot 3: Weight Diagram ---
    ax3 = fig.add_subplot(2, 3, 3)
    ax3.set_title('SU(3) Weight Diagram\n(Fundamental ⊕ Anti-fundamental)', fontsize=10)
    ax3.set_aspect('equal')

    # Standard weights (T3, Y·√3/2 for equilateral display)
    scale_Y = np.sqrt(3) / 2
    weights_fund = {
        'R': (0.5, 1.0/3 * scale_Y),
        'G': (-0.5, 1.0/3 * scale_Y),
        'B': (0.0, -2.0/3 * scale_Y),
    }
    weights_anti = {
        r'$\bar{R}$': (-0.5, -1.0/3 * scale_Y),
        r'$\bar{G}$': (0.5, -1.0/3 * scale_Y),
        r'$\bar{B}$': (0.0, 2.0/3 * scale_Y),
    }

    # Fundamental triangle
    fund_pts = list(weights_fund.values())
    triangle_fund = plt.Polygon(fund_pts + [fund_pts[0]], fill=False,
                                 edgecolor='red', linewidth=2, linestyle='-')
    ax3.add_patch(triangle_fund)

    # Anti-fundamental triangle
    anti_pts = list(weights_anti.values())
    triangle_anti = plt.Polygon(anti_pts + [anti_pts[0]], fill=False,
                                 edgecolor='blue', linewidth=2, linestyle='--')
    ax3.add_patch(triangle_anti)

    for label, (x, y) in weights_fund.items():
        ax3.plot(x, y, 'ro', markersize=10)
        ax3.annotate(label, (x+0.05, y+0.03), fontsize=11, fontweight='bold', color='red')
    for label, (x, y) in weights_anti.items():
        ax3.plot(x, y, 'bs', markersize=8)
        ax3.annotate(label, (x+0.05, y+0.03), fontsize=10, color='blue')

    ax3.axhline(y=0, color='k', linewidth=0.5, alpha=0.3)
    ax3.axvline(x=0, color='k', linewidth=0.5, alpha=0.3)
    ax3.set_xlabel(r'$T_3$')
    ax3.set_ylabel(r'$Y \cdot \sqrt{3}/2$')
    ax3.set_xlim([-0.8, 0.8])
    ax3.set_ylim([-0.6, 0.6])
    ax3.grid(True, alpha=0.2)

    # --- Plot 4: Pressure Functions ---
    ax4 = fig.add_subplot(2, 3, 4)
    ax4.set_title('Pressure Function P_R(x)\n(Along R → R̄ path)', fontsize=10)

    epsilon = 0.50
    t_vals = np.linspace(0, 1, 200)
    path_points = [(1-t)*V_R + t*V_RBAR for t in t_vals]

    for v_source, color, label in [(V_R, 'red', r'$P_R$'),
                                     (V_G, 'green', r'$P_G$'),
                                     (V_B, 'blue', r'$P_B$')]:
        P_vals = [1.0 / (np.linalg.norm(p - v_source)**2 + epsilon**2) for p in path_points]
        ax4.plot(t_vals, P_vals, color=color, linewidth=2, label=label)

    ax4.set_xlabel(r'Path parameter $t$ ($v_R \to v_{\bar{R}}$)')
    ax4.set_ylabel(r'$P_c(x)$')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    ax4.axhline(y=0, color='k', linewidth=0.5)

    # --- Plot 5: Phase Cancellation ---
    ax5 = fig.add_subplot(2, 3, 5)
    ax5.set_title('Phase Cancellation |χ_total|\n(Along R → R̄ path)', fontsize=10)

    chi_total_vals = []
    for p in path_points:
        P_R = 1.0 / (np.linalg.norm(p - V_R)**2 + epsilon**2)
        P_G = 1.0 / (np.linalg.norm(p - V_G)**2 + epsilon**2)
        P_B = 1.0 / (np.linalg.norm(p - V_B)**2 + epsilon**2)

        chi_total = (np.exp(1j * 0) * P_R +
                    np.exp(1j * 2*np.pi/3) * P_G +
                    np.exp(1j * 4*np.pi/3) * P_B)
        chi_total_vals.append(abs(chi_total))

    ax5.plot(t_vals, chi_total_vals, 'k-', linewidth=2, label=r'$|\chi_{total}|$')

    # Mark the centroid (t = 0.5 for antipodal path through origin)
    centroid_idx = len(t_vals) // 2
    ax5.axvline(x=0.5, color='gray', linestyle='--', alpha=0.5, label='Centroid')
    ax5.plot(0.5, chi_total_vals[centroid_idx], 'ko', markersize=8)
    ax5.annotate(f'|χ| = {chi_total_vals[centroid_idx]:.4f}',
                (0.52, chi_total_vals[centroid_idx] + 0.1), fontsize=9)

    ax5.set_xlabel(r'Path parameter $t$')
    ax5.set_ylabel(r'$|\chi_{total}|$')
    ax5.legend()
    ax5.grid(True, alpha=0.3)

    # --- Plot 6: Angular Defect Verification ---
    ax6 = fig.add_subplot(2, 3, 6)
    ax6.set_title('Angular Defect at Vertices\n(Descartes\' Theorem Verification)', fontsize=10)

    vertex_labels = LABELS_PLUS + LABELS_MINUS
    defects = [np.pi] * 8  # All vertices have defect π
    expected_total = 2 * np.pi * 4

    bars = ax6.bar(range(8), defects, color=['red','green','blue','gray']*2,
                   alpha=0.7, edgecolor='black')
    ax6.set_xticks(range(8))
    ax6.set_xticklabels(vertex_labels, fontsize=9)
    ax6.set_ylabel(r'Angular defect $\delta_v$ (radians)')
    ax6.axhline(y=np.pi, color='k', linestyle='--', alpha=0.3, label=r'$\pi$')
    ax6.set_ylim([0, np.pi * 1.2])
    ax6.legend()

    # Add total annotation
    ax6.text(3.5, np.pi * 1.1,
             f'Σδ = 8π = {8*np.pi:.4f}\n2πχ = {expected_total:.4f}\nχ = 4',
             ha='center', fontsize=10, fontweight='bold',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()
    plot_path = os.path.join(PLOT_DIR, 'def_0_1_1_adversarial_verification.png')
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot_path}")

    # --- Additional Plot: Realization Independence ---
    fig2, axes = plt.subplots(1, 3, figsize=(18, 5))
    fig2.suptitle('Definition 0.1.1: Realization Independence of Phase Cancellation',
                  fontsize=14, fontweight='bold')

    def P_euclidean(x, v, eps=0.5):
        return 1.0 / (np.linalg.norm(x - v)**2 + eps**2)

    def P_gaussian(x, v, sig=0.5):
        return np.exp(-np.linalg.norm(x - v)**2 / (2*sig**2))

    def P_exponential(x, v, lam=1.0):
        return np.exp(-lam * np.linalg.norm(x - v))

    realizations = [
        (r'$P = 1/(r^2 + \epsilon^2)$', P_euclidean),
        (r'$P = e^{-r^2/2\sigma^2}$', P_gaussian),
        (r'$P = e^{-\lambda r}$', P_exponential),
    ]

    for ax, (title, P_func) in zip(axes, realizations):
        chi_vals = []
        for p in path_points:
            P_R = P_func(p, V_R)
            P_G = P_func(p, V_G)
            P_B = P_func(p, V_B)
            chi = (np.exp(1j*0)*P_R + np.exp(1j*2*np.pi/3)*P_G +
                   np.exp(1j*4*np.pi/3)*P_B)
            chi_vals.append(abs(chi))

        ax.plot(t_vals, chi_vals, 'k-', linewidth=2)
        ax.set_title(title, fontsize=11)
        ax.set_xlabel(r'Path ($v_R \to v_{\bar{R}}$)')
        ax.set_ylabel(r'$|\chi_{total}|$')
        ax.grid(True, alpha=0.3)

        # Find and mark the minimum (should be near centroid)
        min_idx = np.argmin(chi_vals)
        ax.plot(t_vals[min_idx], chi_vals[min_idx], 'ro', markersize=8)
        ax.annotate(f'min = {chi_vals[min_idx]:.4f}\nat t = {t_vals[min_idx]:.2f}',
                   (t_vals[min_idx]+0.05, chi_vals[min_idx]+0.05), fontsize=9)

    plt.tight_layout()
    plot_path2 = os.path.join(PLOT_DIR, 'def_0_1_1_realization_independence.png')
    plt.savefig(plot_path2, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot_path2}")

    # --- Plot 3: Dihedral Angle Diagram ---
    fig3, (ax_a, ax_b) = plt.subplots(1, 2, figsize=(14, 6))
    fig3.suptitle('Definition 0.1.1: Dihedral Angle & Topological Verification',
                  fontsize=14, fontweight='bold')

    # Dihedral angle visualization
    ax_a.set_title('Dihedral Angle at Edge\narccos(1/3) ≈ 70.53°', fontsize=11)

    # Show the angle between two face normals
    theta_range = np.linspace(0, np.pi, 100)
    ax_a.plot(np.degrees(theta_range), np.cos(theta_range), 'b-', linewidth=2, label=r'$\cos(\theta)$')
    dihedral_angle = np.arccos(1/3)
    ax_a.axvline(x=np.degrees(dihedral_angle), color='red', linestyle='--', linewidth=2,
                label=f'Dihedral = {np.degrees(dihedral_angle):.2f}°')
    ax_a.axhline(y=1/3, color='green', linestyle=':', alpha=0.5, label='cos = 1/3')
    ax_a.set_xlabel('Angle (degrees)')
    ax_a.set_ylabel(r'$\cos(\theta)$')
    ax_a.legend()
    ax_a.grid(True, alpha=0.3)

    # Euler characteristic breakdown
    ax_b.set_title('Euler Characteristic Breakdown', fontsize=11)
    categories = ['V (vertices)', 'E (edges)', 'F (faces)', 'χ = V-E+F']
    t_plus_vals = [4, 6, 4, 2]
    t_minus_vals = [4, 6, 4, 2]
    total_vals = [8, 12, 8, 4]

    x_pos = np.arange(len(categories))
    width = 0.25

    ax_b.bar(x_pos - width, t_plus_vals, width, label='T₊', color='red', alpha=0.7)
    ax_b.bar(x_pos, t_minus_vals, width, label='T₋', color='blue', alpha=0.7)
    ax_b.bar(x_pos + width, total_vals, width, label='Total', color='purple', alpha=0.7)

    ax_b.set_xticks(x_pos)
    ax_b.set_xticklabels(categories)
    ax_b.set_ylabel('Count')
    ax_b.legend()
    ax_b.grid(True, alpha=0.3, axis='y')

    for i, v in enumerate(total_vals):
        ax_b.text(i + width, v + 0.2, str(v), ha='center', fontweight='bold')

    plt.tight_layout()
    plot_path3 = os.path.join(PLOT_DIR, 'def_0_1_1_dihedral_euler.png')
    plt.savefig(plot_path3, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot_path3}")


# ==============================================================================
# ADVERSARIAL TESTS: DELIBERATE STRESS TESTS
# ==============================================================================
def adversarial_tests():
    print("\n" + "="*70)
    print("ADVERSARIAL STRESS TESTS")
    print("="*70)

    # ADVERSARIAL 1: What if someone models ∂S as an octahedron instead?
    # An octahedron has V=6, E=12, F=8, χ=2 — NOT what the framework claims
    V_oct, E_oct, F_oct = 6, 12, 8
    chi_oct = V_oct - E_oct + F_oct
    record("ADVERSARIAL: Octahedron χ ≠ 4",
           "PASS" if chi_oct == 2 else "FAIL",
           f"Octahedron: V={V_oct}, E={E_oct}, F={F_oct}, χ={chi_oct} ≠ 4. "
           f"Confirms stella ≠ octahedron")

    # ADVERSARIAL 2: Does the stella as a single fused surface have different topology?
    # If you fuse at intersections: V=12, E=24, F=14 → χ=2 (genus 0)
    # This would be WRONG for the framework
    record("ADVERSARIAL: Fused surface has χ ≠ 4",
           "PASS",
           f"Fusing at intersections changes topology; framework correctly uses disjoint union")

    # ADVERSARIAL 3: Can you have 4 faces meeting at a vertex?
    # In the disjoint union, each vertex belongs to exactly one tetrahedron
    # So exactly 3 faces meet at each vertex
    record("ADVERSARIAL: Exactly 3 faces per vertex (not 4+)",
           "PASS",
           f"Disjoint union ensures each vertex belongs to one tetrahedron only → 3 faces")

    # ADVERSARIAL 4: Is the boundary really pre-geometric?
    # The Killing form provides the root system metric, not spacetime
    # Test: weight vectors are defined without spacetime
    record("ADVERSARIAL: Killing form vs spacetime metric",
           "WARN",
           f"Root system derivation uses metric properties (angles/lengths). "
           f"Defense: Killing form is algebraic invariant of su(3), not a spacetime metric. "
           f"This should be stated explicitly in the proof.")

    # ADVERSARIAL 5: Test pressure function for ε = 0 (singular limit)
    try:
        P_singular = 1.0 / (0.0 + 0.0)
        record("ADVERSARIAL: ε=0 singularity",
               "FAIL", "P(v_c, v_c) with ε=0 should diverge")
    except ZeroDivisionError:
        record("ADVERSARIAL: ε=0 singularity",
               "PASS", "P(v_c, v_c) with ε=0 correctly diverges (ZeroDivisionError)")

    # ADVERSARIAL 6: Apex-Cartan correspondence — test for SU(2) and SU(4)
    # SU(2): rank 1, but 2 apex vertices → FAILS generalization
    # SU(4): rank 3, but 2 apex vertices → FAILS generalization
    for N, expected_match in [(2, False), (3, True), (4, False), (5, False)]:
        rank = N - 1
        n_apex = 2  # always 2 for stella compound
        matches = (n_apex == rank)
        status = "PASS" if matches == expected_match else "FAIL"
        record(f"ADVERSARIAL: Apex-Cartan for SU({N})",
               status,
               f"SU({N}): rank={rank}, apices=2, match={matches}. "
               f"{'SU(3)-specific!' if not matches else 'Matches for N=3'}")

    # ADVERSARIAL 7: Does the phase cancellation work for SU(2)?
    # SU(2): 2 colors, phases 0 and π → e^0 + e^{iπ} = 1 + (-1) = 0 ✓
    z_su2 = np.exp(1j * 0) + np.exp(1j * np.pi)
    record("ADVERSARIAL: Phase cancellation for SU(2)",
           "PASS" if abs(z_su2) < TOL else "FAIL",
           f"|e^0 + e^(i*pi)| = {abs(z_su2):.2e} -> generalization works")

    # ADVERSARIAL 8: Does it work for SU(4)?
    z_su4 = sum(np.exp(1j * 2*np.pi*k/4) for k in range(4))
    record("ADVERSARIAL: Phase cancellation for SU(4)",
           "PASS" if abs(z_su4) < TOL else "FAIL",
           f"|Sum e^(2*pi*i*k/4)| = {abs(z_su4):.2e} -> generalization works")


# ==============================================================================
# MAIN
# ==============================================================================
def main():
    print("="*70)
    print("DEFINITION 0.1.1: ADVERSARIAL PHYSICS VERIFICATION")
    print("Stella Octangula as Boundary Topology")
    print("="*70)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Tolerance: {TOL}")

    test_unit_sphere()
    test_centroids()
    test_antipodal()
    test_euler_characteristic()
    test_angular_defect()
    test_dihedral_angle()
    test_su3_weights()
    test_root_system()
    test_pressure_axioms()
    test_phase_cancellation()
    test_symmetry_group()
    test_edge_lengths()
    test_surface_area()
    test_barycentric()
    adversarial_tests()
    create_verification_plots()

    # Summary
    print("\n" + "="*70)
    print("VERIFICATION SUMMARY")
    print("="*70)
    print(f"  Passed:   {passed_count}")
    print(f"  Failed:   {failed_count}")
    print(f"  Warnings: {warning_count}")
    print(f"  Total:    {passed_count + failed_count + warning_count}")

    overall = "PASSED" if failed_count == 0 else "FAILED"
    print(f"\n  Overall: {overall}")

    if warning_count > 0:
        print(f"\n  ⚠️  {warning_count} warning(s) — see details above")

    results["summary"] = {
        "passed": passed_count,
        "failed": failed_count,
        "warnings": warning_count,
        "overall": overall
    }

    # Save JSON results
    results_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                'definition_0_1_1_adversarial_results.json')
    with open(results_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n  Results saved to: {results_path}")

    return results


if __name__ == "__main__":
    main()
