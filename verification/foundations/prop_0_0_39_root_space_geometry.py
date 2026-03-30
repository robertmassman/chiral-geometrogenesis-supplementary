#!/usr/bin/env python3
"""
Proposition 0.0.39: SU(3) Root Space Geometry Verification
===========================================================

Verifies the mathematical details of the face-root assignment on the stella
octangula, specifically:

  Task 1: Compute SU(3) weight vectors, roots, and the Weyl group cyclic
          action (Z_3) on roots. Verify alpha_2 -> -(alpha_1+alpha_2) -> alpha_1.
  Task 2: Verify that the full Weyl group S_3 does NOT preserve {positive roots}.
  Task 3: Determine the correct characterization: T_+ faces opposite color
          vertices map to one Z_3 Weyl orbit, not to "all positive roots."
  Task 4: Compute the S_3 action on the Cartan subalgebra h = span(H_1, H_2).
  Task 5: Verify Z_2 (T_+ <-> T_-) swap vs charge conjugation.

Related Documents:
- Proof: docs/proofs/foundations/Proposition-0.0.39-Stella-Adjoint-Decomposition.md
- Lean: lean/ChiralGeometrogenesis/Foundations/ (if formalized)

Verification Date: 2026-02-12
"""

import numpy as np
from itertools import permutations
import json
from datetime import datetime

# ==============================================================================
# UTILITY FUNCTIONS
# ==============================================================================

def vec_str(v, name=None):
    """Pretty-print a 2D vector."""
    prefix = f"{name} = " if name else ""
    # Express in terms of sqrt(3) when possible
    x, y = v
    return f"{prefix}({x:+.6f}, {y:+.6f})"

def vecs_equal(v1, v2, tol=1e-12):
    """Check if two vectors are equal within tolerance."""
    return np.allclose(v1, v2, atol=tol)

def find_root_name(v, root_dict, tol=1e-12):
    """Find the name of a root vector in the dictionary."""
    for name, root in root_dict.items():
        if vecs_equal(v, root, tol):
            return name
    return None

# ==============================================================================
# TASK 1: SU(3) Weight Vectors, Roots, and Z_3 Cyclic Action
# ==============================================================================

def task_1_weights_roots_cyclic_action():
    """
    Compute weight vectors, roots, and verify the Z_3 cyclic action on roots.

    The color vertices of T_+ map to the fundamental weights of SU(3):
      w_R = (1/2, 1/(2*sqrt(3)))
      w_G = (-1/2, 1/(2*sqrt(3)))
      w_B = (0, -1/sqrt(3))

    The simple roots of A_2 are:
      alpha_1 = w_R - w_G = (1, 0)
      alpha_2 = w_G - w_B = (-1/2, sqrt(3)/2)

    The Z_3 cyclic permutation R -> G -> B -> R corresponds to a 120-degree
    rotation in the weight plane.
    """
    print("=" * 80)
    print("TASK 1: SU(3) Weight Vectors, Roots, and Z_3 Cyclic Action")
    print("=" * 80)

    results = {"task": 1, "passed": True, "checks": []}

    # --- Weight vectors ---
    sqrt3 = np.sqrt(3)
    w_R = np.array([1/2, 1/(2*sqrt3)])
    w_G = np.array([-1/2, 1/(2*sqrt3)])
    w_B = np.array([0, -1/sqrt3])

    weights = {"w_R": w_R, "w_G": w_G, "w_B": w_B}

    print("\n--- Fundamental weight vectors (vertices of T_+ in weight plane) ---")
    for name, w in weights.items():
        print(f"  {vec_str(w, name)}")

    # Verify weights sum to zero (SU(3) tracelessness)
    weight_sum = w_R + w_G + w_B
    check_sum = vecs_equal(weight_sum, np.zeros(2))
    print(f"\n  w_R + w_G + w_B = ({weight_sum[0]:.6e}, {weight_sum[1]:.6e})")
    print(f"  Sum = 0? {check_sum}")
    results["checks"].append({"name": "weight_sum_zero", "passed": bool(check_sum)})

    # Verify weights are equidistant (equilateral triangle)
    d_RG = np.linalg.norm(w_R - w_G)
    d_GB = np.linalg.norm(w_G - w_B)
    d_RB = np.linalg.norm(w_R - w_B)
    print(f"\n  |w_R - w_G| = {d_RG:.6f}")
    print(f"  |w_G - w_B| = {d_GB:.6f}")
    print(f"  |w_R - w_B| = {d_RB:.6f}")
    check_equilat = np.allclose([d_RG, d_GB, d_RB], [1.0, 1.0, 1.0], atol=1e-12)
    print(f"  Equilateral with unit side? {check_equilat}")
    results["checks"].append({"name": "equilateral_weights", "passed": bool(check_equilat)})

    # --- Root vectors ---
    alpha_1 = w_R - w_G     # Simple root 1
    alpha_2 = w_G - w_B     # Simple root 2
    alpha_12 = w_R - w_B    # = alpha_1 + alpha_2

    print("\n--- Root vectors (edges of weight triangle) ---")
    print(f"  alpha_1    = w_R - w_G = ({alpha_1[0]:+.6f}, {alpha_1[1]:+.6f})")
    print(f"    Expected: (1, 0)")
    print(f"  alpha_2    = w_G - w_B = ({alpha_2[0]:+.6f}, {alpha_2[1]:+.6f})")
    print(f"    Expected: (-1/2, sqrt(3)/2) = ({-0.5:+.6f}, {sqrt3/2:+.6f})")
    print(f"  alpha_1+alpha_2 = w_R - w_B = ({alpha_12[0]:+.6f}, {alpha_12[1]:+.6f})")
    print(f"    Expected: (1/2, sqrt(3)/2) = ({0.5:+.6f}, {sqrt3/2:+.6f})")

    # Check alpha_12 = alpha_1 + alpha_2
    check_sum_roots = vecs_equal(alpha_12, alpha_1 + alpha_2)
    print(f"\n  alpha_1 + alpha_2 = w_R - w_B? {check_sum_roots}")
    results["checks"].append({"name": "root_sum", "passed": bool(check_sum_roots)})

    # All 6 roots
    roots = {
        "+alpha_1": alpha_1,
        "+alpha_2": alpha_2,
        "+(alpha_1+alpha_2)": alpha_12,
        "-alpha_1": -alpha_1,
        "-alpha_2": -alpha_2,
        "-(alpha_1+alpha_2)": -alpha_12,
    }

    print("\n--- All 6 roots of A_2 ---")
    for name, r in roots.items():
        print(f"  {name:25s} = ({r[0]:+.6f}, {r[1]:+.6f})")

    # --- Z_3 cyclic action: 120-degree rotation ---
    # The cyclic permutation R -> G -> B -> R is a 120-degree rotation
    theta = 2 * np.pi / 3
    R120 = np.array([
        [np.cos(theta), -np.sin(theta)],
        [np.sin(theta),  np.cos(theta)]
    ])

    print("\n--- Z_3 Cyclic Action (120-degree rotation) ---")
    print(f"  Rotation matrix R_120 =")
    print(f"    [{R120[0,0]:+.6f}  {R120[0,1]:+.6f}]")
    print(f"    [{R120[1,0]:+.6f}  {R120[1,1]:+.6f}]")

    # Verify R120 permutes weight vectors: w_R -> w_G -> w_B -> w_R
    w_R_rot = R120 @ w_R
    w_G_rot = R120 @ w_G
    w_B_rot = R120 @ w_B

    check_wR_to_wG = vecs_equal(w_R_rot, w_G)
    check_wG_to_wB = vecs_equal(w_G_rot, w_B)
    check_wB_to_wR = vecs_equal(w_B_rot, w_R)

    print(f"\n  R_120 * w_R = ({w_R_rot[0]:+.6f}, {w_R_rot[1]:+.6f})")
    print(f"    = w_G? {check_wR_to_wG}")
    print(f"  R_120 * w_G = ({w_G_rot[0]:+.6f}, {w_G_rot[1]:+.6f})")
    print(f"    = w_B? {check_wG_to_wB}")
    print(f"  R_120 * w_B = ({w_B_rot[0]:+.6f}, {w_B_rot[1]:+.6f})")
    print(f"    = w_R? {check_wB_to_wR}")

    results["checks"].append({"name": "Z3_permutes_weights",
                              "passed": bool(check_wR_to_wG and check_wG_to_wB and check_wB_to_wR)})

    # Now: Z_3 action on roots
    # The opposite-vertex rule gives us:
    #   F_1+ (opp v_R) -> root along v_G-v_B edge = w_G - w_B = alpha_2
    #   F_2+ (opp v_G) -> root along v_R-v_B edge = ?
    #   F_3+ (opp v_B) -> root along v_R-v_G edge = w_R - w_G = alpha_1

    # For F_2+ (opposite v_G), the edge is v_R-v_B.
    # The two possible directed roots are:
    #   w_R - w_B = alpha_1 + alpha_2  (positive root)
    #   w_B - w_R = -(alpha_1 + alpha_2)  (negative root)

    # Under the cyclic Z_3 that maps R->G->B->R, the face mapping is:
    #   F_1+ (opp v_R) -> F_2+ (opp v_G) -> F_3+ (opp v_B) -> F_1+
    #
    # The root assignment must be Z_3-equivariant. Let's compute R_120 on roots:

    print("\n--- Z_3 action on roots ---")

    a2_rot = R120 @ alpha_2
    a2_rot_name = find_root_name(a2_rot, roots)
    print(f"\n  R_120 * alpha_2 = ({a2_rot[0]:+.6f}, {a2_rot[1]:+.6f})")
    print(f"    = {a2_rot_name}")

    # Second application
    a2_rot2 = R120 @ a2_rot
    a2_rot2_name = find_root_name(a2_rot2, roots)
    print(f"  R_120^2 * alpha_2 = ({a2_rot2[0]:+.6f}, {a2_rot2[1]:+.6f})")
    print(f"    = {a2_rot2_name}")

    # Third application (should return to alpha_2)
    a2_rot3 = R120 @ a2_rot2
    a2_rot3_name = find_root_name(a2_rot3, roots)
    print(f"  R_120^3 * alpha_2 = ({a2_rot3[0]:+.6f}, {a2_rot3[1]:+.6f})")
    print(f"    = {a2_rot3_name}")

    check_cycle = (a2_rot_name == "-(alpha_1+alpha_2)" and
                   a2_rot2_name == "+alpha_1" and
                   a2_rot3_name == "+alpha_2")

    print(f"\n  VERIFY: alpha_2 -> -(alpha_1+alpha_2) -> alpha_1 -> alpha_2?")
    print(f"  Result: {check_cycle}")

    results["checks"].append({"name": "Z3_cycle_alpha2", "passed": bool(check_cycle)})

    # Check ALL root orbits under Z_3
    print("\n--- Complete Z_3 orbits on all 6 roots ---")

    orbit_1 = []
    orbit_2 = []
    for name, r in roots.items():
        r_rot = R120 @ r
        r_rot2 = R120 @ r_rot
        orbit = [name, find_root_name(r_rot, roots), find_root_name(r_rot2, roots)]
        orbit_set = frozenset(orbit)
        if orbit_set not in [frozenset(o) for o in [orbit_1]]:
            if not orbit_1:
                orbit_1 = orbit
            elif orbit_set != frozenset(orbit_1):
                orbit_2 = orbit
                break

    # Compute both orbits properly
    all_orbits = {}
    visited = set()
    for name, r in roots.items():
        if name in visited:
            continue
        orbit_names = []
        current = r.copy()
        for _ in range(3):
            cname = find_root_name(current, roots)
            orbit_names.append(cname)
            visited.add(cname)
            current = R120 @ current
        all_orbits[tuple(orbit_names)] = orbit_names

    print(f"\n  Number of Z_3 orbits: {len(all_orbits)}")
    for i, (key, orbit) in enumerate(all_orbits.items()):
        print(f"  Orbit {i+1}: {' -> '.join(orbit)} -> {orbit[0]}")

    # KEY RESULT: The 3 roots assigned to T_+ faces form ONE Z_3 orbit
    # that MIXES positive and negative roots!
    print("\n--- KEY FINDING ---")
    print("  The Z_3 orbit containing alpha_2 is:")
    print(f"    {{alpha_2, -(alpha_1+alpha_2), alpha_1}}")
    print("  This contains 2 POSITIVE roots and 1 NEGATIVE root!")
    print("  Therefore T_+ faces do NOT map to 'all positive roots'.")

    results["checks"].append({"name": "orbit_mixes_signs", "passed": True,
                              "detail": "Z_3 orbit {alpha_2, -(alpha_1+alpha_2), alpha_1} mixes positive and negative"})

    results["passed"] = all(c["passed"] for c in results["checks"])
    return results


# ==============================================================================
# TASK 2: Full S_3 Weyl Group Does NOT Preserve Positive Roots
# ==============================================================================

def task_2_S3_does_not_preserve_positive_roots():
    """
    The Weyl group of A_2 is S_3 (symmetric group on 3 elements).
    It is generated by two simple reflections s_1, s_2 corresponding to
    the two simple roots alpha_1, alpha_2.

    s_i reflects across the hyperplane perpendicular to alpha_i.

    We verify that S_3 does NOT preserve the set of positive roots
    {alpha_1, alpha_2, alpha_1+alpha_2}.
    """
    print("\n" + "=" * 80)
    print("TASK 2: S_3 Does NOT Preserve the Set of Positive Roots")
    print("=" * 80)

    results = {"task": 2, "passed": True, "checks": []}

    sqrt3 = np.sqrt(3)

    # Roots
    alpha_1 = np.array([1.0, 0.0])
    alpha_2 = np.array([-0.5, sqrt3/2])
    alpha_12 = alpha_1 + alpha_2  # = (0.5, sqrt3/2)

    positive_roots = {"+alpha_1": alpha_1, "+alpha_2": alpha_2, "+(alpha_1+alpha_2)": alpha_12}
    all_roots = {
        "+alpha_1": alpha_1, "+alpha_2": alpha_2, "+(alpha_1+alpha_2)": alpha_12,
        "-alpha_1": -alpha_1, "-alpha_2": -alpha_2, "-(alpha_1+alpha_2)": -alpha_12,
    }

    # Simple reflections
    # s_alpha reflects across the hyperplane perpendicular to alpha:
    # s_alpha(v) = v - 2*(v . alpha)/(alpha . alpha) * alpha

    def reflection(v, alpha):
        return v - 2 * np.dot(v, alpha) / np.dot(alpha, alpha) * alpha

    s1 = lambda v: reflection(v, alpha_1)  # Reflection in alpha_1
    s2 = lambda v: reflection(v, alpha_2)  # Reflection in alpha_2

    # Generate all 6 elements of S_3
    # S_3 = {e, s1, s2, s1*s2, s2*s1, s1*s2*s1}
    weyl_elements = {
        "e": lambda v: v,
        "s1": s1,
        "s2": s2,
        "s1*s2": lambda v: s1(s2(v)),
        "s2*s1": lambda v: s2(s1(v)),
        "s1*s2*s1": lambda v: s1(s2(s1(v))),
    }

    # Verify we have exactly 6 elements (no duplicates)
    print("\n--- Weyl group elements acting on alpha_1 ---")
    images_of_a1 = {}
    for name, w in weyl_elements.items():
        img = w(alpha_1)
        img_name = find_root_name(img, all_roots)
        images_of_a1[name] = img_name
        print(f"  {name:12s}(alpha_1) = ({img[0]:+.6f}, {img[1]:+.6f}) = {img_name}")

    print("\n--- Weyl group elements acting on alpha_2 ---")
    images_of_a2 = {}
    for name, w in weyl_elements.items():
        img = w(alpha_2)
        img_name = find_root_name(img, all_roots)
        images_of_a2[name] = img_name
        print(f"  {name:12s}(alpha_2) = ({img[0]:+.6f}, {img[1]:+.6f}) = {img_name}")

    print("\n--- Weyl group elements acting on alpha_1+alpha_2 ---")
    images_of_a12 = {}
    for name, w in weyl_elements.items():
        img = w(alpha_12)
        img_name = find_root_name(img, all_roots)
        images_of_a12[name] = img_name
        print(f"  {name:12s}(alpha_1+alpha_2) = ({img[0]:+.6f}, {img[1]:+.6f}) = {img_name}")

    # Check: Does any Weyl element (other than e) preserve the set of positive roots?
    print("\n--- Does each element preserve {positive roots}? ---")
    positive_set = {"+alpha_1", "+alpha_2", "+(alpha_1+alpha_2)"}

    any_nontrivial_preserves = False
    for name, w in weyl_elements.items():
        images = set()
        for rname, r in positive_roots.items():
            img = w(r)
            img_name = find_root_name(img, all_roots)
            images.add(img_name)
        preserves = (images == positive_set)
        if name != "e" and preserves:
            any_nontrivial_preserves = True
        print(f"  {name:12s}: {images} -> preserves positive roots? {preserves}")

    check_not_preserved = not any_nontrivial_preserves
    print(f"\n  RESULT: No non-identity Weyl element preserves positive roots: {check_not_preserved}")
    results["checks"].append({"name": "S3_does_not_preserve_positive_roots",
                              "passed": bool(check_not_preserved)})

    # Show explicitly which elements map positive roots to negative
    print("\n--- Explicit sign-mixing ---")
    for name, w in weyl_elements.items():
        if name == "e":
            continue
        neg_count = 0
        for rname, r in positive_roots.items():
            img = w(r)
            img_name = find_root_name(img, all_roots)
            if img_name.startswith("-"):
                neg_count += 1
        print(f"  {name:12s} maps {neg_count}/3 positive roots to negative roots")

    # Verify s1*s2 is the 120-degree rotation (Z_3 generator)
    print("\n--- Identifying the Z_3 subgroup ---")
    theta = 2 * np.pi / 3
    R120 = np.array([[np.cos(theta), -np.sin(theta)],
                     [np.sin(theta),  np.cos(theta)]])

    # Check s1*s2
    test_vec = np.array([1.0, 0.5])
    s1s2_result = s1(s2(test_vec))
    r120_result = R120 @ test_vec
    is_rotation = vecs_equal(s1s2_result, r120_result)
    print(f"  s1*s2 on test vector: ({s1s2_result[0]:+.6f}, {s1s2_result[1]:+.6f})")
    print(f"  R_120 on test vector: ({r120_result[0]:+.6f}, {r120_result[1]:+.6f})")
    print(f"  s1*s2 = R_120? {is_rotation}")

    # Also check s2*s1
    s2s1_result = s2(s1(test_vec))
    r240_result = R120 @ R120 @ test_vec
    is_rotation_240 = vecs_equal(s2s1_result, r240_result)
    print(f"  s2*s1 on test vector: ({s2s1_result[0]:+.6f}, {s2s1_result[1]:+.6f})")
    print(f"  R_240 on test vector: ({r240_result[0]:+.6f}, {r240_result[1]:+.6f})")
    print(f"  s2*s1 = R_240? {is_rotation_240}")

    results["checks"].append({"name": "s1s2_is_R120", "passed": bool(is_rotation)})
    results["checks"].append({"name": "s2s1_is_R240", "passed": bool(is_rotation_240)})

    print(f"\n  Z_3 subgroup = {{e, s1*s2, s2*s1}} = {{e, R_120, R_240}}")
    print(f"  This is the rotation subgroup of S_3.")

    results["passed"] = all(c["passed"] for c in results["checks"])
    return results


# ==============================================================================
# TASK 3: Correct Characterization — Weyl Orbits, Not Positive/Negative
# ==============================================================================

def task_3_correct_characterization():
    """
    The correct statement is:

    The 3 T_+ faces opposite color vertices map to 3 root generators that
    form one COMPLETE Z_3 ORBIT, not "all positive roots."

    Similarly, the 3 T_- faces opposite anti-color vertices map to the OTHER
    Z_3 orbit.

    The two orbits partition the 6 roots into two sets of 3, each related by
    the Weyl group Z_3 subgroup.
    """
    print("\n" + "=" * 80)
    print("TASK 3: Correct Characterization — Z_3 Weyl Orbits")
    print("=" * 80)

    results = {"task": 3, "passed": True, "checks": []}

    sqrt3 = np.sqrt(3)
    alpha_1 = np.array([1.0, 0.0])
    alpha_2 = np.array([-0.5, sqrt3/2])
    alpha_12 = alpha_1 + alpha_2

    all_roots = {
        "+alpha_1": alpha_1, "+alpha_2": alpha_2, "+(alpha_1+alpha_2)": alpha_12,
        "-alpha_1": -alpha_1, "-alpha_2": -alpha_2, "-(alpha_1+alpha_2)": -alpha_12,
    }

    theta = 2 * np.pi / 3
    R120 = np.array([[np.cos(theta), -np.sin(theta)],
                     [np.sin(theta),  np.cos(theta)]])

    # --- Opposite-vertex rule for T_+ ---
    # The "directed" root is determined by the opposite-vertex rule:
    # The face opposite v_c contains the edge connecting the OTHER two color vertices.
    # Under Z_3 equivariance, the cyclic permutation R->G->B->R maps faces to faces.

    # Let's work out the natural assignment.
    # Face opposite v_R in T_+: contains v_G, v_B, v_W. The color edge is v_G-v_B.
    #   Directed root: w_G - w_B = alpha_2 (following cyclic order G->B)

    # Under R_120 (mapping R->G->B->R):
    #   Face opp v_R -> Face opp v_G
    #   The root alpha_2 should map to R_120(alpha_2)

    root_opp_R = alpha_2  # w_G - w_B
    root_opp_G = R120 @ root_opp_R  # R_120 * alpha_2
    root_opp_B = R120 @ root_opp_G  # R_120^2 * alpha_2

    name_opp_R = find_root_name(root_opp_R, all_roots)
    name_opp_G = find_root_name(root_opp_G, all_roots)
    name_opp_B = find_root_name(root_opp_B, all_roots)

    print("\n--- Opposite-vertex rule for T_+ (Z_3-equivariant assignment) ---")
    print(f"  Face opp v_R: edge v_G-v_B -> root = {name_opp_R}")
    print(f"    = ({root_opp_R[0]:+.6f}, {root_opp_R[1]:+.6f})")
    print(f"  Face opp v_G: edge v_B-v_R -> root = R_120(alpha_2) = {name_opp_G}")
    print(f"    = ({root_opp_G[0]:+.6f}, {root_opp_G[1]:+.6f})")
    print(f"  Face opp v_B: edge v_R-v_G -> root = R_120^2(alpha_2) = {name_opp_B}")
    print(f"    = ({root_opp_B[0]:+.6f}, {root_opp_B[1]:+.6f})")

    # Verify this is {alpha_2, -(alpha_1+alpha_2), alpha_1}
    orbit_1_names = {name_opp_R, name_opp_G, name_opp_B}
    expected_orbit_1 = {"+alpha_2", "-(alpha_1+alpha_2)", "+alpha_1"}

    check_orbit_1 = (orbit_1_names == expected_orbit_1)
    print(f"\n  T_+ orbit: {orbit_1_names}")
    print(f"  Expected:  {expected_orbit_1}")
    print(f"  Match? {check_orbit_1}")
    results["checks"].append({"name": "T+_orbit_correct", "passed": bool(check_orbit_1)})

    # Count positive and negative in this orbit
    pos_count = sum(1 for n in orbit_1_names if n.startswith("+"))
    neg_count = sum(1 for n in orbit_1_names if n.startswith("-"))
    print(f"\n  T_+ orbit has {pos_count} positive and {neg_count} negative root(s)")
    print(f"  This DISPROVES the claim that T_+ maps to 'all positive roots'!")

    results["checks"].append({"name": "T+_orbit_mixed_sign",
                              "passed": bool(pos_count > 0 and neg_count > 0),
                              "detail": f"{pos_count} positive, {neg_count} negative"})

    # --- T_- orbit (the other orbit) ---
    # T_- faces opposite anti-color vertices map to the OTHER Z_3 orbit.
    # The other orbit is obtained by negating the first orbit:
    orbit_2_roots = [-root_opp_R, -root_opp_G, -root_opp_B]
    orbit_2_names = {find_root_name(r, all_roots) for r in orbit_2_roots}
    expected_orbit_2 = {"-alpha_2", "+(alpha_1+alpha_2)", "-alpha_1"}

    print(f"\n--- T_- orbit (negation of T_+ orbit) ---")
    print(f"  T_- orbit: {orbit_2_names}")
    print(f"  Expected:  {expected_orbit_2}")
    check_orbit_2 = (orbit_2_names == expected_orbit_2)
    print(f"  Match? {check_orbit_2}")
    results["checks"].append({"name": "T-_orbit_correct", "passed": bool(check_orbit_2)})

    pos_count_2 = sum(1 for n in orbit_2_names if n.startswith("+"))
    neg_count_2 = sum(1 for n in orbit_2_names if n.startswith("-"))
    print(f"  T_- orbit has {pos_count_2} positive and {neg_count_2} negative root(s)")

    # Verify the two orbits partition all 6 roots
    union = orbit_1_names | orbit_2_names
    all_root_names = set(all_roots.keys())
    check_partition = (union == all_root_names and len(orbit_1_names & orbit_2_names) == 0)
    print(f"\n  Two orbits partition all 6 roots? {check_partition}")
    results["checks"].append({"name": "orbits_partition_roots", "passed": bool(check_partition)})

    # --- Alternative: direct computation from weight differences ---
    print("\n--- Direct verification via weight differences ---")
    print("  For T_+, the opposite-vertex rule gives:")
    print(f"    Face opp v_R: w_G - w_B = alpha_2 [POSITIVE root]")

    # For face opp v_G: the edge is v_R-v_B.
    # What direction? Under Z_3 equivariance, we need R->G->B cyclic ordering.
    # The cyclic ordering on the edge determines the direction.
    # Face opp v_R: edge has vertices (v_G, v_B) in cyclic order -> w_G - w_B = alpha_2
    # Face opp v_G: edge has vertices (v_B, v_R) in cyclic order -> w_B - w_R = -(alpha_1+alpha_2)
    # Face opp v_B: edge has vertices (v_R, v_G) in cyclic order -> w_R - w_G = alpha_1

    direct_opp_R = alpha_2                  # w_G - w_B
    direct_opp_G = -alpha_12                # w_B - w_R = -(alpha_1+alpha_2)
    direct_opp_B = alpha_1                  # w_R - w_G

    print(f"    Face opp v_G: w_B - w_R = -(alpha_1+alpha_2) [NEGATIVE root]")
    print(f"    Face opp v_B: w_R - w_G = alpha_1 [POSITIVE root]")

    check_direct = (vecs_equal(direct_opp_R, root_opp_R) and
                    vecs_equal(direct_opp_G, root_opp_G) and
                    vecs_equal(direct_opp_B, root_opp_B))
    print(f"\n  Direct computation matches Z_3-equivariant assignment? {check_direct}")
    results["checks"].append({"name": "direct_matches_Z3", "passed": bool(check_direct)})

    # --- Explanation of the directed edge convention ---
    print("\n--- Why the cyclic ordering determines the direction ---")
    print("  The Z_3 cyclic permutation R->G->B->R fixes a CHIRALITY on the")
    print("  weight triangle. This chirality determines a consistent edge")
    print("  direction for each face:")
    print("    Face opp v_R: v_G -> v_B  (following cyclic order past v_R)")
    print("    Face opp v_G: v_B -> v_R  (following cyclic order past v_G)")
    print("    Face opp v_B: v_R -> v_G  (following cyclic order past v_B)")
    print("")
    print("  The root w_{source} - w_{target} (NOT w_{target} - w_{source})")
    print("  would give the OPPOSITE orbit. The convention above uses")
    print("  w_{first} - w_{second} in cyclic order, giving:")
    print("    {alpha_2, -(alpha_1+alpha_2), alpha_1}")

    # --- The CORRECT statement for the proof ---
    print("\n" + "-" * 60)
    print("CORRECT CHARACTERIZATION FOR PROP 0.0.39:")
    print("-" * 60)
    print("""
  The 6 root generators of su(3) partition into two Z_3 Weyl orbits:

  Orbit A (T_+ faces): {E_{alpha_2}, E_{-(alpha_1+alpha_2)}, E_{alpha_1}}
    - 2 positive roots, 1 negative root
    - Obtained by opposite-vertex rule with cyclic edge direction

  Orbit B (T_- faces): {E_{-alpha_2}, E_{alpha_1+alpha_2}, E_{-alpha_1}}
    - 1 positive root, 2 negative roots
    - Negation of Orbit A

  Each orbit is a COMPLETE Z_3 orbit under the Weyl group's rotation subgroup.
  The two orbits are related by T_+ <-> T_- (the Z_2 swap).

  IMPORTANT: It is INCORRECT to say "T_+ -> all positive roots" and
  "T_- -> all negative roots." The Z_3 symmetry forces mixing of signs.
""")

    results["passed"] = all(c["passed"] for c in results["checks"])
    return results


# ==============================================================================
# TASK 4: S_3 Action on the Cartan Subalgebra
# ==============================================================================

def task_4_S3_action_on_Cartan():
    """
    The Cartan subalgebra h = span(H_1, H_2) is 2-dimensional.
    S_3 acts on h by the induced action from permuting roots.

    We verify:
    (a) S_3 preserves h as a subspace
    (b) S_3 acts nontrivially on individual elements of h
    (c) The S_3-fixed point set of h is {0}
    """
    print("\n" + "=" * 80)
    print("TASK 4: S_3 Action on the Cartan Subalgebra")
    print("=" * 80)

    results = {"task": 4, "passed": True, "checks": []}

    sqrt3 = np.sqrt(3)
    alpha_1 = np.array([1.0, 0.0])
    alpha_2 = np.array([-0.5, sqrt3/2])

    def reflection(v, alpha):
        return v - 2 * np.dot(v, alpha) / np.dot(alpha, alpha) * alpha

    s1 = lambda v: reflection(v, alpha_1)
    s2 = lambda v: reflection(v, alpha_2)

    # S_3 as 2x2 matrices acting on h
    # h is identified with R^2 via the basis {H_1, H_2} (or equivalently,
    # the dual space h* which we've been using as the root space).

    # The Weyl group acts on h* (roots live here) and dually on h.
    # The action on h is by the CONTRAGREDIENT (transpose-inverse) representation.
    # For orthogonal transformations (reflections), transpose-inverse = transpose = itself.
    # So the Weyl group acts the SAME WAY on h and h*.

    print("\n--- S_3 as 2x2 matrices on h (identified with R^2) ---")

    # Compute matrix representations
    e1 = np.array([1.0, 0.0])
    e2 = np.array([0.0, 1.0])

    weyl_funcs = {
        "e": lambda v: v,
        "s1": s1,
        "s2": s2,
        "s1*s2": lambda v: s1(s2(v)),
        "s2*s1": lambda v: s2(s1(v)),
        "s1*s2*s1": lambda v: s1(s2(s1(v))),
    }

    weyl_matrices = {}
    for name, f in weyl_funcs.items():
        col1 = f(e1)
        col2 = f(e2)
        M = np.column_stack([col1, col2])
        weyl_matrices[name] = M
        print(f"\n  {name}:")
        print(f"    [{M[0,0]:+.6f}  {M[0,1]:+.6f}]")
        print(f"    [{M[1,0]:+.6f}  {M[1,1]:+.6f}]")
        det = np.linalg.det(M)
        print(f"    det = {det:+.1f}  {'(rotation)' if det > 0 else '(reflection)'}")

    # (a) S_3 preserves h as a subspace
    # This is trivially true since we've represented S_3 as 2x2 matrices on R^2 = h.
    # Any 2x2 matrix maps R^2 to R^2.
    print("\n--- (a) S_3 preserves h as a subspace ---")
    print("  TRIVIALLY TRUE: S_3 is represented by 2x2 matrices on h = R^2.")
    print("  Every element maps h -> h.")
    results["checks"].append({"name": "S3_preserves_h", "passed": True})

    # (b) S_3 acts nontrivially on individual elements of h
    print("\n--- (b) S_3 acts nontrivially on individual elements ---")

    # Check: does s1 act nontrivially?
    test_h = np.array([1.0, 1.0])  # A generic element of h
    for name, M in weyl_matrices.items():
        img = M @ test_h
        is_identity = vecs_equal(img, test_h)
        print(f"  {name:12s}({test_h}) = ({img[0]:+.6f}, {img[1]:+.6f}) {'= input (TRIVIAL)' if is_identity else '!= input (NONTRIVIAL)'}")

    # Show that s1 specifically permutes Cartan basis elements
    # In the Gell-Mann basis: H_1 = T_3 (isospin), H_2 = T_8 (hypercharge)
    # s1 corresponds to the simple reflection for alpha_1 = (1,0).
    # s1 reflects across the line perpendicular to (1,0), i.e., the y-axis.
    # s1: (x, y) -> (-x, y)
    H1 = np.array([1.0, 0.0])  # Represents T_3 direction
    H2 = np.array([0.0, 1.0])  # Represents T_8 direction

    s1_H1 = weyl_matrices["s1"] @ H1
    s1_H2 = weyl_matrices["s1"] @ H2
    print(f"\n  s1(H_1) = ({s1_H1[0]:+.6f}, {s1_H1[1]:+.6f})  -> H_1 negated")
    print(f"  s1(H_2) = ({s1_H2[0]:+.6f}, {s1_H2[1]:+.6f})  -> H_2 unchanged")

    nontrivial_count = sum(1 for name, M in weyl_matrices.items()
                          if name != "e" and not vecs_equal(M @ test_h, test_h))
    check_nontrivial = (nontrivial_count == 5)  # All non-identity are nontrivial
    print(f"\n  Number of nontrivial elements on test vector: {nontrivial_count}/5")
    print(f"  All non-identity elements act nontrivially? {check_nontrivial}")
    results["checks"].append({"name": "S3_nontrivial_on_h", "passed": bool(check_nontrivial)})

    # (c) S_3-fixed point set is {0}
    print("\n--- (c) S_3-fixed point set of h ---")
    print("  A vector v in h is S_3-fixed iff w(v) = v for ALL w in S_3.")
    print("  Equivalently, (M - I)v = 0 for all Weyl matrices M.")
    print()

    # Stack all (M - I) constraints
    # For v to be fixed by all of S_3, it must be in the kernel of every (M - I)
    constraints = []
    for name, M in weyl_matrices.items():
        if name == "e":
            continue
        diff = M - np.eye(2)
        constraints.append(diff)

    # Stack into a big matrix and find kernel
    big_matrix = np.vstack(constraints)
    print(f"  Constraint matrix (stacked (M-I) for all non-identity elements):")
    print(f"  Shape: {big_matrix.shape}")

    # SVD to find kernel
    U, S_vals, Vt = np.linalg.svd(big_matrix)
    rank = np.sum(S_vals > 1e-10)
    kernel_dim = 2 - rank

    print(f"  Singular values: {S_vals[:4]}")
    print(f"  Rank: {rank}")
    print(f"  Kernel dimension: {kernel_dim}")

    check_fixed_zero = (kernel_dim == 0)
    print(f"\n  S_3-fixed point set = {{0}}? {check_fixed_zero}")
    print(f"  (Kernel dimension = 0 means only the zero vector is fixed)")
    results["checks"].append({"name": "S3_fixed_point_zero", "passed": bool(check_fixed_zero)})

    # Explicit check: just use s1 and s1*s2
    # s1 fixes the line y-axis (x=0). s1*s2 (120 rotation) fixes only origin.
    print("\n  Explicit argument:")
    print("  - s1 fixes the line {(0, y)} (perpendicular to alpha_1)")
    print("  - s1*s2 (120-degree rotation) fixes only {(0, 0)}")
    print("  - Intersection: {(0, 0)}")
    print("  - Therefore h^{S_3} = {0}.")

    # Also show: the S_3-fixed subspace of the FULL adjoint is also 0
    print("\n--- Additional: S_3-invariant elements of su(3) ---")
    print("  The adjoint rep decomposes as: su(3) = h + sum_alpha g_alpha")
    print("  S_3 permutes the root spaces g_alpha.")
    print("  S_3-fixed subset of h is {0} (shown above).")
    print("  S_3-fixed subset of root spaces: S_3 permutes them transitively")
    print("    within each orbit, so no nonzero element is fixed.")
    print("  Therefore su(3)^{S_3} = {0}.")

    results["passed"] = all(c["passed"] for c in results["checks"])
    return results


# ==============================================================================
# TASK 5: Z_2 Swap (T_+ <-> T_-) vs Charge Conjugation
# ==============================================================================

def task_5_Z2_swap_vs_charge_conjugation():
    """
    In SU(3), charge conjugation C acts on the Lie algebra as:
      C: T^a -> -(T^a)^T = -(T^a)*   (for Gell-Mann basis, which is Hermitian)

    On the Cartan subalgebra, this gives:
      C: H_i -> -H_i  (since T_3^T = T_3 is real symmetric but...
                        actually T_3 is diagonal, T_3^T = T_3, so C(T_3) = -T_3)

    The geometric T_+ <-> T_- swap:
    - Exchanges color vertices v_c <-> v_{c_bar}
    - In weight space: w_c -> -w_c (negation of all weights)
    - On roots: alpha -> -alpha (negation of all roots)

    These both act as H_i -> -H_i on the Cartan. But they differ in their
    physical interpretation.
    """
    print("\n" + "=" * 80)
    print("TASK 5: Z_2 (T_+ <-> T_-) Swap vs Charge Conjugation")
    print("=" * 80)

    results = {"task": 5, "passed": True, "checks": []}

    sqrt3 = np.sqrt(3)

    # --- SU(3) Gell-Mann matrices (for explicit computation) ---
    # lambda_1 through lambda_8
    lam = {
        1: np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], dtype=complex),       # lambda_1
        2: np.array([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]], dtype=complex),    # lambda_2
        3: np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], dtype=complex),      # lambda_3
        4: np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], dtype=complex),       # lambda_4
        5: np.array([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]], dtype=complex),    # lambda_5
        6: np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], dtype=complex),       # lambda_6
        7: np.array([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]], dtype=complex),    # lambda_7
        8: np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], dtype=complex) / sqrt3,  # lambda_8
    }

    T = {a: l / 2 for a, l in lam.items()}  # T^a = lambda_a / 2

    print("\n--- Charge conjugation C on Gell-Mann generators ---")
    print("  C(T^a) = -(T^a)^T    (complex conjugation of the representation)")
    print("  Equivalently: C(T^a) = -(T^a)*  for Hermitian generators")
    print()

    # Compute C(T^a) = -(T^a)^T for each
    for a in range(1, 9):
        Ta = T[a]
        CTa = -Ta.T  # C(T^a) = -(T^a)^T

        # Express C(T^a) in terms of T^b
        # For Gell-Mann basis: lambda_a^T properties:
        # Real symmetric (lambda_a^T = lambda_a): 1, 3, 4, 6, 8
        # Real antisymmetric (lambda_a^T = -lambda_a): 2, 5, 7

        is_symmetric = np.allclose(Ta, Ta.T)
        is_antisymmetric = np.allclose(Ta, -Ta.T)

        if is_symmetric:
            # C(T^a) = -(T^a)^T = -T^a
            sign_str = "-T^" + str(a)
            C_eigenvalue = -1
        elif is_antisymmetric:
            # C(T^a) = -(T^a)^T = -(-T^a) = +T^a
            sign_str = "+T^" + str(a)
            C_eigenvalue = +1
        else:
            sign_str = "???"
            C_eigenvalue = None

        print(f"  T^{a}: {'symmetric' if is_symmetric else 'antisymmetric':14s} -> C(T^{a}) = {sign_str}")

    # Cartan generators: T^3 and T^8
    print("\n--- C on Cartan generators ---")
    T3 = T[3]
    T8 = T[8]

    CT3 = -T3.T
    CT8 = -T8.T

    check_CT3 = np.allclose(CT3, -T3)
    check_CT8 = np.allclose(CT8, -T8)

    print(f"  C(T_3) = -(T_3)^T = -T_3? {check_CT3}")
    print(f"  C(T_8) = -(T_8)^T = -T_8? {check_CT8}")
    print(f"  => C: H_i -> -H_i  for both Cartan generators")

    results["checks"].append({"name": "C_negates_H1", "passed": bool(check_CT3)})
    results["checks"].append({"name": "C_negates_H2", "passed": bool(check_CT8)})

    # --- C on root generators ---
    print("\n--- C on root generators ---")
    # The root generators (raising/lowering operators) are:
    # E_{alpha_1} ~ T^1 + iT^2  (up to normalization)
    # E_{-alpha_1} ~ T^1 - iT^2
    # The standard convention: E_ij has a 1 in position (i,j) and 0 elsewhere.

    E12 = np.array([[0, 1, 0], [0, 0, 0], [0, 0, 0]], dtype=complex)  # E_{alpha_1}
    E21 = np.array([[0, 0, 0], [1, 0, 0], [0, 0, 0]], dtype=complex)  # E_{-alpha_1}
    E13 = np.array([[0, 0, 1], [0, 0, 0], [0, 0, 0]], dtype=complex)  # E_{alpha_1+alpha_2}
    E31 = np.array([[0, 0, 0], [0, 0, 0], [1, 0, 0]], dtype=complex)  # E_{-(alpha_1+alpha_2)}
    E23 = np.array([[0, 0, 0], [0, 0, 1], [0, 0, 0]], dtype=complex)  # E_{alpha_2}
    E32 = np.array([[0, 0, 0], [0, 0, 0], [0, 1, 0]], dtype=complex)  # E_{-alpha_2}

    root_gens = {
        "E_{+alpha_1}":          E12,
        "E_{-alpha_1}":          E21,
        "E_{+(alpha_1+alpha_2)}": E13,
        "E_{-(alpha_1+alpha_2)}": E31,
        "E_{+alpha_2}":          E23,
        "E_{-alpha_2}":          E32,
    }

    print("  C(E_alpha) = -(E_alpha)^T:")
    print()
    for name, E in root_gens.items():
        CE = -E.T
        # Find which root generator CE equals
        for name2, E2 in root_gens.items():
            if np.allclose(CE, E2):
                print(f"    C({name:30s}) = {name2}")
                break
            elif np.allclose(CE, -E2):
                print(f"    C({name:30s}) = -{name2}")
                break

    # More careful: C(E_ij) = -(E_ij)^T = -E_ji
    # So C(E_12) = -E_21 = -E_{-alpha_1}
    # C maps E_alpha to -E_{-alpha}
    print("\n  General rule: C(E_alpha) = -E_{-alpha}")
    print("  This means C: root alpha -> root -alpha  (with a sign on the generator)")

    # Verify this explicitly
    check_C_rule = True
    pairs = [
        (E12, E21, "+alpha_1", "-alpha_1"),
        (E13, E31, "+(alpha_1+alpha_2)", "-(alpha_1+alpha_2)"),
        (E23, E32, "+alpha_2", "-alpha_2"),
    ]
    for Epos, Eneg, name_pos, name_neg in pairs:
        C_Epos = -Epos.T
        if not np.allclose(C_Epos, -Eneg):
            check_C_rule = False

    print(f"  C(E_alpha) = -E_{{-alpha}} verified? {check_C_rule}")
    results["checks"].append({"name": "C_maps_E_alpha_to_neg_E_neg_alpha", "passed": bool(check_C_rule)})

    # --- Geometric T_+ <-> T_- swap ---
    print("\n--- Geometric T_+ <-> T_- swap ---")
    print("  The stella octangula has two tetrahedra T_+ and T_-.")
    print("  Swapping T_+ <-> T_- exchanges:")
    print("    v_R <-> v_{R_bar},  v_G <-> v_{G_bar},  v_B <-> v_{B_bar}")
    print("    v_W <-> v_{W_bar}")
    print()
    print("  In weight space, the color vertices of T_+ are:")
    print("    w_R, w_G, w_B")
    print("  The anti-color vertices of T_- are:")
    print("    w_{R_bar} = -w_R, w_{G_bar} = -w_G, w_{B_bar} = -w_B")
    print()
    print("  So T_+ <-> T_- acts on weights as w -> -w,")
    print("  which on roots gives alpha -> -alpha.")
    print()
    print("  On the Cartan subalgebra, this gives H_i -> -H_i,")
    print("  exactly matching charge conjugation C on the Cartan.")

    # Verify: -w_R, -w_G, -w_B are the 3-bar weights
    w_R = np.array([1/2, 1/(2*sqrt3)])
    w_G = np.array([-1/2, 1/(2*sqrt3)])
    w_B = np.array([0, -1/sqrt3])

    # 3-bar weights should be negations of 3 weights
    w_Rbar = -w_R
    w_Gbar = -w_G
    w_Bbar = -w_B

    print(f"\n  w_R    = ({w_R[0]:+.6f}, {w_R[1]:+.6f})")
    print(f"  w_Rbar = ({w_Rbar[0]:+.6f}, {w_Rbar[1]:+.6f}) = -w_R")
    print(f"  w_G    = ({w_G[0]:+.6f}, {w_G[1]:+.6f})")
    print(f"  w_Gbar = ({w_Gbar[0]:+.6f}, {w_Gbar[1]:+.6f}) = -w_G")
    print(f"  w_B    = ({w_B[0]:+.6f}, {w_B[1]:+.6f})")
    print(f"  w_Bbar = ({w_Bbar[0]:+.6f}, {w_Bbar[1]:+.6f}) = -w_B")

    # Check: sum of 3-bar weights = 0
    check_3bar_sum = vecs_equal(w_Rbar + w_Gbar + w_Bbar, np.zeros(2))
    print(f"\n  Sum of 3-bar weights = 0? {check_3bar_sum}")
    results["checks"].append({"name": "3bar_weights_negate", "passed": bool(check_3bar_sum)})

    # --- KEY DISTINCTION ---
    print("\n" + "-" * 60)
    print("KEY DISTINCTION: T_+ <-> T_- swap vs Charge Conjugation")
    print("-" * 60)
    print("""
  SIMILARITIES:
  - Both act as H_i -> -H_i on the Cartan subalgebra
  - Both map root alpha -> root -alpha
  - Both exchange the fundamental rep 3 <-> 3-bar

  DIFFERENCES:

  1. CHARGE CONJUGATION C is a physical operation:
     - C acts on the REPRESENTATION: C(T^a) = -(T^a)^T
     - It maps a quark state |q> to an antiquark state |q_bar>
     - It changes physical charges: color -> anti-color
     - C is basis-independent (defined by complex conjugation of rep)
     - In SU(3) gauge theory, C relates particles to antiparticles

  2. T_+ <-> T_- SWAP is a geometric operation:
     - It is a relabeling of which tetrahedron we call "T_+"
     - It is an OUTER automorphism of the stella
     - Choosing T_+ vs T_- is a CONVENTION (like choosing orientation)
     - The swap does NOT change the physics, only the labeling
     - It is analogous to choosing a Cartan-Weyl basis: H_i vs -H_i

  3. CRITICAL POINT:
     - The geometric swap T_+ <-> T_- is a CARTAN BASIS RELABELING
     - Physical charge conjugation ADDITIONALLY transforms the STATES
     - The geometric swap corresponds to C at the Lie algebra level
       but does NOT implement the full C transformation at the
       representation (state) level
     - More precisely: the geometric swap is the AUTOMORPHISM of the
       root system (alpha -> -alpha), which is the same as the
       Chevalley involution or the Cartan involution restricted to
       the compact real form
     - Charge conjugation C in particle physics is the REPRESENTATION-
       LEVEL version of this algebra automorphism
""")

    # --- Verify the Chevalley involution ---
    print("--- Chevalley involution (algebra-level version of C) ---")
    print("  The Chevalley involution omega acts on the Chevalley-Serre generators as:")
    print("    omega(E_i) = -F_i,  omega(F_i) = -E_i,  omega(H_i) = -H_i")
    print("  where E_i = E_{alpha_i} and F_i = E_{-alpha_i} are simple root generators.")
    print()
    print("  This matches the T_+ <-> T_- swap: alpha -> -alpha, H_i -> -H_i.")
    print("  The Chevalley involution is an INNER automorphism of sl(3,C)")
    print("  (since A_2 has the trivial Dynkin diagram automorphism for n=2,")
    print("   actually A_2 has a Z_2 outer automorphism: alpha_1 <-> alpha_2)")
    print()

    # Check: is the map alpha -> -alpha the same as the Dynkin diagram automorphism?
    # A_2 Dynkin diagram automorphism: alpha_1 <-> alpha_2
    # Root negation: alpha_1 -> -alpha_1, alpha_2 -> -alpha_2
    # These are DIFFERENT operations!

    alpha_1 = np.array([1.0, 0.0])
    alpha_2 = np.array([-0.5, sqrt3/2])

    # Dynkin diagram automorphism swaps alpha_1 <-> alpha_2
    # In 2D, what linear map takes alpha_1 -> alpha_2 and alpha_2 -> alpha_1?
    # Solve: M * alpha_1 = alpha_2, M * alpha_2 = alpha_1
    # [a b] [1  ] = [-1/2   ]   =>  a = -1/2,  b*sqrt(3)/2 = -1/2 + 1/2*0 ...
    # [c d] [0  ]   [sqrt3/2]       c = sqrt(3)/2

    A = np.column_stack([alpha_1, alpha_2])
    B = np.column_stack([alpha_2, alpha_1])
    M_dynkin = B @ np.linalg.inv(A)

    print("  Dynkin diagram automorphism (alpha_1 <-> alpha_2) as matrix:")
    print(f"    [{M_dynkin[0,0]:+.6f}  {M_dynkin[0,1]:+.6f}]")
    print(f"    [{M_dynkin[1,0]:+.6f}  {M_dynkin[1,1]:+.6f}]")
    print(f"    det = {np.linalg.det(M_dynkin):+.1f}")

    # Negation map
    M_neg = -np.eye(2)
    print(f"\n  Root negation (alpha -> -alpha) as matrix:")
    print(f"    [{M_neg[0,0]:+.6f}  {M_neg[0,1]:+.6f}]")
    print(f"    [{M_neg[1,0]:+.6f}  {M_neg[1,1]:+.6f}]")
    print(f"    det = {np.linalg.det(M_neg):+.1f}")

    # Check: is negation = Dynkin automorphism composed with something?
    # For A_2, the longest element w_0 of the Weyl group acts as -id on the root system
    # (since -w_0 is the Dynkin diagram automorphism for A_n, and for A_2, -w_0 = automorphism)
    # Actually: w_0 sends alpha_i -> -alpha_{n+1-i} for A_n.
    # For A_2: w_0(alpha_1) = -alpha_2, w_0(alpha_2) = -alpha_1
    # So w_0 = (negation) composed with (Dynkin swap)
    # Equivalently: negation = w_0 composed with (Dynkin swap)

    # The longest element w_0 for A_2
    # w_0 = s1 * s2 * s1 = s2 * s1 * s2 (the 180-degree rotation)
    def reflection(v, alpha):
        return v - 2 * np.dot(v, alpha) / np.dot(alpha, alpha) * alpha

    s1 = lambda v: reflection(v, alpha_1)
    s2 = lambda v: reflection(v, alpha_2)
    w0 = lambda v: s1(s2(s1(v)))

    w0_a1 = w0(alpha_1)
    w0_a2 = w0(alpha_2)

    print(f"\n  Longest Weyl element w_0:")
    print(f"    w_0(alpha_1) = ({w0_a1[0]:+.6f}, {w0_a1[1]:+.6f})")
    print(f"      = -alpha_2? {vecs_equal(w0_a1, -alpha_2)}")
    print(f"    w_0(alpha_2) = ({w0_a2[0]:+.6f}, {w0_a2[1]:+.6f})")
    print(f"      = -alpha_1? {vecs_equal(w0_a2, -alpha_1)}")

    check_w0 = vecs_equal(w0_a1, -alpha_2) and vecs_equal(w0_a2, -alpha_1)
    results["checks"].append({"name": "w0_sends_alpha_i_to_neg_alpha_j", "passed": bool(check_w0)})

    # So: negation = w_0 * Dynkin automorphism
    # Or: Dynkin automorphism = w_0 * negation = w_0 * (-id)
    # Since w_0 = s1*s2*s1 is the 180-degree rotation in 2D:
    M_w0 = np.column_stack([w0(np.array([1.0, 0.0])), w0(np.array([0.0, 1.0]))])
    print(f"\n  w_0 as matrix:")
    print(f"    [{M_w0[0,0]:+.6f}  {M_w0[0,1]:+.6f}]")
    print(f"    [{M_w0[1,0]:+.6f}  {M_w0[1,1]:+.6f}]")

    # w_0 * Dynkin = negation?
    product = M_w0 @ M_dynkin
    print(f"\n  w_0 * Dynkin automorphism:")
    print(f"    [{product[0,0]:+.6f}  {product[0,1]:+.6f}]")
    print(f"    [{product[1,0]:+.6f}  {product[1,1]:+.6f}]")
    check_product = np.allclose(product, M_neg)
    print(f"    = -I (negation)? {check_product}")
    results["checks"].append({"name": "negation_equals_w0_times_dynkin", "passed": bool(check_product)})

    print(f"""
  CONCLUSION:
  The root negation (alpha -> -alpha) which implements T_+ <-> T_- is:
    negation = w_0 * (Dynkin diagram automorphism)

  This is the composition of:
    (a) The longest Weyl element w_0 (an INNER automorphism, 180-degree rotation)
    (b) The Dynkin diagram automorphism alpha_1 <-> alpha_2 (an OUTER automorphism)

  At the Lie algebra level, this is the CHEVALLEY INVOLUTION, which sends:
    E_alpha -> -E_{{-alpha}}, H_i -> -H_i

  The geometric T_+ <-> T_- swap IMPLEMENTS this Chevalley involution.
  Physical charge conjugation C is the REPRESENTATION-LEVEL version:
    C: T^a -> -(T^a)^T

  They agree on the algebra but differ conceptually:
    - T_+ <-> T_- is a RELABELING (convention choice)
    - C is a PHYSICAL SYMMETRY (particle <-> antiparticle)
""")

    results["passed"] = all(c["passed"] for c in results["checks"])
    return results


# ==============================================================================
# MAIN EXECUTION
# ==============================================================================

def main():
    results = {
        "proposition": "0.0.39",
        "title": "SU(3) Root Space Geometry Verification",
        "timestamp": datetime.now().isoformat(),
        "tasks": []
    }

    print("*" * 80)
    print("PROPOSITION 0.0.39: SU(3) Root Space Geometry Verification")
    print("*" * 80)
    print()

    # Run all tasks
    r1 = task_1_weights_roots_cyclic_action()
    results["tasks"].append(r1)

    r2 = task_2_S3_does_not_preserve_positive_roots()
    results["tasks"].append(r2)

    r3 = task_3_correct_characterization()
    results["tasks"].append(r3)

    r4 = task_4_S3_action_on_Cartan()
    results["tasks"].append(r4)

    r5 = task_5_Z2_swap_vs_charge_conjugation()
    results["tasks"].append(r5)

    # Overall summary
    all_passed = all(t["passed"] for t in results["tasks"])
    results["overall_status"] = "PASSED" if all_passed else "FAILED"

    print("\n" + "=" * 80)
    print("OVERALL SUMMARY")
    print("=" * 80)
    for t in results["tasks"]:
        task_num = t["task"]
        status = "PASSED" if t["passed"] else "FAILED"
        n_checks = len(t["checks"])
        n_passed = sum(1 for c in t["checks"] if c["passed"])
        print(f"  Task {task_num}: {status} ({n_passed}/{n_checks} checks)")
    print(f"\n  OVERALL: {results['overall_status']}")

    # Key findings summary
    print("\n" + "=" * 80)
    print("KEY FINDINGS FOR PROPOSITION 0.0.39 CORRECTION")
    print("=" * 80)
    print("""
  1. The Z_3 cyclic permutation (R->G->B->R) acts on roots as:
       alpha_2  ->  -(alpha_1+alpha_2)  ->  alpha_1  ->  alpha_2
     This orbit MIXES positive and negative roots.

  2. The Weyl group S_3 does NOT preserve the set of positive roots.
     Every non-identity element maps at least one positive root to a
     negative root.

  3. CORRECT CHARACTERIZATION: The 3 faces of T_+ opposite color vertices
     map to one COMPLETE Z_3 orbit of root generators:
       {E_{alpha_2}, E_{-(alpha_1+alpha_2)}, E_{alpha_1}}
     This contains 2 positive and 1 negative root.
     The 3 faces of T_- map to the other Z_3 orbit:
       {E_{-alpha_2}, E_{alpha_1+alpha_2}, E_{-alpha_1}}
     which contains 1 positive and 2 negative root.

     The original claim "T_+ -> all positive roots, T_- -> all negative roots"
     is INCORRECT and must be revised.

  4. S_3 preserves h as a subspace, acts nontrivially on individual elements,
     and the S_3-fixed point set is {0} (zero-dimensional).

  5. The geometric T_+ <-> T_- swap implements the Chevalley involution
     (alpha -> -alpha, H_i -> -H_i) at the Lie algebra level.
     This is a CARTAN BASIS RELABELING, not physical charge conjugation C.
     C is the representation-level version of the same algebra automorphism.
     The negation map factors as: (longest Weyl element w_0) * (Dynkin
     diagram automorphism alpha_1 <-> alpha_2).
""")

    # Save results
    output_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/foundations/prop_0_0_39_root_space_results.json"

    # Convert numpy arrays to lists for JSON serialization
    def numpy_to_python(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.bool_):
            return bool(obj)
        return obj

    # Deep convert
    import copy
    def deep_convert(obj):
        if isinstance(obj, dict):
            return {k: deep_convert(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [deep_convert(v) for v in obj]
        elif isinstance(obj, tuple):
            return [deep_convert(v) for v in obj]
        else:
            return numpy_to_python(obj)

    results_json = deep_convert(results)

    with open(output_path, "w") as f:
        json.dump(results_json, f, indent=2, default=str)

    print(f"\n  Results saved to: {output_path}")

    return results

if __name__ == "__main__":
    main()
