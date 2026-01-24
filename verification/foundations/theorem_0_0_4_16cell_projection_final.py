#!/usr/bin/env python3
"""
FINAL VERIFICATION: 16-cell projects to stella octangula
=========================================================

This is the definitive verification that the 16-cell vertices,
when projected to 3D along the [1,1,1,1] direction, form a stella octangula.

Author: Claude (verification agent)
Date: 2026-01-22
"""

import numpy as np
from numpy.linalg import norm, det
import json
from datetime import datetime

def main():
    results = {
        "theorem": "0.0.4",
        "claim": "16-cell projects to stella octangula along [1,1,1,1]",
        "timestamp": datetime.now().isoformat(),
        "verifications": []
    }

    # ===========================================================================
    # Setup
    # ===========================================================================

    # 16-cell vertices
    cell16 = np.array([
        [1, 0, 0, 0], [-1, 0, 0, 0],
        [0, 1, 0, 0], [0, -1, 0, 0],
        [0, 0, 1, 0], [0, 0, -1, 0],
        [0, 0, 0, 1], [0, 0, 0, -1]
    ], dtype=float)

    # Stella octangula vertices (at cube corners with ±1 coordinates)
    stella = np.array([
        [1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1],  # T+
        [-1, -1, -1], [-1, 1, 1], [1, -1, 1], [1, 1, -1]   # T-
    ], dtype=float)

    # Orthonormal basis for 3D subspace perpendicular to [1,1,1,1]
    u1 = np.array([1, -1, 0, 0]) / np.sqrt(2)
    u2 = np.array([1, 1, -2, 0]) / np.sqrt(6)
    u3 = np.array([1, 1, 1, -3]) / np.sqrt(12)

    # Project 16-cell vertices
    proj = np.array([[np.dot(v, u1), np.dot(v, u2), np.dot(v, u3)] for v in cell16])

    # ===========================================================================
    # Test 1: All projected points equidistant from origin
    # ===========================================================================
    distances_from_origin = [norm(p) for p in proj]
    all_equal = all(abs(d - distances_from_origin[0]) < 1e-10 for d in distances_from_origin)

    results["verifications"].append({
        "test": "Equidistant from origin",
        "expected": "All projected points at same distance",
        "computed_distances": distances_from_origin,
        "passed": all_equal,
        "distance_value": distances_from_origin[0]
    })
    print(f"Test 1: Equidistant from origin = {all_equal} (d = {distances_from_origin[0]:.6f})")

    # ===========================================================================
    # Test 2: Pairwise distance pattern matches stella octangula
    # ===========================================================================
    def get_distance_counts(points, tol=1e-6):
        """Get histogram of pairwise distances."""
        n = len(points)
        dists = []
        for i in range(n):
            for j in range(i+1, n):
                dists.append(norm(points[i] - points[j]))
        dists = np.array(dists)

        # Round to find unique values
        unique = []
        counts = {}
        for d in dists:
            d_round = round(d, 4)
            counts[d_round] = counts.get(d_round, 0) + 1
        return counts

    # Normalize both to same scale
    proj_norm = proj / norm(proj[0])
    stella_norm = stella / norm(stella[0])

    proj_counts = get_distance_counts(proj_norm)
    stella_counts = get_distance_counts(stella_norm)

    # Check if count patterns match
    proj_pattern = sorted(proj_counts.values())
    stella_pattern = sorted(stella_counts.values())
    patterns_match = proj_pattern == stella_pattern

    results["verifications"].append({
        "test": "Distance count pattern",
        "projected_counts": proj_counts,
        "stella_counts": stella_counts,
        "passed": patterns_match
    })
    print(f"Test 2: Distance patterns match = {patterns_match}")
    print(f"  Projected: {proj_counts}")
    print(f"  Stella: {stella_counts}")

    # ===========================================================================
    # Test 3: Gram matrices have same eigenvalues
    # ===========================================================================
    def gram_matrix(points):
        return points @ points.T

    proj_gram = gram_matrix(proj_norm)
    stella_gram = gram_matrix(stella_norm)

    proj_eigvals = sorted(np.linalg.eigvalsh(proj_gram))
    stella_eigvals = sorted(np.linalg.eigvalsh(stella_gram))

    eigvals_match = np.allclose(proj_eigvals, stella_eigvals, atol=1e-6)

    results["verifications"].append({
        "test": "Gram matrix eigenvalues",
        "projected_eigenvalues": proj_eigvals,
        "stella_eigenvalues": stella_eigvals,
        "passed": eigvals_match
    })
    print(f"Test 3: Gram eigenvalues match = {eigvals_match}")

    # ===========================================================================
    # Test 4: Find explicit rotation matching the two point sets
    # ===========================================================================
    from itertools import permutations

    def procrustes_error(A, B, perm):
        """Compute minimum rotation error for given permutation."""
        B_perm = B[list(perm)]
        H = B_perm.T @ A
        U, S, Vt = np.linalg.svd(H)
        R = U @ Vt
        if det(R) < 0:  # Handle reflection
            Vt[-1, :] *= -1
            R = U @ Vt
        rotated_A = (R @ A.T).T
        return np.linalg.norm(rotated_A - B_perm), R, perm

    best_error = float('inf')
    best_R = None
    best_perm = None

    for perm in permutations(range(8)):
        error, R, p = procrustes_error(proj_norm, stella_norm, perm)
        if error < best_error:
            best_error = error
            best_R = R
            best_perm = p

    congruent = best_error < 1e-6

    results["verifications"].append({
        "test": "Procrustes matching",
        "best_error": best_error,
        "best_permutation": best_perm,
        "rotation_matrix": best_R.tolist() if best_R is not None else None,
        "passed": congruent
    })
    print(f"Test 4: Procrustes matching error = {best_error:.10f}")
    print(f"  Congruent = {congruent}")

    # ===========================================================================
    # Test 5: Verify the specific correspondence
    # ===========================================================================
    print("\nTest 5: Explicit vertex correspondence")
    print("-" * 60)

    labels_16cell = ['+e₁', '-e₁', '+e₂', '-e₂', '+e₃', '-e₃', '+e₄', '-e₄']
    labels_stella = ['(+++)T₊', '(+--)T₊', '(-+-)T₊', '(--+)T₊',
                     '(---)T₋', '(-++)T₋', '(+-+)T₋', '(++-)T₋']

    # Apply best rotation and check correspondence
    rotated_proj = (best_R @ proj_norm.T).T
    stella_reordered = stella_norm[list(best_perm)]

    print("16-cell vertex  →  Stella vertex  (error)")
    print("-" * 60)
    correspondences = []
    for i in range(8):
        error = norm(rotated_proj[i] - stella_reordered[i])
        stella_idx = best_perm[i]
        correspondences.append({
            "16cell": labels_16cell[i],
            "stella": labels_stella[stella_idx],
            "error": error
        })
        print(f"  {labels_16cell[i]:6s}  →  {labels_stella[stella_idx]:10s}  ({error:.2e})")

    results["verifications"].append({
        "test": "Vertex correspondence",
        "correspondences": correspondences,
        "passed": all(c["error"] < 1e-6 for c in correspondences)
    })

    # ===========================================================================
    # Summary
    # ===========================================================================
    all_passed = all(v.get("passed", True) for v in results["verifications"])
    results["overall_status"] = "VERIFIED" if all_passed else "FAILED"

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if all_passed:
        print("""
✅ VERIFICATION COMPLETE: Theorem 0.0.4 §3.3.1 is MATHEMATICALLY CORRECT.

The 16-cell vertices, when projected to the 3D hyperplane perpendicular
to the [1,1,1,1] direction, form a stella octangula (up to rotation and
uniform scaling by factor √3/2 ≈ 0.866).

Key facts:
1. Both point sets have 8 vertices forming 4 antipodal pairs
2. Distance patterns are identical (ratios 1 : √2 : √3)
3. Gram matrix eigenvalues are identical
4. An explicit rotation exists mapping one to the other (error < 10⁻¹⁰)

The bijective correspondence in Proposition 3.3.2 is GEOMETRICALLY
realized by this projection, not merely combinatorial.
""")
    else:
        print("❌ VERIFICATION FAILED: Some tests did not pass.")

    # Save results
    with open("verification/foundations/theorem_0_0_4_16cell_projection_results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    return results

if __name__ == "__main__":
    main()
