#!/usr/bin/env python3
"""
Verification: Does the 16-cell project to a stella octangula?
Version 2: More careful analysis

The initial result showed that distance COUNT patterns match with ratio 0.8660.
This means the shapes may be SIMILAR (congruent up to scale and rotation).

Let's verify this more rigorously.

Author: Claude (verification agent)
Date: 2026-01-22
"""

import numpy as np
from numpy.linalg import norm, det
from scipy.spatial.transform import Rotation

# 16-cell vertices
cell16_vertices = np.array([
    [1, 0, 0, 0],
    [-1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, -1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, -1, 0],
    [0, 0, 0, 1],
    [0, 0, 0, -1]
], dtype=float)

# Stella octangula vertices (in 3D)
# T_+ (even number of minus signs)
T_plus = np.array([
    [1, 1, 1],
    [1, -1, -1],
    [-1, 1, -1],
    [-1, -1, 1]
], dtype=float)

# T_- (odd number of minus signs)
T_minus = np.array([
    [-1, -1, -1],
    [-1, 1, 1],
    [1, -1, 1],
    [1, 1, -1]
], dtype=float)

stella_vertices = np.vstack([T_plus, T_minus])

# Orthonormal basis for 3D subspace perpendicular to [1,1,1,1]
u1 = np.array([1, -1, 0, 0]) / np.sqrt(2)
u2 = np.array([1, 1, -2, 0]) / np.sqrt(6)
u3 = np.array([1, 1, 1, -3]) / np.sqrt(12)

# Project 16-cell vertices
def project_to_3d(v4d):
    """Project 4D point to 3D subspace perpendicular to [1,1,1,1]."""
    return np.array([np.dot(v4d, u1), np.dot(v4d, u2), np.dot(v4d, u3)])

projected_16cell = np.array([project_to_3d(v) for v in cell16_vertices])

print("="*70)
print("VERIFICATION: Is projected 16-cell similar to stella octangula?")
print("="*70)

# Normalize both to have the same scale (unit distance from origin)
proj_scale = norm(projected_16cell[0])
stella_scale = norm(stella_vertices[0])

proj_normalized = projected_16cell / proj_scale
stella_normalized = stella_vertices / stella_scale

print(f"\nProjected 16-cell, normalized (distance from origin = 1):")
for i, p in enumerate(proj_normalized):
    print(f"  v{i}: ({p[0]:+.6f}, {p[1]:+.6f}, {p[2]:+.6f})")

print(f"\nStella octangula, normalized (distance from origin = 1):")
for i, s in enumerate(stella_normalized):
    print(f"  s{i}: ({s[0]:+.6f}, {s[1]:+.6f}, {s[2]:+.6f})")

# Compute the Gram matrix (matrix of all pairwise dot products)
# Two point sets are similar iff their Gram matrices are equal (up to permutation)

def gram_matrix(points):
    """Compute Gram matrix of pairwise dot products."""
    n = len(points)
    G = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            G[i,j] = np.dot(points[i], points[j])
    return G

proj_gram = gram_matrix(proj_normalized)
stella_gram = gram_matrix(stella_normalized)

print("\n" + "="*70)
print("Gram matrix analysis (dot products)")
print("="*70)

print("\nProjected 16-cell Gram matrix:")
print(np.array2string(proj_gram, precision=4, suppress_small=True))

print("\nStella octangula Gram matrix:")
print(np.array2string(stella_gram, precision=4, suppress_small=True))

# The Gram matrices should be equal up to a permutation of rows/columns
# if the point sets are congruent

# Let's check the eigenvalues of each Gram matrix
# (eigenvalues are invariant under rotation but depend on the point configuration)

proj_eigvals = sorted(np.linalg.eigvalsh(proj_gram))
stella_eigvals = sorted(np.linalg.eigvalsh(stella_gram))

print("\nEigenvalues of Gram matrices:")
print(f"  Projected: {[f'{e:.4f}' for e in proj_eigvals]}")
print(f"  Stella:    {[f'{e:.4f}' for e in stella_eigvals]}")

# Also check: for each set, how many distinct dot products are there?
def unique_dot_products(points, tol=1e-6):
    """Find unique dot products (excluding self-products)."""
    n = len(points)
    dots = []
    for i in range(n):
        for j in range(i+1, n):
            d = np.dot(points[i], points[j])
            dots.append(d)
    dots = np.array(dots)
    dots_sorted = np.sort(dots)

    unique = [dots_sorted[0]]
    for d in dots_sorted[1:]:
        if abs(d - unique[-1]) > tol:
            unique.append(d)
    return unique, dots

proj_dots, proj_all_dots = unique_dot_products(proj_normalized)
stella_dots, stella_all_dots = unique_dot_products(stella_normalized)

print("\nUnique pairwise dot products:")
print(f"  Projected: {[f'{d:.6f}' for d in proj_dots]}")
print(f"  Stella:    {[f'{d:.6f}' for d in stella_dots]}")

# Check if the structures can be matched
print("\n" + "="*70)
print("Attempting to find rotation/permutation matching")
print("="*70)

# Key insight: if the projected points form a stella octangula,
# we should be able to find a permutation and rotation that maps one to the other

# Let's try a different approach: check if both form antipodal pairs
# and if the tetrahedra have the same structure

print("\nAntipodal structure check:")
print("In the projected 16-cell:")
for i in range(4):
    v1, v2 = proj_normalized[2*i], proj_normalized[2*i+1]
    is_antipodal = np.allclose(v1, -v2)
    print(f"  v{2*i} and v{2*i+1}: antipodal = {is_antipodal}, sum = {v1 + v2}")

print("\nIn the stella octangula:")
# The antipodal pairs are: (T+[i], T-[some permutation])
# Let's find them
for i, s1 in enumerate(stella_normalized):
    for j, s2 in enumerate(stella_normalized):
        if np.allclose(s1, -s2) and i < j:
            print(f"  s{i} and s{j}: antipodal")

# The key test: can we actually ROTATE the projected points to match stella?
print("\n" + "="*70)
print("CRITICAL TEST: Attempting to find rotation matrix")
print("="*70)

# Method: Use Procrustes analysis
# We need to find if there's a permutation P and rotation R such that
# R @ proj_normalized ≈ stella_normalized[P]

from itertools import permutations

def procrustes(A, B):
    """Find optimal rotation R such that R @ A ≈ B (minimizing Frobenius norm)."""
    # SVD of B @ A.T
    H = B.T @ A
    U, S, Vt = np.linalg.svd(H)
    R = U @ Vt

    # Handle reflection
    if det(R) < 0:
        Vt[-1, :] *= -1
        R = U @ Vt

    return R

def check_match(P, A, B, tol=1e-4):
    """Check if permutation P makes A matchable to B via rotation."""
    B_perm = B[list(P)]
    R = procrustes(A, B_perm)
    rotated_A = (R @ A.T).T
    error = np.linalg.norm(rotated_A - B_perm)
    return error, R

print("Searching through permutations (this may take a moment)...")

best_error = float('inf')
best_perm = None
best_R = None

# Only check a subset of permutations (full would be 8! = 40320)
# Use the structure: both should have antipodal pairs
# So we can reduce the search space

# Actually, let's just check all 8! permutations - it's not that many
count = 0
for perm in permutations(range(8)):
    count += 1
    error, R = check_match(perm, proj_normalized, stella_normalized)
    if error < best_error:
        best_error = error
        best_perm = perm
        best_R = R

    if count % 5000 == 0:
        print(f"  Checked {count} permutations, best error so far: {best_error:.6f}")

print(f"\nTotal permutations checked: {count}")
print(f"Best matching error: {best_error:.6f}")
print(f"Best permutation: {best_perm}")

if best_error < 0.01:
    print(f"\n✅ SUCCESS: The projected 16-cell IS congruent to stella octangula!")
    print(f"   The matching rotation matrix R:")
    print(np.array2string(best_R, precision=4, suppress_small=True))

    # Verify the match
    print("\nVerification of match:")
    rotated_proj = (best_R @ proj_normalized.T).T
    stella_reordered = stella_normalized[list(best_perm)]
    for i in range(8):
        diff = norm(rotated_proj[i] - stella_reordered[i])
        print(f"  Point {i}: difference = {diff:.6f}")
else:
    print(f"\n❌ FAILED: The projected 16-cell is NOT congruent to stella octangula")
    print(f"   Minimum achievable error: {best_error:.6f}")

# Final analysis
print("\n" + "="*70)
print("FINAL ANALYSIS")
print("="*70)

if best_error < 0.01:
    print("""
CONCLUSION: The claim in Theorem 0.0.4 §3.3.1 IS MATHEMATICALLY CORRECT!

The 16-cell vertices, when projected to the 3D hyperplane perpendicular
to [1,1,1,1], DO form a stella octangula (up to rotation and scaling).

The scaling factor is √(3/4) = √3/2 ≈ 0.866 (as seen in the distance ratios).

This validates Proposition 3.3.1 in Theorem 0.0.4.
""")
else:
    print("""
CONCLUSION: The claim in Theorem 0.0.4 §3.3.1 is INCORRECT.

The 16-cell vertices, when projected to 3D along [1,1,1,1], do NOT
form a stella octangula.

The projected shape has the same number of vertices and similar
distance structure, but is NOT geometrically congruent.
""")
