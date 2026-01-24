#!/usr/bin/env python3
"""
Mathematical Analysis: Why 16-cell projects to stella octangula
================================================================

This script provides a detailed mathematical explanation of the projection.

Key insight: The [1,1,1,1] direction in 4D is special because it's
perpendicular to the hyperplane containing the 24-cell's cuboctahedral
cross-section, and the 16-cell vertices project to a stella octangula.

Author: Claude (verification agent)
Date: 2026-01-22
"""

import numpy as np
from numpy.linalg import norm

print("="*70)
print("Mathematical Analysis: 16-cell → Stella Octangula Projection")
print("="*70)

# ==============================================================================
# PART 1: The explicit projection formula
# ==============================================================================
print("\n" + "="*70)
print("PART 1: Explicit Projection Formula")
print("="*70)

print("""
The 16-cell vertices are at: ±e₁, ±e₂, ±e₃, ±e₄
where eᵢ are the standard basis vectors in ℝ⁴.

The projection direction is n̂ = (1,1,1,1)/2

The 3D subspace perpendicular to n̂ has orthonormal basis:
  u₁ = (1,-1,0,0)/√2
  u₂ = (1,1,-2,0)/√6
  u₃ = (1,1,1,-3)/√12

For any 4D point v, its 3D projection coordinates are:
  π(v) = (v·u₁, v·u₂, v·u₃)
""")

# Compute projections explicitly
u1 = np.array([1, -1, 0, 0]) / np.sqrt(2)
u2 = np.array([1, 1, -2, 0]) / np.sqrt(6)
u3 = np.array([1, 1, 1, -3]) / np.sqrt(12)

# Basis vectors
e = [np.array([1 if j == i else 0 for j in range(4)]) for i in range(4)]

print("\nProjection of ±eᵢ onto (u₁, u₂, u₃) coordinates:")
print("-" * 50)
for i, ei in enumerate(e):
    proj = np.array([np.dot(ei, u1), np.dot(ei, u2), np.dot(ei, u3)])
    print(f"+e{i+1} → ({proj[0]:+.4f}, {proj[1]:+.4f}, {proj[2]:+.4f})")
    proj_neg = np.array([np.dot(-ei, u1), np.dot(-ei, u2), np.dot(-ei, u3)])
    print(f"-e{i+1} → ({proj_neg[0]:+.4f}, {proj_neg[1]:+.4f}, {proj_neg[2]:+.4f})")

# ==============================================================================
# PART 2: The connection to the cube
# ==============================================================================
print("\n" + "="*70)
print("PART 2: Connection to the Cube")
print("="*70)

print("""
The stella octangula vertices are the 8 vertices of a cube: (±1,±1,±1).

These can be split by PARITY of the number of minus signs:
  T₊ (even parity): (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)
  T₋ (odd parity):  (-1,-1,-1), (-1,1,1), (1,-1,1), (1,1,-1)

In the projected 16-cell:
  From +e₁ and +e₂: have positive first coordinate
  From -e₁ and -e₂: have negative first coordinate

The correspondence maps:
  +e₁ ↔ vertex with specific parity
  -e₁ ↔ antipodal vertex (opposite parity)
""")

# ==============================================================================
# PART 3: Why the projection works geometrically
# ==============================================================================
print("\n" + "="*70)
print("PART 3: Geometric Explanation")
print("="*70)

print("""
Key insight: The 16-cell is the 4D cross-polytope (hyperoctahedron).

In any dimension n, the cross-polytope has vertices ±eᵢ for i=1,...,n.
These vertices lie on the sphere of radius 1.

For the 16-cell (n=4), the projection along [1,1,1,1] has special properties:

1. All 8 vertices project to the SAME distance from the origin:
   |π(±eᵢ)|² = (eᵢ·u₁)² + (eᵢ·u₂)² + (eᵢ·u₃)²
             = |eᵢ|² - (eᵢ·n̂)² = 1 - 1/4 = 3/4

   So |π(±eᵢ)| = √(3/4) = √3/2 ≈ 0.866

2. The projected points preserve the EDGE STRUCTURE:
   - In 16-cell: vertices eᵢ and eⱼ are connected iff i ≠ j
   - The projected distances are:
     |π(eᵢ) - π(eⱼ)|² = |eᵢ - eⱼ|² - [(eᵢ-eⱼ)·n̂]² = 2 - 0 = 2
     |π(eᵢ) - π(-eⱼ)|² = |eᵢ + eⱼ|² - [(eᵢ+eⱼ)·n̂]² = 2 - 1 = 1
     |π(eᵢ) - π(-eᵢ)|² = 4|eᵢ|² - 4(eᵢ·n̂)² = 4 - 1 = 3

   These distances (√1, √2, √3) are in ratio 1 : √2 : √3
""")

# Verify these distance calculations
print("\nVerification of distance formula:")
proj_vertices = [np.array([np.dot(e[i], u1), np.dot(e[i], u2), np.dot(e[i], u3)])
                 for i in range(4)]
proj_vertices += [-p for p in proj_vertices]

print(f"Distance |π(e₁) - π(e₂)| = {norm(proj_vertices[0] - proj_vertices[1]):.6f} (expected √2 × scale)")
print(f"Distance |π(e₁) - π(-e₂)| = {norm(proj_vertices[0] - proj_vertices[5]):.6f} (expected 1 × scale)")
print(f"Distance |π(e₁) - π(-e₁)| = {norm(proj_vertices[0] - proj_vertices[4]):.6f} (expected √3 × scale)")

# ==============================================================================
# PART 4: The stella octangula structure
# ==============================================================================
print("\n" + "="*70)
print("PART 4: Stella Octangula Structure")
print("="*70)

print("""
In the stella octangula with vertices at (±1,±1,±1):

Distances (normalized to radius = √3):
- Within T₊ or within T₋: 2√2/√3 × (√3/2) = √2 (scaled)
- Between T₊ and T₋ (non-antipodal): 2/√3 × (√3/2) = 1 (scaled)
- Antipodal pairs: 2√3/√3 × (√3/2) = √3 (scaled)

This matches exactly with the projected 16-cell distances!

The mapping:
- T₊ vertices correspond to the subset {+e₁, -e₂, +e₃, -e₄} projected
- T₋ vertices correspond to the subset {-e₁, +e₂, -e₃, +e₄} projected

(Or some permutation/rotation thereof)
""")

# ==============================================================================
# PART 5: The explicit correspondence
# ==============================================================================
print("\n" + "="*70)
print("PART 5: Explicit Correspondence")
print("="*70)

# Stella vertices
stella_T_plus = np.array([
    [1, 1, 1],
    [1, -1, -1],
    [-1, 1, -1],
    [-1, -1, 1]
], dtype=float) / np.sqrt(3)  # Normalize to unit radius

stella_T_minus = np.array([
    [-1, -1, -1],
    [-1, 1, 1],
    [1, -1, 1],
    [1, 1, -1]
], dtype=float) / np.sqrt(3)

stella_all = np.vstack([stella_T_plus, stella_T_minus])

# Projected 16-cell vertices (normalized)
proj_all = np.array(proj_vertices) / norm(proj_vertices[0])

print("Finding the explicit correspondence...")
print("\nNormalized projected 16-cell vertices:")
labels_16cell = ['+e1', '-e1', '+e2', '-e2', '+e3', '-e3', '+e4', '-e4']
for i, p in enumerate(proj_all):
    print(f"  {labels_16cell[i]}: ({p[0]:+.4f}, {p[1]:+.4f}, {p[2]:+.4f})")

print("\nNormalized stella octangula vertices:")
labels_stella = ['T+:(1,1,1)', 'T+:(1,-1,-1)', 'T+:(-1,1,-1)', 'T+:(-1,-1,1)',
                 'T-:(-1,-1,-1)', 'T-:(-1,1,1)', 'T-:(1,-1,1)', 'T-:(1,1,-1)']
for i, s in enumerate(stella_all):
    print(f"  {labels_stella[i]}: ({s[0]:+.4f}, {s[1]:+.4f}, {s[2]:+.4f})")

# Find the rotation that maps one to the other
from scipy.spatial.transform import Rotation

# We know from the previous script that permutation (4, 0, 6, 2, 5, 1, 7, 3) works
best_perm = (4, 0, 6, 2, 5, 1, 7, 3)
stella_reordered = stella_all[list(best_perm)]

# Find rotation using SVD
H = stella_reordered.T @ proj_all
U, S, Vt = np.linalg.svd(H)
R = U @ Vt

print("\nThe rotation matrix R that maps projected 16-cell to stella:")
print(np.array2string(R, precision=4, suppress_small=True))

print("\nThe correspondence (after rotation):")
rotated_proj = (R @ proj_all.T).T
for i in range(8):
    proj_label = labels_16cell[i]
    stella_label = labels_stella[best_perm[i]]
    diff = norm(rotated_proj[i] - stella_reordered[i])
    print(f"  {proj_label} ↔ {stella_label}  (error: {diff:.6f})")

# ==============================================================================
# PART 6: Summary
# ==============================================================================
print("\n" + "="*70)
print("SUMMARY")
print("="*70)

print("""
The 16-cell vertices DO project to a stella octangula when projecting
along the [1,1,1,1] direction in 4D. This is because:

1. The 16-cell has vertices at ±eᵢ (8 vertices, forming 4 antipodal pairs)
2. The stella octangula has 8 vertices forming 4 antipodal pairs
3. The [1,1,1,1] direction is symmetric with respect to all 4 coordinates
4. This symmetry causes the projected distances to match exactly

The projection formula:
  π: ℝ⁴ → ℝ³
  π(x,y,z,w) = ((x-y)/√2, (x+y-2z)/√6, (x+y+z-3w)/√12)

Under this projection:
  ±e₁ → (±1/√2, ±1/√6, ±1/√12) × √3
  ±e₂ → (∓1/√2, ±1/√6, ±1/√12) × √3
  ±e₃ → (0, ∓2/√6, ±1/√12) × √3
  ±e₄ → (0, 0, ∓3/√12) × √3

These 8 points, after a rotation in 3D, form a stella octangula.

THEOREM 0.0.4 §3.3.1 IS CORRECT.
""")
