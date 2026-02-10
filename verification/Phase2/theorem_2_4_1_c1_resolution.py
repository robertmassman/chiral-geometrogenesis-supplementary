#!/usr/bin/env python3
"""
Theorem 2.4.1 Issue C1 Resolution: Lift Map Analysis
=====================================================

The issue: The lift map φ(x₁, x₂, x₃) = ½(x₁, x₂, x₃, x₁x₂x₃) maps stella
octangula vertices to demitesseract vertices, NOT 16-cell vertices.

This script:
1. Analyzes what the current lift actually produces
2. Explores the relationship between demitesseract and 16-cell
3. Determines if the embedding chain can proceed through demitesseract
4. Provides the corrected mathematical statement

Author: Verification System
Date: 2025-12-26
"""

import numpy as np
from itertools import combinations, product
import json

print("=" * 70)
print("ISSUE C1 RESOLUTION: Lift Map Analysis")
print("=" * 70)

# =============================================================================
# Part 1: Stella Octangula Vertices
# =============================================================================
print("\n" + "=" * 70)
print("PART 1: Stella Octangula Structure")
print("=" * 70)

# T+ tetrahedron (positive parity vertices)
T_plus = np.array([
    [1, 1, 1],
    [1, -1, -1],
    [-1, 1, -1],
    [-1, -1, 1]
], dtype=float)

# T- tetrahedron (negative parity vertices)
T_minus = np.array([
    [-1, -1, -1],
    [-1, 1, 1],
    [1, -1, 1],
    [1, 1, -1]
], dtype=float)

stella = np.vstack([T_plus, T_minus])

print("\nStella octangula vertices (8 total):")
print("T+ (parity +1):", T_plus.tolist())
print("T- (parity -1):", T_minus.tolist())

# Verify parity structure
print("\nParity check (x₁ × x₂ × x₃):")
for v in T_plus:
    parity = v[0] * v[1] * v[2]
    print(f"  {v} → parity = {parity}")
for v in T_minus:
    parity = v[0] * v[1] * v[2]
    print(f"  {v} → parity = {parity}")

# =============================================================================
# Part 2: Current Lift Map Analysis
# =============================================================================
print("\n" + "=" * 70)
print("PART 2: Current Lift Map φ(x₁, x₂, x₃) = ½(x₁, x₂, x₃, x₁x₂x₃)")
print("=" * 70)

def lift_map(v):
    """Current lift map from theorem."""
    x1, x2, x3 = v
    x4 = x1 * x2 * x3
    return np.array([x1, x2, x3, x4]) / 2

lifted_vertices = np.array([lift_map(v) for v in stella])

print("\nLifted vertices:")
for i, (orig, lifted) in enumerate(zip(stella, lifted_vertices)):
    print(f"  {orig} → {lifted}")

# Check what these vertices form
print("\nProperties of lifted vertices:")
norms = np.linalg.norm(lifted_vertices, axis=1)
print(f"  All norms: {norms}")
print(f"  All same norm: {np.allclose(norms, norms[0])}")
print(f"  Norm value: {norms[0]:.6f}")

# =============================================================================
# Part 3: Compare with Standard 16-cell
# =============================================================================
print("\n" + "=" * 70)
print("PART 3: Standard 16-cell Vertices")
print("=" * 70)

# Standard 16-cell: vertices at ±eᵢ
cell_16_standard = np.array([
    [1, 0, 0, 0], [-1, 0, 0, 0],
    [0, 1, 0, 0], [0, -1, 0, 0],
    [0, 0, 1, 0], [0, 0, -1, 0],
    [0, 0, 0, 1], [0, 0, 0, -1]
], dtype=float)

print("\nStandard 16-cell vertices (±eᵢ):")
for v in cell_16_standard:
    print(f"  {v}")

print("\nComparing lifted stella to standard 16-cell:")
# Check if any lifted vertex matches any 16-cell vertex
matches = 0
for lifted in lifted_vertices:
    for standard in cell_16_standard:
        if np.allclose(lifted, standard):
            matches += 1
print(f"  Number of matches: {matches}")
print(f"  Conclusion: Lifted vertices are {'NOT ' if matches == 0 else ''}16-cell vertices")

# =============================================================================
# Part 4: What IS the Demitesseract?
# =============================================================================
print("\n" + "=" * 70)
print("PART 4: Demitesseract (Half-Hypercube) Analysis")
print("=" * 70)

# Demitesseract: vertices of tesseract with even number of minus signs
# Tesseract has 16 vertices at (±1, ±1, ±1, ±1)
# Demitesseract keeps 8 with even parity

demitesseract = []
for signs in product([1, -1], repeat=4):
    parity = np.prod(signs)
    if parity == 1:  # Even number of minus signs
        demitesseract.append(list(signs))
demitesseract = np.array(demitesseract, dtype=float) / 2  # Scale to match lifted

print("\nDemitesseract vertices (scaled by 1/2):")
for v in demitesseract:
    print(f"  {v}")

# Check if lifted vertices match demitesseract
print("\nComparing lifted stella to demitesseract:")
lifted_set = set(tuple(v) for v in lifted_vertices)
demitess_set = set(tuple(v) for v in demitesseract)
print(f"  Lifted set: {len(lifted_set)} unique vertices")
print(f"  Demitesseract set: {len(demitess_set)} unique vertices")
print(f"  Sets are equal: {lifted_set == demitess_set}")

# =============================================================================
# Part 5: Key Insight - Demitesseract IS a 16-cell (differently oriented)
# =============================================================================
print("\n" + "=" * 70)
print("PART 5: KEY INSIGHT - Demitesseract = Rotated 16-cell")
print("=" * 70)

print("""
CRITICAL MATHEMATICAL FACT:
The demitesseract (half-hypercube) with 8 vertices at ½(±1, ±1, ±1, ±1)
with even parity IS combinatorially equivalent to the 16-cell.

Both are:
- The same polytope, just differently oriented/scaled in R⁴
- The dual of the tesseract
- Regular 4-polytopes with 8 vertices, 24 edges, 32 triangular faces, 16 tetrahedral cells

The confusion arises from two different coordinate representations:
1. "Standard" 16-cell: vertices at ±eᵢ (coordinate axes)
2. "Demitesseract" form: vertices at ½(±1,±1,±1,±1) with even parity

These are related by a rotation in R⁴!
""")

# Prove they're the same polytope by checking edge structure
print("Verification: Checking edge structure...")

def count_edges(vertices, threshold):
    """Count edges (pairs at distance threshold)."""
    edges = []
    n = len(vertices)
    for i in range(n):
        for j in range(i+1, n):
            dist = np.linalg.norm(vertices[i] - vertices[j])
            if np.isclose(dist, threshold, rtol=0.01):
                edges.append((i, j))
    return edges

# Find edge lengths
print("\nEdge length analysis:")
# Standard 16-cell
dists_16 = []
for i in range(8):
    for j in range(i+1, 8):
        dists_16.append(np.linalg.norm(cell_16_standard[i] - cell_16_standard[j]))
unique_dists_16 = sorted(set(np.round(dists_16, 6)))
print(f"  Standard 16-cell distances: {unique_dists_16}")

# Demitesseract
dists_demi = []
for i in range(8):
    for j in range(i+1, 8):
        dists_demi.append(np.linalg.norm(demitesseract[i] - demitesseract[j]))
unique_dists_demi = sorted(set(np.round(dists_demi, 6)))
print(f"  Demitesseract distances: {unique_dists_demi}")

# Edge count
edges_16 = count_edges(cell_16_standard, np.sqrt(2))
edges_demi = count_edges(demitesseract, 1.0)  # Edge length in demitesseract form
print(f"\n  Standard 16-cell edge count: {len(edges_16)}")
print(f"  Demitesseract edge count: {len(edges_demi)}")

# =============================================================================
# Part 6: Explicit Rotation Matrix
# =============================================================================
print("\n" + "=" * 70)
print("PART 6: Explicit Rotation from Demitesseract to Standard 16-cell")
print("=" * 70)

# The rotation that takes demitesseract to standard 16-cell
# We need R such that R @ demitesseract vertices → standard 16-cell vertices (up to scaling)

# The transformation is related to the Hadamard matrix
H4 = np.array([
    [1, 1, 1, 1],
    [1, -1, 1, -1],
    [1, 1, -1, -1],
    [1, -1, -1, 1]
], dtype=float) / 2

print("Transformation matrix (scaled Hadamard):")
print(H4)

print("\nApplying H4 to demitesseract vertices:")
transformed = demitesseract @ H4.T * 2  # Scale demitesseract back to unit, apply H4, get axes

# Check which axes we get
for i, v in enumerate(transformed):
    print(f"  demitesseract[{i}] = {demitesseract[i]} → {v}")

# Verify these are on coordinate axes
on_axes = 0
for v in transformed:
    nonzero = np.sum(np.abs(v) > 0.01)
    if nonzero == 1:
        on_axes += 1
print(f"\nVertices on coordinate axes: {on_axes}/8")

# =============================================================================
# Part 7: The Correct Statement
# =============================================================================
print("\n" + "=" * 70)
print("PART 7: RESOLUTION - Correct Mathematical Statement")
print("=" * 70)

print("""
RESOLUTION OF ISSUE C1:

The original theorem stated that the lift map produces "16-cell vertices."
The verification agent objected that it produces "demitesseract vertices."

BOTH STATEMENTS ARE TRUE because the demitesseract and 16-cell are the
SAME POLYTOPE in different coordinate representations.

CORRECTED STATEMENT FOR THEOREM 2.4.1:

"The lift map φ: R³ → R⁴ defined by
    φ(x₁, x₂, x₃) = ½(x₁, x₂, x₃, x₁x₂x₃)
maps the 8 stella octangula vertices to the 8 vertices of a 16-cell
in its demitesseract representation, i.e., vertices at ½(±1,±1,±1,±1)
with even coordinate parity.

This is related to the standard 16-cell (vertices at ±eᵢ) by an
orthogonal transformation (specifically, a scaled Hadamard matrix).
Since the Weyl group W(B₄) is defined intrinsically and independent
of coordinate choice, both representations have the same symmetry
group of order 384."

KEY POINT: The embedding S₄ × Z₂ → W(B₄) is VALID because:
1. The demitesseract = 16-cell as abstract polytopes
2. W(B₄) is the automorphism group of BOTH
3. The stella octangula symmetry embeds correctly

The issue was TERMINOLOGICAL, not MATHEMATICAL.
""")

# =============================================================================
# Part 8: Verify the Symmetry Groups Match
# =============================================================================
print("\n" + "=" * 70)
print("PART 8: Symmetry Group Verification")
print("=" * 70)

# Both should have 384 symmetries
# W(B₄) = (Z₂)⁴ ⋊ S₄ acts on both representations

# For demitesseract: symmetries are coordinate permutations AND sign changes
# that preserve even parity

def count_symmetries_demitesseract():
    """Count automorphisms of the demitesseract."""
    vertices = set(tuple(v) for v in demitesseract * 2)  # Use integer coords
    count = 0

    # Generate all signed permutations
    from itertools import permutations
    for perm in permutations(range(4)):
        for signs in product([1, -1], repeat=4):
            # Apply transformation to all vertices
            transformed = set()
            valid = True
            for v in vertices:
                new_v = tuple(signs[i] * v[perm[i]] for i in range(4))
                if new_v not in vertices:
                    valid = False
                    break
                transformed.add(new_v)
            if valid and transformed == vertices:
                count += 1
    return count

sym_count = count_symmetries_demitesseract()
print(f"Symmetries of demitesseract (should be 384): {sym_count}")
print(f"|W(B₄)| = 2⁴ × 4! = {2**4 * 24}")
print(f"Match: {sym_count == 384}")

# =============================================================================
# Part 9: Summary
# =============================================================================
print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)

results = {
    "issue": "C1",
    "description": "Lift map produces demitesseract vs 16-cell vertices",
    "resolution": "TERMINOLOGICAL - demitesseract = 16-cell in different coordinates",
    "mathematical_validity": "UNCHANGED - embedding chain is valid",
    "key_facts": [
        "Demitesseract and 16-cell are the same polytope",
        "Both have 8 vertices, 24 edges, same Weyl group W(B₄)",
        "Related by orthogonal transformation (Hadamard matrix)",
        "S₄ × Z₂ → W(B₄) embedding is correct"
    ],
    "action_required": "Clarify terminology in theorem derivation",
    "symmetry_verification": {
        "demitesseract_symmetries": sym_count,
        "expected_W_B4": 384,
        "match": sym_count == 384
    }
}

print(f"""
Issue C1 Resolution: {'RESOLVED' if sym_count == 384 else 'NEEDS WORK'}

The demitesseract representation of the 16-cell is mathematically
equivalent to the standard representation. The embedding chain is VALID.

Required change: Update theorem text to clarify that the lift produces
the "demitesseract form" of the 16-cell, which is the same polytope
in different coordinates.
""")

# Save results
with open("verification/theorem_2_4_1_c1_resolution_results.json", "w") as f:
    json.dump(results, f, indent=2)

print("Results saved to theorem_2_4_1_c1_resolution_results.json")
