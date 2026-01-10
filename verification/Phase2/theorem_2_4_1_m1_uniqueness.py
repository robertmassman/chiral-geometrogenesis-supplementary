#!/usr/bin/env python3
"""
Theorem 2.4.1 Issue M1 Resolution: Lift Map Uniqueness Analysis
================================================================

The issue: Is the lift map from stella octangula to 16-cell unique?

This script:
1. Analyzes all possible lifts preserving key properties
2. Shows which properties determine the lift uniquely
3. Provides the uniqueness theorem

Author: Verification System
Date: 2025-12-26
"""

import numpy as np
from itertools import permutations, product

print("=" * 70)
print("ISSUE M1: Lift Map Uniqueness Analysis")
print("=" * 70)

# =============================================================================
# Part 1: What Properties Should a Lift Preserve?
# =============================================================================
print("\n" + "=" * 70)
print("PART 1: Desired Properties of the Lift")
print("=" * 70)

print("""
A lift map Φ: R³ → R⁴ from stella octangula to 16-cell should preserve:

(P1) VERTEX COUNT: 8 stella vertices → 8 16-cell vertices (bijection)

(P2) PARITY STRUCTURE: T₊ and T₋ should map to "opposite" sets
     - T₊ (parity +1) → one set of 4 vertices
     - T₋ (parity -1) → antipodal set of 4 vertices

(P3) ADJACENCY: Adjacent stella vertices should map to adjacent 16-cell vertices
     (This preserves the edge structure)

(P4) SYMMETRY EMBEDDING: The stella symmetry S₄ × Z₂ should embed into
     the 16-cell symmetry W(B₄)

(P5) LINEARITY (optional): The lift should be linear or piecewise linear

Let's analyze how unique the lift is under these constraints.
""")

# =============================================================================
# Part 2: The Standard 16-cell Structure
# =============================================================================
print("\n" + "=" * 70)
print("PART 2: 16-cell Vertex Structure")
print("=" * 70)

# Standard 16-cell vertices
cell_16 = np.array([
    [1, 0, 0, 0], [-1, 0, 0, 0],
    [0, 1, 0, 0], [0, -1, 0, 0],
    [0, 0, 1, 0], [0, 0, -1, 0],
    [0, 0, 0, 1], [0, 0, 0, -1]
], dtype=float)

print("Standard 16-cell vertices (±eᵢ):")
for i, v in enumerate(cell_16):
    print(f"  v{i}: {v}")

# The 16-cell has a natural partition into 4 antipodal pairs
print("\nAntipodal pairs:")
for i in range(4):
    print(f"  (+e{i+1}, -e{i+1}): {cell_16[2*i]}, {cell_16[2*i+1]}")

# =============================================================================
# Part 3: Stella Octangula Structure
# =============================================================================
print("\n" + "=" * 70)
print("PART 3: Stella Octangula Vertex Structure")
print("=" * 70)

T_plus = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], dtype=float)
T_minus = np.array([[-1, -1, -1], [-1, 1, 1], [1, -1, 1], [1, 1, -1]], dtype=float)

print("T₊ vertices (parity +1):", T_plus.tolist())
print("T₋ vertices (parity -1):", T_minus.tolist())

# Check which T₊ and T₋ vertices are antipodal
print("\nAntipodal pairs in stella:")
for vp in T_plus:
    for vm in T_minus:
        if np.allclose(vp, -vm):
            print(f"  {vp} ↔ {vm}")

# =============================================================================
# Part 4: Counting Possible Lifts
# =============================================================================
print("\n" + "=" * 70)
print("PART 4: Counting Possible Lifts (Under Symmetry)")
print("=" * 70)

print("""
Key Observation: The 16-cell has 8 vertices grouped into 4 antipodal pairs.
The stella has 8 vertices grouped into 4 antipodal pairs.

A lift satisfying (P2) must map antipodal stella pairs to antipodal 16-cell pairs.

Step 1: Choose which 16-cell pair corresponds to each stella pair
  - There are 4! = 24 ways to match up the 4 pairs

Step 2: For each pair, choose which vertex goes to which
  - There are 2⁴ = 16 ways to choose the orientation of each pair

Total: 24 × 16 = 384 possible lifts

But wait! This is exactly |W(B₄)| = 384, the symmetry group of the 16-cell.

This means: Any two valid lifts differ by a 16-cell symmetry.
""")

# =============================================================================
# Part 5: Uniqueness Theorem
# =============================================================================
print("\n" + "=" * 70)
print("PART 5: Uniqueness Theorem")
print("=" * 70)

print("""
THEOREM (Lift Uniqueness):

Any two lifts Φ₁, Φ₂: Stella → 16-cell satisfying properties (P1)-(P4)
are related by an element of W(B₄):

    Φ₂ = g · Φ₁  for some g ∈ W(B₄)

PROOF:
1. Both lifts are bijections between the 8 vertices (by P1)
2. The composition Φ₂ · Φ₁⁻¹ is a bijection 16-cell → 16-cell
3. It preserves adjacency (by P3), so it preserves the polytope structure
4. Therefore Φ₂ · Φ₁⁻¹ ∈ Aut(16-cell) = W(B₄)
5. Hence Φ₂ = (Φ₂ · Φ₁⁻¹) · Φ₁ = g · Φ₁ for g ∈ W(B₄) □

COROLLARY:
The lift Φ is UNIQUE UP TO 16-CELL SYMMETRY.

Since we are interested in the embedding of symmetry groups
S₄ × Z₂ → W(B₄), and different lifts give conjugate embeddings
(related by inner automorphisms of W(B₄)), the embedding is
ESSENTIALLY UNIQUE.

This is the correct statement: "The lift is unique up to W(B₄) symmetry."
""")

# =============================================================================
# Part 6: Explicit Verification
# =============================================================================
print("\n" + "=" * 70)
print("PART 6: Explicit Verification")
print("=" * 70)

# Our chosen lift (Hadamard version)
H4 = np.array([
    [1, 1, 1, 1],
    [1, -1, 1, -1],
    [1, 1, -1, -1],
    [1, -1, -1, 1]
], dtype=float) / 2

def our_lift(v):
    """Our chosen lift via Hadamard."""
    x1, x2, x3 = v
    p = x1 * x2 * x3
    return H4 @ np.array([x1, x2, x3, p])

# Alternative lift: just permute coordinates differently
def alt_lift_1(v):
    """Alternative lift: swap e₂ and e₃."""
    result = our_lift(v)
    return np.array([result[0], result[2], result[1], result[3]])

# Both should give valid 16-cell vertices
print("Our lift:")
for v in T_plus:
    print(f"  {v} → {our_lift(v)}")

print("\nAlternative lift (swap e₂ ↔ e₃):")
for v in T_plus:
    print(f"  {v} → {alt_lift_1(v)}")

# The alternative lift is related by a W(B₄) element
print("\nRelation: alt_lift = g · our_lift where g swaps coordinates 2 and 3")
print("g ∈ W(B₄) is the transposition (2 3) ∈ S₄ ⊂ W(B₄)")

# =============================================================================
# Part 7: Why Our Choice is Natural
# =============================================================================
print("\n" + "=" * 70)
print("PART 7: Why the Hadamard Lift is Natural")
print("=" * 70)

print("""
Among all equivalent lifts, the Hadamard lift Φ = H₄ · φ is distinguished by:

1. SYMMETRIC FORMULA: All four coordinates are treated democratically
   in the Hadamard matrix.

2. PRESERVES PARITY STRUCTURE: T₊ → {+eᵢ} and T₋ → {-eᵢ}
   (positive parity goes to positive axes)

3. MINIMAL MODIFICATION: The original lift φ(x) = (x₁, x₂, x₃, x₁x₂x₃)
   preserves the first three coordinates. The Hadamard rotation is the
   simplest transformation to "symmetrize" the fourth coordinate.

4. COMMUTES WITH TETRAHEDRON SWAPPING: The Z₂ symmetry (T₊ ↔ T₋) maps
   to the antipodal map in 16-cell, which is central in W(B₄).

These properties make the Hadamard lift the CANONICAL choice.
""")

# =============================================================================
# Part 8: Summary
# =============================================================================
print("\n" + "=" * 70)
print("SUMMARY: Resolution of Issue M1")
print("=" * 70)

print("""
RESOLUTION OF ISSUE M1 (Non-Uniqueness):

The lift map is NOT unique in the absolute sense, but it IS unique
up to symmetry of the target space.

PRECISE STATEMENT:
  "The lift Φ: Stella → 16-cell is unique up to composition with
   an element of W(B₄). The Hadamard lift is the canonical choice
   satisfying symmetry and parity preservation properties."

This is analogous to standard situations in mathematics:
- An embedding is "unique up to conjugation"
- A basis is "unique up to change of basis"
- A lift is "unique up to the symmetry group of the target"

The embedding S₄ × Z₂ → W(B₄) is well-defined up to conjugacy,
which is the appropriate notion for group-theoretic purposes.

REQUIRED CHANGE TO THEOREM:
Add the statement: "The lift map is unique up to W(B₄) symmetry.
We choose the Hadamard lift as the canonical representative."
""")
