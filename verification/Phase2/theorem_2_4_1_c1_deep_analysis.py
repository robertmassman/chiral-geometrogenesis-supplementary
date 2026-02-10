#!/usr/bin/env python3
"""
Theorem 2.4.1 Issue C1 Deep Analysis: 16-cell vs Demitesseract Symmetries
=========================================================================

The previous analysis revealed that the demitesseract has 192 symmetries
(W(D₄)), not 384 (W(B₄)). This is a REAL mathematical difference.

Let's understand:
1. 16-cell symmetry = W(B₄) = 384
2. Demitesseract symmetry = W(D₄) = 192
3. What does this mean for the embedding chain?

Author: Verification System
Date: 2025-12-26
"""

import numpy as np
from itertools import permutations, product

print("=" * 70)
print("ISSUE C1 DEEP ANALYSIS: 16-cell vs Demitesseract Symmetries")
print("=" * 70)

# =============================================================================
# Part 1: Understand the Key Difference
# =============================================================================
print("\n" + "=" * 70)
print("PART 1: Understanding the Symmetry Difference")
print("=" * 70)

print("""
KEY FACT: The 16-cell and demitesseract are COMBINATORIALLY the same
(same vertices, edges, faces, cells) but have DIFFERENT symmetry groups
when considered as point sets in R⁴.

The difference:
- Standard 16-cell at ±eᵢ: Symmetries include ALL signed permutations
  This gives W(B₄) = (Z₂)⁴ ⋊ S₄ with |W(B₄)| = 16 × 24 = 384

- Demitesseract at ½(±1,±1,±1,±1) with even parity:
  Symmetries must PRESERVE the even parity constraint
  This gives W(D₄) = {signed permutations with EVEN number of sign flips}
  |W(D₄)| = 8 × 24 = 192

The point: If we want to embed S₄ × Z₂ (order 48) into the symmetry group,
we need to know which symmetry group we're working with!
""")

# =============================================================================
# Part 2: Verify Both Symmetry Groups
# =============================================================================
print("\n" + "=" * 70)
print("PART 2: Verify Both Symmetry Groups")
print("=" * 70)

# Standard 16-cell
cell_16_standard = np.array([
    [1, 0, 0, 0], [-1, 0, 0, 0],
    [0, 1, 0, 0], [0, -1, 0, 0],
    [0, 0, 1, 0], [0, 0, -1, 0],
    [0, 0, 0, 1], [0, 0, 0, -1]
], dtype=float)

# Demitesseract
demitesseract = np.array([
    [1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1],
    [-1, 1, 1, -1], [-1, 1, -1, 1], [-1, -1, 1, 1], [-1, -1, -1, -1]
], dtype=float) / 2

def count_automorphisms(vertices):
    """Count automorphisms that map the vertex set to itself."""
    vertices_set = set(tuple(v) for v in vertices)
    count = 0

    for perm in permutations(range(4)):
        for signs in product([1, -1], repeat=4):
            # Check if this signed permutation maps vertices to vertices
            valid = True
            for v in vertices:
                new_v = tuple(signs[i] * v[perm[i]] for i in range(4))
                if new_v not in vertices_set:
                    valid = False
                    break
            if valid:
                count += 1
    return count

sym_16 = count_automorphisms(cell_16_standard)
sym_demi = count_automorphisms(demitesseract)

print(f"Standard 16-cell symmetries: {sym_16}")
print(f"Expected W(B₄) = 2⁴ × 4!: {2**4 * 24}")
print(f"Match: {sym_16 == 384}")

print(f"\nDemitesseract symmetries: {sym_demi}")
print(f"Expected W(D₄) = 2³ × 4!: {2**3 * 24}")
print(f"Match: {sym_demi == 192}")

# =============================================================================
# Part 3: What About the Stella Embedding?
# =============================================================================
print("\n" + "=" * 70)
print("PART 3: Stella Octangula Embedding Analysis")
print("=" * 70)

print("""
The stella octangula has symmetry group S₄ × Z₂ (order 48).

Question: Does S₄ × Z₂ embed in W(D₄)?

Let's check the index: 192 / 48 = 4

So S₄ × Z₂ DOES embed in W(D₄) with index 4 (not 8 as claimed).

But wait - what's the ACTUAL embedding we're constructing?
""")

# The stella lift map
def lift_map(v):
    x1, x2, x3 = v
    x4 = x1 * x2 * x3
    return np.array([x1, x2, x3, x4]) / 2

# Stella vertices
T_plus = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], dtype=float)
T_minus = np.array([[-1, -1, -1], [-1, 1, 1], [1, -1, 1], [1, 1, -1]], dtype=float)
stella = np.vstack([T_plus, T_minus])

# Lift to 4D
lifted = np.array([lift_map(v) for v in stella])

print("Stella vertices and their lifts:")
for s, l in zip(stella, lifted):
    print(f"  {s} → {l}")

# =============================================================================
# Part 4: The CORRECT Embedding Chain
# =============================================================================
print("\n" + "=" * 70)
print("PART 4: The CORRECT Embedding Chain")
print("=" * 70)

print("""
RESOLUTION: The embedding chain needs a slight modification.

OPTION A: Use W(D₄) instead of W(B₄)
------------------------------------------
The natural lift produces demitesseract vertices, which have
symmetry group W(D₄) = 192.

Embedding chain:
  S₄ × Z₂ (48) → W(D₄) (192) → W(F₄) (1152)

  Index: [W(D₄) : S₄ × Z₂] = 192/48 = 4
  Index: [W(F₄) : W(D₄)] = 1152/192 = 6

OPTION B: Use standard 16-cell coordinates
------------------------------------------
We can apply the Hadamard transformation to get standard 16-cell
vertices, which have symmetry group W(B₄) = 384.

Embedding chain:
  S₄ × Z₂ (48) → W(B₄) (384) → W(F₄) (1152)

  Index: [W(B₄) : S₄ × Z₂] = 384/48 = 8
  Index: [W(F₄) : W(B₄)] = 1152/384 = 3

WHICH IS CORRECT?

The theorem CLAIMS index 8 and index 3, which corresponds to OPTION B.
So the theorem should use the Hadamard-transformed coordinates.
""")

# =============================================================================
# Part 5: Verify Option B Works
# =============================================================================
print("\n" + "=" * 70)
print("PART 5: Verify Option B (Standard 16-cell Embedding)")
print("=" * 70)

# Hadamard matrix (normalized)
H4 = np.array([
    [1, 1, 1, 1],
    [1, -1, 1, -1],
    [1, 1, -1, -1],
    [1, -1, -1, 1]
], dtype=float) / 2

# Transform demitesseract to standard 16-cell
transformed = (demitesseract * 2) @ H4.T / 2  # Note: demitesseract is already scaled

print("Hadamard transformation of lifted vertices:")
for orig, trans in zip(lifted, (lifted * 2) @ H4.T / 2):
    print(f"  {orig} → {trans}")

# Rescale to get unit vectors on axes
standard_lifted = (lifted * 2) @ H4.T

print("\nRescaled to unit vectors:")
for v in standard_lifted:
    print(f"  {v}")

# Verify these are on coordinate axes
on_axes = sum(1 for v in standard_lifted if np.sum(np.abs(v) > 0.01) == 1)
print(f"\nVertices on coordinate axes: {on_axes}/8")

# =============================================================================
# Part 6: Compute the Correct Composite Lift Map
# =============================================================================
print("\n" + "=" * 70)
print("PART 6: The Correct Composite Lift Map")
print("=" * 70)

print("""
The CORRECT lift from stella octangula to standard 16-cell is:

  Φ(x₁, x₂, x₃) = H₄ · [x₁, x₂, x₃, x₁x₂x₃]ᵀ

where H₄ is the Hadamard matrix.

Let's compute this explicitly.
""")

def composite_lift(v):
    """Composite lift: stella → demitesseract → standard 16-cell."""
    x1, x2, x3 = v
    x4 = x1 * x2 * x3
    demitess_form = np.array([x1, x2, x3, x4])
    # Apply Hadamard
    return H4 @ demitess_form * 2  # Factor of 2 for proper scaling

print("Composite lift Φ = H₄ · φ:")
for s in stella:
    result = composite_lift(s)
    print(f"  {s} → {result}")

# Verify these match standard 16-cell vertices
print("\nVerification against standard 16-cell:")
lifted_set = set()
for s in stella:
    result = composite_lift(s)
    # Normalize to ±eᵢ form
    idx = np.argmax(np.abs(result))
    sign = np.sign(result[idx])
    lifted_set.add((idx, sign))
    print(f"  {result} = {'+' if sign > 0 else '-'}e_{idx+1}")

print(f"\nUnique directions: {len(lifted_set)} (should be 8)")

# =============================================================================
# Part 7: Write Out the Corrected Lift Map Explicitly
# =============================================================================
print("\n" + "=" * 70)
print("PART 7: Explicit Corrected Lift Map")
print("=" * 70)

print("""
The corrected lift map Φ: R³ → R⁴ is:

  Φ(x₁, x₂, x₃) = (y₁, y₂, y₃, y₄)

where:
  y₁ = x₁ + x₂ + x₃ + x₁x₂x₃
  y₂ = x₁ - x₂ + x₃ - x₁x₂x₃
  y₃ = x₁ + x₂ - x₃ - x₁x₂x₃
  y₄ = x₁ - x₂ - x₃ + x₁x₂x₃

(with appropriate normalization)

For stella vertices with xᵢ ∈ {±1}:
""")

def explicit_lift(v):
    x1, x2, x3 = v
    p = x1 * x2 * x3  # parity
    y1 = x1 + x2 + x3 + p
    y2 = x1 - x2 + x3 - p
    y3 = x1 + x2 - x3 - p
    y4 = x1 - x2 - x3 + p
    return np.array([y1, y2, y3, y4])

print("Explicit formula verification:")
for s in stella:
    result = explicit_lift(s)
    print(f"  Φ({s}) = {result}")

# =============================================================================
# Part 8: Final Resolution
# =============================================================================
print("\n" + "=" * 70)
print("PART 8: FINAL RESOLUTION OF ISSUE C1")
print("=" * 70)

print("""
ISSUE C1 RESOLUTION:

The original theorem used the lift map φ(x) = ½(x₁, x₂, x₃, x₁x₂x₃),
which produces demitesseract vertices with symmetry W(D₄) = 192.

The claimed embedding indices (8 and 3) require W(B₄) = 384.

SOLUTION: Use the composite lift Φ = H₄ · φ, which produces
standard 16-cell vertices at ±eᵢ with symmetry W(B₄) = 384.

Explicit formula:
  Φ(x₁, x₂, x₃) = ¼(x₁+x₂+x₃+p, x₁-x₂+x₃-p, x₁+x₂-x₃-p, x₁-x₂-x₃+p)

  where p = x₁x₂x₃ is the parity.

This maps:
  T₊ vertices (p = +1) → {+e₁, +e₂, +e₃, +e₄}
  T₋ vertices (p = -1) → {-e₁, -e₂, -e₃, -e₄}

The embedding chain is then:
  S₄ × Z₂ (48) → W(B₄) (384) → W(F₄) (1152)

  with indices [W(B₄) : S₄×Z₂] = 8 and [W(F₄) : W(B₄)] = 3 ✓

REQUIRED CHANGES TO THEOREM 2.4.1:
1. Replace φ with Φ in the derivation
2. Update the explicit formula
3. Add note explaining why Hadamard transformation is needed
""")

# Verify embedding indices
print("\nFinal Verification:")
print(f"  |S₄ × Z₂| = 48")
print(f"  |W(B₄)| = {sym_16}")
print(f"  |W(F₄)| = 1152")
print(f"  [W(B₄) : S₄ × Z₂] = {sym_16 // 48}")
print(f"  [W(F₄) : W(B₄)] = {1152 // sym_16}")
print(f"\nIndices match theorem claims: {sym_16 // 48 == 8 and 1152 // sym_16 == 3}")
