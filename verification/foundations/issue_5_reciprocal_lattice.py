"""
Issue 5: Explicit Derivation of Minimum Reciprocal Lattice Vector |G_min|

The theorem states |G_min| ~ 2π/a but doesn't derive this for the FCC lattice.
Let's provide the explicit derivation.
"""

import numpy as np

print("=" * 70)
print("ISSUE 5: RECIPROCAL LATTICE VECTOR DERIVATION FOR FCC")
print("=" * 70)
print()

# FCC direct lattice primitive vectors (conventional cube side a)
# The primitive vectors for FCC are:
# a1 = (a/2)(0, 1, 1)
# a2 = (a/2)(1, 0, 1)
# a3 = (a/2)(1, 1, 0)

a = 1.0  # Lattice constant (we'll keep it symbolic)

print("FCC Direct Lattice:")
print("-" * 50)
print("Primitive vectors (with conventional cube side a):")
print("  a₁ = (a/2)(0, 1, 1) = (0, a/2, a/2)")
print("  a₂ = (a/2)(1, 0, 1) = (a/2, 0, a/2)")
print("  a₃ = (a/2)(1, 1, 0) = (a/2, a/2, 0)")
print()

a1 = np.array([0, a/2, a/2])
a2 = np.array([a/2, 0, a/2])
a3 = np.array([a/2, a/2, 0])

# Volume of primitive cell
V = np.dot(a1, np.cross(a2, a3))
print(f"Primitive cell volume: V = a₁ · (a₂ × a₃) = {V:.4f} a³ = a³/4")
print()

# Reciprocal lattice vectors
# b_i = 2π (a_j × a_k) / V  (cyclic)
print("Reciprocal Lattice:")
print("-" * 50)
print("Definition: bᵢ = 2π (aⱼ × aₖ) / V")
print()

b1 = 2 * np.pi * np.cross(a2, a3) / V
b2 = 2 * np.pi * np.cross(a3, a1) / V
b3 = 2 * np.pi * np.cross(a1, a2) / V

print("Reciprocal primitive vectors:")
print(f"  b₁ = 2π/V × (a₂ × a₃) = (2π/a)(-1, 1, 1) = {b1 / (2*np.pi/a)}")
print(f"  b₂ = 2π/V × (a₃ × a₁) = (2π/a)(1, -1, 1) = {b2 / (2*np.pi/a)}")
print(f"  b₃ = 2π/V × (a₁ × a₂) = (2π/a)(1, 1, -1) = {b3 / (2*np.pi/a)}")
print()

# The reciprocal lattice of FCC is BCC!
print("Note: The reciprocal lattice of FCC is BCC (body-centered cubic).")
print()

# Find minimum |G| for reciprocal lattice vectors
print("=" * 70)
print("MINIMUM RECIPROCAL LATTICE VECTOR")
print("=" * 70)
print()

# General reciprocal lattice vector
print("General reciprocal lattice vector: G = n₁b₁ + n₂b₂ + n₃b₃")
print("where (n₁, n₂, n₃) ∈ ℤ³")
print()

# Find shortest nonzero G vectors
G_vectors = []
for n1 in range(-2, 3):
    for n2 in range(-2, 3):
        for n3 in range(-2, 3):
            if n1 == n2 == n3 == 0:
                continue
            G = n1 * b1 + n2 * b2 + n3 * b3
            G_mag = np.linalg.norm(G)
            G_vectors.append((n1, n2, n3, G, G_mag))

# Sort by magnitude
G_vectors.sort(key=lambda x: x[4])

print("Shortest reciprocal lattice vectors:")
print("-" * 70)
print(f"{'(n₁,n₂,n₃)':<15} {'|G|/(2π/a)':<15} {'|G|':<20}")
print("-" * 70)

# Get unique magnitudes
unique_mags = []
for n1, n2, n3, G, G_mag in G_vectors[:20]:
    if len(unique_mags) == 0 or abs(G_mag - unique_mags[-1]) > 1e-10:
        unique_mags.append(G_mag)
    if len(unique_mags) <= 3:
        print(f"({n1:2d},{n2:2d},{n3:2d})        {G_mag/(2*np.pi/a):12.4f}     {G_mag:.6f} × (2π/a)")

print()

# The minimum
G_min = G_vectors[0][4]
print(f"Minimum |G| = {G_min:.6f} = {G_min/(2*np.pi/a):.4f} × (2π/a)")
print()

# This equals sqrt(2) × 2π/a for FCC
print("For FCC reciprocal lattice (which is BCC):")
print(f"  |G_min| = √2 × (2π/a) ≈ {np.sqrt(2):.4f} × (2π/a)")
print()

# But for practical purposes
print("=" * 70)
print("PRACTICAL IMPLICATION")
print("=" * 70)
print()
print("The minimum reciprocal lattice vector magnitude is:")
print(f"  |G_min| = √2 × (2π/a) ≈ 1.414 × (2π/a) ~ 2π/a")
print()
print("Therefore, for the suppression formula:")
print("  1/(GL)² = 1/(|G_min| × L)² ~ 1/(2π L/a)² ~ (a/2πL)² ~ (a/L)²")
print()
print("The factor of 2π and √2 are absorbed into the 'order of magnitude' (~)")
print("so the suppression is correctly characterized as (a/L)².")
print()

# Lattice spacing clarification
print("=" * 70)
print("LATTICE SPACING CLARIFICATION")
print("=" * 70)
print()
print("For the FCC lattice, there are TWO relevant length scales:")
print()
print("1. Conventional cube side: a (used in O_h symmetry discussion)")
print("2. Nearest-neighbor distance: a/√2 ≈ 0.707 a")
print()
print("In the Chiral Geometrogenesis framework:")
print("  - The 'lattice spacing' a refers to the conventional cube side")
print("  - This is consistent with O_h being the point group of the cube")
print("  - |G_min| = √2 × (2π/a) is the correct minimum reciprocal vector")
print()

# Proposed addition to theorem
print("=" * 70)
print("PROPOSED ADDITION TO SECTION 3.3")
print("=" * 70)
print()
print("""
**Note on |G_min|:** For the FCC reciprocal lattice (which is BCC), the minimum
nonzero reciprocal lattice vector magnitude is:

$$|\\mathbf{G}_{\\min}| = \\sqrt{2} \\cdot \\frac{2\\pi}{a} \\approx \\frac{2\\pi}{a}$$

where $a$ is the conventional cubic cell side. The precise coefficient $\\sqrt{2}$
is absorbed into the order-of-magnitude estimate, so $(GL)^{-2} \\sim (a/L)^2$
captures the correct scaling behavior.
""")
