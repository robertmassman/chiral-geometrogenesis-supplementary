"""
Issue 5: Explicit Derivation of Minimum Reciprocal Lattice Vector |G_min|
CORRECTED VERSION
"""

import numpy as np

print("=" * 70)
print("ISSUE 5: RECIPROCAL LATTICE VECTOR DERIVATION FOR FCC (CORRECTED)")
print("=" * 70)
print()

# FCC direct lattice primitive vectors (conventional cube side a)
a = 1.0  # Lattice constant

# FCC primitive vectors
a1 = np.array([0, a/2, a/2])
a2 = np.array([a/2, 0, a/2])
a3 = np.array([a/2, a/2, 0])

print("FCC Direct Lattice Primitive Vectors:")
print(f"  a₁ = (a/2)(0, 1, 1)")
print(f"  a₂ = (a/2)(1, 0, 1)")
print(f"  a₃ = (a/2)(1, 1, 0)")
print()

# Volume of primitive cell
V = np.dot(a1, np.cross(a2, a3))
print(f"Primitive cell volume: V = {V:.4f} = a³/4")
print()

# Reciprocal lattice vectors: b_i = 2π (a_j × a_k) / V
b1 = 2 * np.pi * np.cross(a2, a3) / V
b2 = 2 * np.pi * np.cross(a3, a1) / V
b3 = 2 * np.pi * np.cross(a1, a2) / V

print("Reciprocal Lattice Primitive Vectors (BCC structure):")
print(f"  b₁ = (2π/a)(-1, 1, 1)  |b₁| = √3 × (2π/a)")
print(f"  b₂ = (2π/a)(1, -1, 1)  |b₂| = √3 × (2π/a)")
print(f"  b₃ = (2π/a)(1, 1, -1)  |b₃| = √3 × (2π/a)")
print()

# Verify
print("Numerical verification:")
print(f"  |b₁| = {np.linalg.norm(b1):.6f} = {np.linalg.norm(b1)/(2*np.pi):.4f} × (2π/a)")
print(f"  √3 × (2π/a) = {np.sqrt(3) * 2 * np.pi:.6f}")
print()

# Find shortest G vectors
print("=" * 70)
print("SHORTEST RECIPROCAL LATTICE VECTORS")
print("=" * 70)
print()

G_list = []
for n1 in range(-2, 3):
    for n2 in range(-2, 3):
        for n3 in range(-2, 3):
            if n1 == n2 == n3 == 0:
                continue
            G = n1 * b1 + n2 * b2 + n3 * b3
            G_mag = np.linalg.norm(G)
            G_list.append((n1, n2, n3, G_mag))

G_list.sort(key=lambda x: x[3])

# Get the first shell of shortest vectors
G_min_mag = G_list[0][3]
print(f"Minimum |G| = {G_min_mag:.6f} = {G_min_mag/(2*np.pi):.4f} × (2π/a)")
print()

# Count vectors in first shell
first_shell = [(n1, n2, n3, mag) for n1, n2, n3, mag in G_list if abs(mag - G_min_mag) < 1e-10]
print(f"First shell: {len(first_shell)} vectors at |G| = √3 × (2π/a)")
print()

# These are the 8 vectors (±1, ±1, ±1) type in BCC reciprocal space
print("First shell vectors (indices):")
for n1, n2, n3, mag in first_shell:
    print(f"  ({n1:2d}, {n2:2d}, {n3:2d})")

print()
print("=" * 70)
print("PHYSICAL INTERPRETATION")
print("=" * 70)
print()

print(f"|G_min| = √3 × (2π/a) ≈ {np.sqrt(3):.3f} × (2π/a)")
print()
print("For the suppression formula:")
print(f"  1/(G_min × L)² = 1/(√3 × 2πL/a)² = (a/(√3 × 2πL))²")
print(f"                 = (1/(√3 × 2π))² × (a/L)²")
print(f"                 ≈ (1/{np.sqrt(3)*2*np.pi:.2f})² × (a/L)²")
print(f"                 ≈ {1/(np.sqrt(3)*2*np.pi)**2:.4f} × (a/L)²")
print()
print("Since 1/(√3 × 2π)² ≈ 0.008 ~ O(0.01), the suppression is:")
print("  |⟨e^{iG·x}⟩_L| ~ 0.01 × (a/L)² ~ (a/L)²")
print()
print("The numerical prefactor ~0.01 is absorbed into the order-of-magnitude (~)")
print()

print("=" * 70)
print("CORRECTED FORMULATION FOR SECTION 3.2/3.3")
print("=" * 70)
print()
print("""
**FCC Reciprocal Lattice:**

The reciprocal lattice of the FCC direct lattice is body-centered cubic (BCC).
The reciprocal primitive vectors are:

$$\\mathbf{b}_1 = \\frac{2\\pi}{a}(-1, 1, 1), \\quad
  \\mathbf{b}_2 = \\frac{2\\pi}{a}(1, -1, 1), \\quad
  \\mathbf{b}_3 = \\frac{2\\pi}{a}(1, 1, -1)$$

The minimum nonzero reciprocal lattice vector magnitude is:

$$|\\mathbf{G}_{\\min}| = |\\mathbf{b}_1| = \\sqrt{3} \\cdot \\frac{2\\pi}{a} \\approx 10.88/a$$

For the Fourier component suppression, this gives:

$$\\frac{1}{(G_{\\min} L)^2} = \\frac{1}{12\\pi^2} \\left(\\frac{a}{L}\\right)^2 \\approx 0.008 \\left(\\frac{a}{L}\\right)^2$$

Since the numerical prefactor is $O(10^{-2})$, the suppression is correctly characterized
as order $(a/L)^2$.
""")
