"""
Issue 1: Verify D_6h Group Order

The theorem states D_6h has "12 elements" but we need to verify the correct order.
"""

import numpy as np

print("=" * 70)
print("ISSUE 1: D_6h GROUP ORDER VERIFICATION")
print("=" * 70)
print()

# D_6h is the point group of the graphene honeycomb lattice
# It is the symmetry group of a regular hexagonal prism

print("D_6h Group Structure Analysis")
print("-" * 50)
print()

# The group D_6h can be constructed as:
# D_6h = D_6 × C_s  (direct product with horizontal mirror)
# Or equivalently: D_6h = D_6 ⊗ {E, σ_h}

print("Construction: D_6h = D_6 × C_s")
print()

# D_6 subgroup elements:
print("D_6 subgroup (order 12):")
print("  - E: identity")
print("  - C_6, C_6^2=C_3, C_6^3=C_2, C_6^4=C_3^2, C_6^5: rotations about 6-fold axis (5 elements)")
print("  - 3 C_2': 2-fold axes through opposite vertices")
print("  - 3 C_2'': 2-fold axes through midpoints of opposite edges")
print("  Total D_6 elements: 1 + 5 + 3 + 3 = 12")
print()

# C_s subgroup:
print("C_s factor (order 2):")
print("  - E: identity")
print("  - σ_h: horizontal mirror plane")
print()

# Direct product:
print("D_6h = D_6 × C_s:")
print("  Order = |D_6| × |C_s| = 12 × 2 = 24")
print()

# Explicit enumeration of D_6h elements:
print("Complete D_6h element list (24 elements):")
print("-" * 50)

elements = []

# Proper rotations (from D_6)
proper_rotations = [
    "E (identity)",
    "C_6 (60° rotation)",
    "C_3 = C_6² (120° rotation)",
    "C_2 = C_6³ (180° rotation)",
    "C_3² = C_6⁴ (240° rotation)",
    "C_6⁵ (300° rotation)",
    "C_2'(1) (2-fold through vertices, axis 1)",
    "C_2'(2) (2-fold through vertices, axis 2)",
    "C_2'(3) (2-fold through vertices, axis 3)",
    "C_2''(1) (2-fold through edges, axis 1)",
    "C_2''(2) (2-fold through edges, axis 2)",
    "C_2''(3) (2-fold through edges, axis 3)",
]

# Improper rotations (proper × σ_h)
improper_rotations = [
    "σ_h (horizontal mirror)",
    "S_6 = C_6 × σ_h (improper 6-fold)",
    "S_3 = C_3 × σ_h (improper 3-fold)",
    "i = C_2 × σ_h (inversion)",
    "S_3² = C_3² × σ_h",
    "S_6⁵ = C_6⁵ × σ_h",
    "σ_v(1) = C_2'(1) × σ_h (vertical mirror 1)",
    "σ_v(2) = C_2'(2) × σ_h (vertical mirror 2)",
    "σ_v(3) = C_2'(3) × σ_h (vertical mirror 3)",
    "σ_d(1) = C_2''(1) × σ_h (dihedral mirror 1)",
    "σ_d(2) = C_2''(2) × σ_h (dihedral mirror 2)",
    "σ_d(3) = C_2''(3) × σ_h (dihedral mirror 3)",
]

print("Proper rotations (12):")
for i, elem in enumerate(proper_rotations, 1):
    print(f"  {i:2d}. {elem}")

print()
print("Improper rotations (12):")
for i, elem in enumerate(improper_rotations, 1):
    print(f"  {i:2d}. {elem}")

print()
print(f"TOTAL: {len(proper_rotations) + len(improper_rotations)} elements")
print()

# Verify using character table dimension sum
print("Verification via Burnside's theorem:")
print("-" * 50)

# D_6h irreducible representations
irreps_D6h = {
    'A_1g': 1, 'A_2g': 1, 'B_1g': 1, 'B_2g': 1, 'E_1g': 2, 'E_2g': 2,
    'A_1u': 1, 'A_2u': 1, 'B_1u': 1, 'B_2u': 1, 'E_1u': 2, 'E_2u': 2,
}

print("D_6h irreducible representations:")
for name, dim in irreps_D6h.items():
    print(f"  {name}: dimension {dim}")

dim_squared_sum = sum(d**2 for d in irreps_D6h.values())
print()
print(f"Sum of (dimension)²: {dim_squared_sum}")
print(f"By Burnside: this equals |G| = {dim_squared_sum}")
print()

# Comparison with theorem claim
print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("THEOREM STATES: D_6h has 12 elements")
print("CORRECT VALUE:  D_6h has 24 elements")
print()
print("The error likely comes from confusing D_6h with D_6.")
print("  - D_6 (chiral dihedral group of order 6): 12 elements")
print("  - D_6h (full hexagonal group with mirrors): 24 elements")
print()
print("Graphene's point group is D_6h (includes horizontal mirror σ_h),")
print("NOT just D_6.")
print()
print("FIX REQUIRED: Change '(12 elements)' to '(24 elements)' in Section 4.3")
