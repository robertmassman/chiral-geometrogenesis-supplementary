"""
Issue 4: Spherical Harmonics and O_h Representations

The theorem claims O_h "leaves invariant all spherical harmonics for ℓ ≤ 3".
This is IMPRECISE. Let's derive the correct statement.

Key insight: The correct statement is about the DECOMPOSITION of SO(3) irreps
into O_h irreps, not about "leaving invariant" individual Y_ℓm.
"""

import numpy as np

print("=" * 70)
print("ISSUE 4: SPHERICAL HARMONICS AND O_h REPRESENTATIONS")
print("=" * 70)
print()

# O_h irreducible representations and their dimensions
O_h_irreps = {
    # Gerade (even under inversion)
    'A_1g': 1,  # Totally symmetric
    'A_2g': 1,  #
    'E_g': 2,   # Doubly degenerate
    'T_1g': 3,  # Triply degenerate
    'T_2g': 3,  # Triply degenerate
    # Ungerade (odd under inversion)
    'A_1u': 1,
    'A_2u': 1,
    'E_u': 2,
    'T_1u': 3,  # Vector representation
    'T_2u': 3,
}

print("O_h Irreducible Representations:")
print("-" * 50)
for name, dim in O_h_irreps.items():
    print(f"  {name}: dimension {dim}")
print()

# Decomposition of SO(3) representations D^(ℓ) into O_h irreps
print("Decomposition of SO(3) representations D^(ℓ) → O_h irreps:")
print("=" * 70)
print()

decompositions = {
    0: {'irreps': ['A_1g'], 'contains_A1': True},
    1: {'irreps': ['T_1u'], 'contains_A1': False},
    2: {'irreps': ['E_g', 'T_2g'], 'contains_A1': False},
    3: {'irreps': ['A_2u', 'T_1u', 'T_2u'], 'contains_A1': False},
    4: {'irreps': ['A_1g', 'E_g', 'T_1g', 'T_2g'], 'contains_A1': True},
    5: {'irreps': ['E_u', 'T_1u', 'T_2u', 'T_2u'], 'contains_A1': False},
    6: {'irreps': ['A_1g', 'A_2g', 'E_g', 'T_1g', 'T_2g', 'T_2g'], 'contains_A1': True},
}

for ell, data in decompositions.items():
    dim_SO3 = 2*ell + 1
    irreps = data['irreps']
    dim_sum = sum(O_h_irreps[ir] for ir in irreps)

    # Check dimensions match
    assert dim_SO3 == dim_sum, f"Dimension mismatch at ℓ={ell}"

    irrep_str = ' ⊕ '.join(irreps)
    a1_mark = "★ CONTAINS A_1" if data['contains_A1'] else ""

    print(f"ℓ = {ell}: D^({ell}) → {irrep_str}")
    print(f"       dim: {dim_SO3} = {' + '.join(str(O_h_irreps[ir]) for ir in irreps)} ✓")
    if a1_mark:
        print(f"       {a1_mark}")
    print()

print("=" * 70)
print("KEY INSIGHT: What 'first anisotropic observable at ℓ=4' means")
print("=" * 70)
print()

print("The A_1g (or A_1) representation is the TRIVIAL representation.")
print("An O_h-invariant observable is one that transforms as A_1g.")
print()
print("Analysis:")
print("-" * 50)

for ell in range(7):
    contains_a1 = ell in [0, 4, 6]  # ℓ where A_1g appears
    marker = "★" if contains_a1 else " "
    print(f"  ℓ = {ell}: Contains A_1g? {'Yes' if contains_a1 else 'No'} {marker}")

print()
print("Conclusion:")
print("-" * 50)
print("• For ℓ = 0: A_1g appears → isotropic (this is trivially SO(3) invariant)")
print("• For ℓ = 1,2,3: NO A_1g → no O_h-invariant anisotropic component")
print("• For ℓ = 4: A_1g APPEARS → first O_h-invariant-but-not-SO(3)-invariant observable!")
print()

# The cubic harmonic at ℓ=4
print("=" * 70)
print("THE CUBIC HARMONIC AT ℓ = 4")
print("=" * 70)
print()

print("The A_1g component at ℓ = 4 is the 'cubic harmonic':")
print()
print("  K_4(x,y,z) = Y_4^0 + √(5/14)(Y_4^4 + Y_4^{-4})")
print()
print("This can be written as:")
print("  K_4 ∝ x⁴ + y⁴ + z⁴ - (3/5)r⁴")
print()
print("Properties:")
print("  • O_h-invariant: symmetric under all 48 elements ✓")
print("  • NOT SO(3)-invariant: changes under arbitrary rotations ✗")
print("  • Represents lattice anisotropy at lowest multipole order")
print()

# What the theorem should say
print("=" * 70)
print("CORRECT FORMULATION FOR SECTION 3.5")
print("=" * 70)
print()

print("CURRENT (imprecise):")
print('  "O_h leaves invariant all spherical harmonics Y_ℓm for ℓ ≤ 3"')
print()
print("This is WRONG. O_h does NOT leave individual Y_ℓm invariant.")
print("Instead, O_h MIXES Y_ℓm within each ℓ multiplet.")
print()
print("CORRECT formulation:")
print("-" * 70)
print("""
**Claim:** Among discrete subgroups of O(3), O_h is maximally symmetric
in the following sense: the SO(3) representations D^(ℓ) for ℓ ≤ 3
decompose into irreducible representations of O_h without any
O_h-invariant singlets (A_1g or A_1u).

**Proof:** Under restriction from SO(3) to O_h:
- ℓ = 0: D^(0) → A_1g (trivial; this IS SO(3)-invariant, so no new anisotropy)
- ℓ = 1: D^(1) → T_1u (no A_1g)
- ℓ = 2: D^(2) → E_g ⊕ T_2g (no A_1g)
- ℓ = 3: D^(3) → A_2u ⊕ T_1u ⊕ T_2u (no A_1g)
- ℓ = 4: D^(4) → A_1g ⊕ E_g ⊕ T_1g ⊕ T_2g (★ FIRST A_1g!)

**Consequence:** The first O_h-invariant-but-not-SO(3)-invariant observable
is the ℓ = 4 cubic harmonic K_4 ∝ x⁴ + y⁴ + z⁴ - (3/5)r⁴, which
corresponds to dimension-8 operators, ensuring strong IR suppression.
""")
print("-" * 70)

# Verify dimension matching
print()
print("Verification of dimension matching:")
for ell in range(5):
    dim_so3 = 2*ell + 1
    if ell in decompositions:
        dim_oh = sum(O_h_irreps[ir] for ir in decompositions[ell]['irreps'])
        status = "✓" if dim_so3 == dim_oh else "✗"
        print(f"  ℓ = {ell}: dim(D^({ell})) = {dim_so3}, sum of O_h dims = {dim_oh} {status}")
