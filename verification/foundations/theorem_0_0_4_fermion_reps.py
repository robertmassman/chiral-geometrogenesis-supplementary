#!/usr/bin/env python3
"""
Theorem 0.0.4 Issue C2: Verify SU(5) Fermion Representations

This script verifies the correct assignment of Standard Model fermions
to SU(5) multiplets, correcting the error in Table 3.6.1c.

The correct assignments are:
- 5̄ = (3̄,1)_{1/3} ⊕ (1,2)_{-1/2}  → d_R^c, (ν_L, e_L)
- 10 = (3,2)_{1/6} ⊕ (3̄,1)_{-2/3} ⊕ (1,1)_1  → Q_L, u_R^c, e_R^c

Author: Verification Agent
Date: 2025-12-26
"""

import numpy as np

print("="*70)
print("ISSUE C2: Verifying SU(5) Fermion Representations")
print("="*70)

# =============================================================================
# PART 1: The 5̄ Representation
# =============================================================================
print("\n" + "="*70)
print("PART 1: The 5̄ Representation of SU(5)")
print("="*70)

print("""
The fundamental representation 5 of SU(5) decomposes under SU(3)×SU(2)×U(1) as:

    5 = (3,1)_{-1/3} ⊕ (1,2)_{1/2}

The conjugate 5̄ is therefore:

    5̄ = (3̄,1)_{1/3} ⊕ (1,2)_{-1/2}

Physical content of 5̄:
    - (3̄,1)_{1/3}: Color anti-triplet, weak singlet, Y=+1/3
                   This is d_R^c (charge conjugate of right-handed down quark)
                   Has electric charge Q = T_3 + Y = 0 + 1/3 = +1/3 ✓
                   (The d_R^c has charge +1/3, conjugate of d_R with -1/3)

    - (1,2)_{-1/2}: Color singlet, weak doublet, Y=-1/2
                   This is the left-handed lepton doublet (ν_L, e_L)
                   ν_L: Q = +1/2 + (-1/2) = 0 ✓
                   e_L: Q = -1/2 + (-1/2) = -1 ✓

Dimension check: 3 + 2 = 5 ✓
""")

# Verify dimensions
dim_5bar = 5
decomp_5bar = 3 + 2
print(f"5̄ dimension check: {dim_5bar} = {decomp_5bar} ✓")

# =============================================================================
# PART 2: The 10 Representation
# =============================================================================
print("\n" + "="*70)
print("PART 2: The 10 Representation of SU(5)")
print("="*70)

print("""
The antisymmetric tensor representation 10 of SU(5) decomposes as:

    10 = (3,2)_{1/6} ⊕ (3̄,1)_{-2/3} ⊕ (1,1)_1

Physical content of 10:
    - (3,2)_{1/6}: Color triplet, weak doublet, Y=+1/6
                  This is the LEFT-HANDED QUARK DOUBLET Q_L = (u_L, d_L)
                  u_L: Q = +1/2 + 1/6 = +2/3 ✓
                  d_L: Q = -1/2 + 1/6 = -1/3 ✓

    - (3̄,1)_{-2/3}: Color anti-triplet, weak singlet, Y=-2/3
                   This is u_R^c (charge conjugate of right-handed up quark)
                   Q = 0 + (-2/3) = -2/3
                   (The u_R^c has charge -2/3, conjugate of u_R with +2/3) ✓

    - (1,1)_1: Color singlet, weak singlet, Y=+1
              This is e_R^c (charge conjugate of right-handed electron)
              Q = 0 + 1 = +1
              (The e_R^c has charge +1, conjugate of e_R with -1) ✓

Dimension check: 6 + 3 + 1 = 10 ✓
  where (3,2) has dimension 3×2 = 6
""")

# Verify dimensions
dim_10 = 10
decomp_10 = 6 + 3 + 1  # (3,2) + (3̄,1) + (1,1)
print(f"10 dimension check: {dim_10} = {decomp_10} ✓")

# =============================================================================
# PART 3: The ERROR in the Original Table
# =============================================================================
print("\n" + "="*70)
print("PART 3: Identifying the Error")
print("="*70)

print("""
ORIGINAL TABLE 3.6.1c (INCORRECT):
| SM Representation      | SU(5) Origin |
|------------------------|--------------|
| (3,2)_{1/6} (left Q)   | 5̄           |  ← ERROR!
| (3̄,1)_{-2/3} (right u)| 10          |  ← correct
| (3̄,1)_{1/3} (right d) | 5̄           |  ← correct
| (1,2)_{-1/2} (left L)  | 5̄           |  ← correct
| (1,1)_1 (right e)      | 10          |  ← correct

THE ERROR:
Left-handed quarks (3,2)_{1/6} are listed as coming from 5̄.
But 5̄ = (3̄,1)_{1/3} ⊕ (1,2)_{-1/2} does NOT contain (3,2).

The 5̄ contains:
  - (3̄,1)_{1/3}: anti-triplet, NOT triplet
  - (1,2)_{-1/2}: doublet, but color singlet

The LEFT-HANDED QUARK DOUBLET (3,2)_{1/6} must come from the 10!
""")

# =============================================================================
# PART 4: The CORRECTED Table
# =============================================================================
print("\n" + "="*70)
print("PART 4: Corrected Table")
print("="*70)

print("""
CORRECTED TABLE 3.6.1c:
| SM Representation       | SU(5) Origin | 24-cell Structure |
|-------------------------|--------------|-------------------|
| (3,2)_{1/6} (left Q_L)  | **10**       | 2-faces           |
| (3̄,1)_{-2/3} (u_R^c)   | 10           | 2-faces           |
| (3̄,1)_{1/3} (d_R^c)    | 5̄           | 5-simplex vertex  |
| (1,2)_{-1/2} (L_L)      | 5̄           | 5-simplex edge    |
| (1,1)_1 (e_R^c)         | 10           | 2-faces           |

Verification:
- 5̄ content: (3̄,1)_{1/3} + (1,2)_{-1/2} = 3 + 2 = 5 ✓
- 10 content: (3,2)_{1/6} + (3̄,1)_{-2/3} + (1,1)_1 = 6 + 3 + 1 = 10 ✓
- Total: 5 + 10 = 15 fermions per generation ✓

Note: We use charge conjugates (ψ^c) for right-handed fields so that
all fields in 5̄ and 10 are LEFT-HANDED. This is the standard convention.
""")

# =============================================================================
# PART 5: Electric Charge Verification
# =============================================================================
print("\n" + "="*70)
print("PART 5: Electric Charge Formula Q = T_3 + Y")
print("="*70)

# Define the particles and verify Q = T_3 + Y
particles = [
    # (name, T_3, Y, expected Q)
    ("u_L", 1/2, 1/6, 2/3),
    ("d_L", -1/2, 1/6, -1/3),
    ("u_R^c", 0, -2/3, -2/3),  # conjugate has opposite charge
    ("d_R^c", 0, 1/3, 1/3),
    ("ν_L", 1/2, -1/2, 0),
    ("e_L", -1/2, -1/2, -1),
    ("e_R^c", 0, 1, 1),
]

print("\nElectric charge verification (Q = T_3 + Y):")
print("-" * 50)
all_correct = True
for name, T3, Y, Q_expected in particles:
    Q_calc = T3 + Y
    match = "✓" if abs(Q_calc - Q_expected) < 0.001 else "✗"
    if match == "✗":
        all_correct = False
    print(f"{name:8s}: T_3 = {T3:+.2f}, Y = {Y:+.2f} → Q = {Q_calc:+.2f} {match}")

print("-" * 50)
print(f"All charges verified: {'✓' if all_correct else '✗'}")

# =============================================================================
# PART 6: Summary
# =============================================================================
print("\n" + "="*70)
print("SUMMARY: Issue C2 Resolution")
print("="*70)

print("""
ERROR IDENTIFIED:
Table 3.6.1c incorrectly assigned (3,2)_{1/6} to the 5̄ representation.

CORRECTION:
The left-handed quark doublet (3,2)_{1/6} comes from the 10 representation,
not the 5̄. The 5̄ only contains (3̄,1) and (1,2), not (3,2).

The corrected table properly assigns:
- From 5̄: right-handed down quark (d_R^c) and left-handed leptons (L_L)
- From 10: left-handed quarks (Q_L), right-handed up quark (u_R^c),
           right-handed electron (e_R^c)

This matches the standard Georgi-Glashow SU(5) embedding (1974).
""")
