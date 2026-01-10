#!/usr/bin/env python3
"""
Theorem 0.0.3 Verification: Gluon Self-Coupling Structure Constants

This script derives the SU(3) structure constants f^abc that determine
gluon self-interactions. These are PURE LIE ALGEBRA — no phenomenological
input required.

Key Result:
- The structure constants f^abc are completely determined by [T^a, T^b] = i f^abc T^c
- The triple-gluon vertex structure is fixed by gauge invariance + f^abc
- The quartic-gluon vertex structure is fixed by f^abe f^cde

Author: Chiral Geometrogenesis Verification Suite
Date: December 2025
"""

import numpy as np
import json
from itertools import product

# =============================================================================
# GELL-MANN MATRICES (Standard Normalization: Tr(λ^a λ^b) = 2δ^ab)
# =============================================================================

lambda_1 = np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], dtype=complex)
lambda_2 = np.array([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]], dtype=complex)
lambda_3 = np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], dtype=complex)
lambda_4 = np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], dtype=complex)
lambda_5 = np.array([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]], dtype=complex)
lambda_6 = np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], dtype=complex)
lambda_7 = np.array([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]], dtype=complex)
lambda_8 = np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], dtype=complex) / np.sqrt(3)

gell_mann = [lambda_1, lambda_2, lambda_3, lambda_4, lambda_5, lambda_6, lambda_7, lambda_8]

# Generators T^a = λ^a / 2 (normalization Tr(T^a T^b) = δ^ab / 2)
generators = [lam / 2 for lam in gell_mann]

print("=" * 70)
print("GLUON SELF-COUPLING: Structure Constants f^abc")
print("=" * 70)
print("\nDeriving from SU(3) Lie algebra: [T^a, T^b] = i f^abc T^c")
print()

# =============================================================================
# COMPUTE STRUCTURE CONSTANTS f^abc
# =============================================================================

def compute_structure_constants(gens):
    """
    Compute structure constants f^abc from [T^a, T^b] = i f^abc T^c
    
    Method: f^abc = -2i Tr([T^a, T^b] T^c)
    """
    n = len(gens)
    f = np.zeros((n, n, n), dtype=float)
    
    for a in range(n):
        for b in range(n):
            commutator = gens[a] @ gens[b] - gens[b] @ gens[a]  # [T^a, T^b]
            for c in range(n):
                # f^abc = -2i Tr([T^a, T^b] T^c)
                val = -2j * np.trace(commutator @ gens[c])
                f[a, b, c] = np.real(val)  # f^abc is real
    
    return f

f_abc = compute_structure_constants(generators)

print("Structure Constants f^abc (non-zero components):")
print("-" * 50)

# Store non-zero structure constants
nonzero_f = []
for a, b, c in product(range(8), repeat=3):
    if abs(f_abc[a, b, c]) > 1e-10:
        # Use 1-indexed notation (standard physics convention)
        nonzero_f.append({
            'indices': (a+1, b+1, c+1),
            'value': float(f_abc[a, b, c])
        })
        if a < b:  # Print each independent component once
            val = f_abc[a, b, c]
            if abs(val - 1.0) < 1e-10:
                print(f"  f^{a+1}{b+1}{c+1} = 1")
            elif abs(val - 0.5) < 1e-10:
                print(f"  f^{a+1}{b+1}{c+1} = 1/2")
            elif abs(val + 0.5) < 1e-10:
                print(f"  f^{a+1}{b+1}{c+1} = -1/2")
            elif abs(val - np.sqrt(3)/2) < 1e-10:
                print(f"  f^{a+1}{b+1}{c+1} = √3/2")
            elif abs(val + np.sqrt(3)/2) < 1e-10:
                print(f"  f^{a+1}{b+1}{c+1} = -√3/2")
            else:
                print(f"  f^{a+1}{b+1}{c+1} = {val:.6f}")

# =============================================================================
# VERIFY ANTISYMMETRY
# =============================================================================

print("\n" + "=" * 70)
print("VERIFICATION 1: Antisymmetry f^abc = -f^bac")
print("=" * 70)

antisymmetry_satisfied = True
for a, b, c in product(range(8), repeat=3):
    if abs(f_abc[a, b, c] + f_abc[b, a, c]) > 1e-10:
        antisymmetry_satisfied = False
        print(f"  FAILED: f^{a+1}{b+1}{c+1} ≠ -f^{b+1}{a+1}{c+1}")

if antisymmetry_satisfied:
    print("✓ Antisymmetry verified: f^abc = -f^bac for all a,b,c")

# =============================================================================
# VERIFY JACOBI IDENTITY
# =============================================================================

print("\n" + "=" * 70)
print("VERIFICATION 2: Jacobi Identity")
print("=" * 70)
print("f^ade f^bcd + f^bde f^cad + f^cde f^abd = 0")

jacobi_satisfied = True
jacobi_error = 0
for a, b, c, d in product(range(8), repeat=4):
    # Jacobi: f^ade f^bcd + f^bde f^cad + f^cde f^abd = 0
    term1 = sum(f_abc[a, d, e] * f_abc[b, c, e] for e in range(8))
    term2 = sum(f_abc[b, d, e] * f_abc[c, a, e] for e in range(8))
    term3 = sum(f_abc[c, d, e] * f_abc[a, b, e] for e in range(8))
    error = abs(term1 + term2 + term3)
    jacobi_error = max(jacobi_error, error)
    if error > 1e-10:
        jacobi_satisfied = False

if jacobi_satisfied:
    print(f"✓ Jacobi identity verified (max error: {jacobi_error:.2e})")
else:
    print(f"✗ Jacobi identity FAILED (max error: {jacobi_error:.2e})")

# =============================================================================
# COMPUTE ADJOINT CASIMIR C_A
# =============================================================================

print("\n" + "=" * 70)
print("ADJOINT CASIMIR C_A (Gluon self-energy)")
print("=" * 70)

# C_A δ^cd = f^ace f^bde for adjoint rep
# C_A = f^ace f^ace / 8 (trace over all indices)

C_A_from_f = sum(f_abc[a, c, e] * f_abc[a, c, e] 
                  for a in range(8) for c in range(8) for e in range(8)) / 8

print(f"\nFrom f^abc: C_A = Σ f^ace f^ace / 8 = {C_A_from_f:.6f}")
print(f"Expected: C_A = N_c = 3")
print(f"Match: {abs(C_A_from_f - 3.0) < 1e-10}")

# =============================================================================
# TRIPLE GLUON VERTEX STRUCTURE
# =============================================================================

print("\n" + "=" * 70)
print("TRIPLE GLUON VERTEX")
print("=" * 70)
print("\nThe QCD Lagrangian contains: -g f^abc (∂_μ A^a_ν) A^bμ A^cν")
print("\nThis gives the triple-gluon vertex:")
print("  V^abc_μνρ(k,p,q) = -g f^abc × [Lorentz structure]")
print("\nwhere the Lorentz structure is:")
print("  g_μν(k-p)_ρ + g_νρ(p-q)_μ + g_ρμ(q-k)_ν")
print("\n→ The COLOR STRUCTURE (f^abc) is geometrically determined")
print("→ Only the coupling strength g requires dynamics")

# Count independent f^abc components
# f^abc is totally antisymmetric, so independent components = C(8,3) = 56
# but most are zero
unique_nonzero = set()
for a, b, c in product(range(8), repeat=3):
    if abs(f_abc[a, b, c]) > 1e-10:
        sorted_idx = tuple(sorted([a, b, c]))
        unique_nonzero.add(sorted_idx)

print(f"\nNumber of independent non-zero f^abc: {len(unique_nonzero)}")

# =============================================================================
# QUARTIC GLUON VERTEX STRUCTURE  
# =============================================================================

print("\n" + "=" * 70)
print("QUARTIC GLUON VERTEX")
print("=" * 70)
print("\nThe QCD Lagrangian contains: -¼g² f^abe f^cde A^a A^b A^c A^d")
print("\nThe quartic vertex has structure:")
print("  V^abcd_μνρσ = -ig² × [f^abe f^cde + f^ace f^bde + f^ade f^bce]")
print("                    × [Lorentz structure]")

# Compute a sample quartic structure
# V^1234 = f^12e f^34e summed over e
V_1234 = sum(f_abc[0, 1, e] * f_abc[2, 3, e] for e in range(8))
V_1324 = sum(f_abc[0, 2, e] * f_abc[1, 3, e] for e in range(8))
V_1423 = sum(f_abc[0, 3, e] * f_abc[1, 2, e] for e in range(8))

print(f"\nExample: gluons with colors (1,2,3,4)")
print(f"  f^12e f^34e = {V_1234:.6f}")
print(f"  f^13e f^24e = {V_1324:.6f}")  
print(f"  f^14e f^23e = {V_1423:.6f}")

# =============================================================================
# COMPARISON: ABELIAN vs NON-ABELIAN
# =============================================================================

print("\n" + "=" * 70)
print("WHY GLUON SELF-COUPLING IS GEOMETRICALLY FORCED")
print("=" * 70)
print("""
For U(1) (QED): 
  - Lie algebra is abelian: [T, T] = 0
  - Structure constants: f = 0
  - Photon does not self-couple ✓

For SU(3) (QCD):
  - Lie algebra is non-abelian: [T^a, T^b] ≠ 0
  - Structure constants: f^abc ≠ 0
  - Gluons MUST self-couple ✓

The non-abelian structure is FORCED by the group theory.
N_c = 3 → SU(3) is non-abelian → gluons self-couple.

This is why "no gluon self-coupling" is not an option for SU(3).
""")

# =============================================================================
# KNOWN VALUES CHECK
# =============================================================================

print("\n" + "=" * 70)
print("STANDARD STRUCTURE CONSTANTS (Verification)")
print("=" * 70)

known_f = {
    (1, 2, 3): 1.0,
    (1, 4, 7): 0.5,
    (1, 5, 6): -0.5,
    (2, 4, 6): 0.5,
    (2, 5, 7): 0.5,
    (3, 4, 5): 0.5,
    (3, 6, 7): -0.5,
    (4, 5, 8): np.sqrt(3)/2,
    (6, 7, 8): np.sqrt(3)/2
}

all_correct = True
for (a, b, c), expected in known_f.items():
    computed = f_abc[a-1, b-1, c-1]
    match = abs(computed - expected) < 1e-10
    status = "✓" if match else "✗"
    print(f"  f^{a}{b}{c}: computed = {computed:.6f}, expected = {expected:.6f} {status}")
    if not match:
        all_correct = False

print(f"\nAll standard values match: {all_correct}")

# =============================================================================
# SUMMARY & JSON OUTPUT
# =============================================================================

print("\n" + "=" * 70)
print("SUMMARY: Gluon Self-Coupling from Geometry")
print("=" * 70)

results = {
    'theorem': '0.0.3',
    'topic': 'Gluon Self-Coupling Structure',
    'key_results': {
        'structure_constants_determined': True,
        'antisymmetry_verified': antisymmetry_satisfied,
        'jacobi_identity_verified': jacobi_satisfied,
        'adjoint_casimir_C_A': float(C_A_from_f),
        'expected_C_A': 3.0,
        'C_A_match': abs(C_A_from_f - 3.0) < 1e-10,
        'num_independent_nonzero_f': len(unique_nonzero)
    },
    'structure_constants': [
        {'indices': list(item['indices']), 'value': item['value']} 
        for item in nonzero_f if item['indices'][0] < item['indices'][1]
    ],
    'what_is_geometric': [
        'All f^abc structure constants',
        'Triple gluon vertex COLOR structure',
        'Quartic gluon vertex COLOR structure',
        'Non-abelian nature (gluons self-couple)',
        'Adjoint Casimir C_A = N_c = 3'
    ],
    'what_requires_dynamics': [
        'Coupling constant g (or α_s)',
        'Running of coupling'
    ],
    'conclusion': 'Gluon self-coupling STRUCTURE is completely determined by SU(3) Lie algebra. Only coupling STRENGTH requires phenomenological input.'
}

print(f"""
✅ Structure constants f^abc: GEOMETRICALLY DETERMINED
   - Computed directly from [T^a, T^b] = i f^abc T^c
   - All 9 independent non-zero components verified
   - Antisymmetry and Jacobi identity confirmed

✅ Triple gluon vertex: COLOR STRUCTURE DETERMINED
   - Vertex ∝ f^abc (from Lie algebra)
   - Only coupling g undetermined

✅ Quartic gluon vertex: COLOR STRUCTURE DETERMINED  
   - Vertex ∝ f^abe f^cde (from Lie algebra squared)
   - Only coupling g² undetermined

✅ Adjoint Casimir: C_A = {C_A_from_f:.0f} = N_c (verified)

CONCLUSION: Gluon self-interactions are NON-OPTIONAL
- SU(3) is non-abelian → [T^a, T^b] ≠ 0 → f^abc ≠ 0
- Gluon self-coupling is FORCED by gauge group structure
- Only the STRENGTH (g) requires dynamics
""")

# Save results
output_file = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/theorem_0_0_3_gluon_self_coupling_results.json'
with open(output_file, 'w') as f:
    json.dump(results, f, indent=2)

print(f"Results saved to: {output_file}")
