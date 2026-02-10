#!/usr/bin/env python3
"""
Issue 1 Resolution: Bag Constant Normalization

The Chi-Profile-Derivation has an inconsistency between:
- Line 116: V_eff = λ(χ² - v_χ²)²
- Line 136: B_eff = λv_χ⁴(2A - A²)²
- Line 139: B_max ≈ (λ/4)f_π⁴

This script investigates the correct normalization and determines the fix.

Date: 2025-12-14
"""

import numpy as np

print("=" * 70)
print("ISSUE 1: BAG CONSTANT NORMALIZATION INVESTIGATION")
print("=" * 70)

# Parameters
f_pi = 93.0  # MeV (document value)
v_chi = f_pi  # v_χ = f_π in σ-model
A = 0.25  # Suppression amplitude
lambda_coupling = 20.0  # Quartic coupling (estimated)

print("\n" + "=" * 70)
print("PART 1: STANDARD CONVENTIONS FOR MEXICAN HAT POTENTIAL")
print("=" * 70)

print("""
There are TWO common conventions for the Mexican hat potential:

CONVENTION A (Particle Physics Standard):
   V(φ) = (λ/4)(φ² - v²)²

   - Used by Peskin & Schroeder, PDG, most particle physics texts
   - Minimum at φ = ±v
   - Height at origin: V(0) = (λ/4)v⁴
   - Mass of radial mode: m² = 2λv²

CONVENTION B (Some Field Theory Texts):
   V(φ) = λ(φ² - v²)²

   - Used in some condensed matter and older texts
   - Minimum at φ = ±v
   - Height at origin: V(0) = λv⁴
   - Mass of radial mode: m² = 8λv²

The Chi-Profile-Derivation MIXES these conventions!
""")

print("\n" + "=" * 70)
print("PART 2: TRACING THE DOCUMENT'S CALCULATIONS")
print("=" * 70)

# What the document states
print("\nDocument Line 116: V_eff = λ(χ² - v_χ²)²")
print("This is CONVENTION B")
print(f"→ B_max = V_eff(0) = λ × v_χ⁴ = {lambda_coupling} × {v_chi}⁴")
B_max_convB = lambda_coupling * v_chi**4
print(f"→ B_max = {B_max_convB:.2e} MeV⁴")
print(f"→ B_max^(1/4) = {B_max_convB**0.25:.1f} MeV")

print("\nDocument Line 139: B_max ≈ (λ/4)f_π⁴")
print("This is CONVENTION A")
print(f"→ B_max = (λ/4) × v_χ⁴ = ({lambda_coupling}/4) × {v_chi}⁴")
B_max_convA = (lambda_coupling/4) * v_chi**4
print(f"→ B_max = {B_max_convA:.2e} MeV⁴")
print(f"→ B_max^(1/4) = {B_max_convA**0.25:.1f} MeV")

print("\n⚠️  INCONSISTENCY IDENTIFIED:")
print(f"   Convention B gives: B_max^(1/4) = {B_max_convB**0.25:.1f} MeV")
print(f"   Convention A gives: B_max^(1/4) = {B_max_convA**0.25:.1f} MeV")
print(f"   Ratio: {B_max_convB/B_max_convA:.1f}× difference")

print("\n" + "=" * 70)
print("PART 3: WHAT THE NUMERICAL RESULT IMPLIES")
print("=" * 70)

# Document claims B_eff^(1/4) ≈ 92 MeV
B_eff_target = 92.0  # MeV (what document claims)
B_eff_target_4 = B_eff_target**4  # MeV⁴

# The suppression factor
factor = (2*A - A**2)**2
print(f"\nSuppression factor (2A - A²)² with A = {A}:")
print(f"   (2×{A} - {A}²)² = ({2*A} - {A**2})² = {2*A - A**2}² = {factor:.4f}")
print(f"   ≈ 0.19 (as stated in document)")

# Work backwards: what B_max would give B_eff^(1/4) = 92 MeV?
B_max_implied = B_eff_target_4 / factor
print(f"\nTo get B_eff^(1/4) = {B_eff_target} MeV:")
print(f"   B_eff = {B_eff_target}⁴ = {B_eff_target_4:.2e} MeV⁴")
print(f"   B_max = B_eff / 0.19 = {B_max_implied:.2e} MeV⁴")
print(f"   B_max^(1/4) = {B_max_implied**0.25:.1f} MeV")

# What λ does this imply?
# Convention A: B_max = (λ/4)v⁴ → λ = 4 B_max / v⁴
lambda_implied_A = 4 * B_max_implied / v_chi**4
print(f"\nIf using Convention A: λ = 4 × B_max / v_χ⁴ = {lambda_implied_A:.1f}")

# Convention B: B_max = λv⁴ → λ = B_max / v⁴
lambda_implied_B = B_max_implied / v_chi**4
print(f"If using Convention B: λ = B_max / v_χ⁴ = {lambda_implied_B:.1f}")

print("\n" + "=" * 70)
print("PART 4: VERIFICATION WITH LINE 142 CALCULATION")
print("=" * 70)

print("\nDocument Line 141-142:")
print(f"   'Using λ ≈ 20, f_π = 93 MeV:'")
print(f"   'B_eff^(1/4) ≈ 0.66 × 139 MeV ≈ 92 MeV'")

print("\nLet's verify the '139 MeV' value:")
print(f"   If B_max^(1/4) = 139 MeV, then B_max = 139⁴ = {139**4:.2e} MeV⁴")

# Check which convention gives 139 MeV
print(f"\n   Convention A: B_max = (λ/4)v⁴ = (20/4) × 93⁴ = {(20/4) * 93**4:.2e} MeV⁴")
print(f"   → B_max^(1/4) = {((20/4) * 93**4)**0.25:.1f} MeV")

print(f"\n   Convention B: B_max = λv⁴ = 20 × 93⁴ = {20 * 93**4:.2e} MeV⁴")
print(f"   → B_max^(1/4) = {(20 * 93**4)**0.25:.1f} MeV")

print("\n✅ The numerical calculation (139 MeV) uses CONVENTION A: B_max = (λ/4)v⁴")
print("❌ But Line 116 states CONVENTION B: V_eff = λ(χ² - v_χ²)²")

print("\n" + "=" * 70)
print("PART 5: THE CORRECT FIX")
print("=" * 70)

print("""
The document is internally inconsistent. There are two ways to fix it:

OPTION 1: Change Line 116 to Convention A (RECOMMENDED)
   Change: V_eff = λ(χ² - v_χ²)²
   To:     V_eff = (λ/4)(χ² - v_χ²)²

   Then all numerical calculations are consistent.
   This matches Peskin & Schroeder and standard particle physics.

OPTION 2: Change Lines 136, 139 to Convention B
   Change Line 136: B_eff = λv_χ⁴(2A - A²)² (already correct)
   Change Line 139: B_max = λf_π⁴ (remove the /4)
   Recalculate: B_max^(1/4) = (λv⁴)^(1/4) = (20 × 93⁴)^(1/4) = 196 MeV
   Then: B_eff^(1/4) = 0.66 × 196 = 130 MeV (NOT 92 MeV!)

   This would require changing the claimed B_eff value.

OPTION 1 is clearly the better fix - it preserves the numerical result.
""")

print("\n" + "=" * 70)
print("PART 6: VERIFICATION OF THE CORRECTED FORMULA")
print("=" * 70)

# Corrected formula with Convention A
print("\nWith Convention A: V_eff = (λ/4)(χ² - v_χ²)²")
print(f"\nParameters:")
print(f"   λ = {lambda_coupling}")
print(f"   v_χ = f_π = {v_chi} MeV")
print(f"   A = {A}")

# B_max with Convention A
B_max_A = (lambda_coupling/4) * v_chi**4
print(f"\nB_max = (λ/4)v_χ⁴ = ({lambda_coupling}/4) × {v_chi}⁴")
print(f"      = {B_max_A:.4e} MeV⁴")
print(f"B_max^(1/4) = {B_max_A**0.25:.1f} MeV")

# B_eff with Convention A
B_eff_A = (lambda_coupling/4) * v_chi**4 * factor
print(f"\nB_eff = (λ/4)v_χ⁴ × (2A - A²)²")
print(f"      = {B_max_A:.4e} × {factor:.4f}")
print(f"      = {B_eff_A:.4e} MeV⁴")
print(f"B_eff^(1/4) = {B_eff_A**0.25:.1f} MeV")

# Check the 0.66 factor
print(f"\nRatio B_eff^(1/4) / B_max^(1/4) = {B_eff_A**0.25:.1f} / {B_max_A**0.25:.1f} = {(B_eff_A**0.25)/(B_max_A**0.25):.2f}")
print(f"Document claims: 0.66")
print(f"Calculated: {factor**0.25:.2f}")
print(f"Match: {'✅ YES' if abs(factor**0.25 - 0.66) < 0.01 else '❌ NO'}")

print("\n" + "=" * 70)
print("PART 7: RECOMMENDED DOCUMENT CHANGES")
print("=" * 70)

print("""
CHANGE 1: Line 116
   FROM: V_eff = λ(χ² - v_χ²)²
   TO:   V_eff = (λ/4)(χ² - v_χ²)²

CHANGE 2: Line 119
   FROM: P(r) = -λ[χ(r)² - v_χ²]²
   TO:   P(r) = -(λ/4)[χ(r)² - v_χ²]²

CHANGE 3: Line 123
   FROM: P(0) = -λv_χ⁴[(1-A)² - 1]² = -λv_χ⁴(2A - A²)²
   TO:   P(0) = -(λ/4)v_χ⁴[(1-A)² - 1]² = -(λ/4)v_χ⁴(2A - A²)²

CHANGE 4: Line 126
   FROM: P(0) ≈ -0.19λv_χ⁴ ≈ -0.19 B_max
   TO:   P(0) ≈ -0.19(λ/4)v_χ⁴ ≈ -0.19 B_max

CHANGE 5: Line 136
   FROM: B_eff = λv_χ⁴[(1-A)² - 1]² = λv_χ⁴(2A - A²)²
   TO:   B_eff = (λ/4)v_χ⁴[(1-A)² - 1]² = (λ/4)v_χ⁴(2A - A²)²

These changes make the document internally consistent AND match
the standard particle physics convention.
""")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
DIAGNOSIS: The document uses two different conventions:
   - Line 116 uses V_eff = λ(χ² - v²)² (Convention B)
   - Line 139 uses B_max = (λ/4)v⁴ (Convention A)

FIX: Change Lines 116, 119, 123, 126, 136 to use Convention A
   - Replace λ with (λ/4) in the potential
   - This matches standard particle physics (Peskin & Schroeder)
   - All numerical results remain unchanged

VERIFICATION: After fix, B_eff^(1/4) = 92 MeV is correct.
""")

# Save results
import json
results = {
    'issue': 'Bag constant normalization inconsistency',
    'diagnosis': 'Document mixes Convention A (λ/4) and Convention B (λ)',
    'fix': 'Change V_eff = λ(...) to V_eff = (λ/4)(...)',
    'lines_to_change': [116, 119, 123, 126, 136],
    'B_max_quarter_MeV': B_max_A**0.25,
    'B_eff_quarter_MeV': B_eff_A**0.25,
    'suppression_factor': factor,
    'ratio': factor**0.25,
    'numerical_verification': 'PASSED'
}

with open('issue1_bag_constant_results.json', 'w') as f:
    json.dump(results, f, indent=2)

print("\nResults saved to: issue1_bag_constant_results.json")
