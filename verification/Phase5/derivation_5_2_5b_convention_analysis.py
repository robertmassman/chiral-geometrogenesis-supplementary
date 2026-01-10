#!/usr/bin/env python3
"""
Convention Analysis for Surface Gravity and Hawking Temperature

This script analyzes the two conventions used in Derivation-5.2.5a and 5.2.5b
and determines which formulation is correct.

Issue:
- 5.2.5a uses κ = c³/(4GM) with [κ] = 1/s → T_H = ℏκ/(2πk_B)
- 5.2.5b uses κ = c⁴/(4GM) with [κ] = m/s² → T_H = ℏκ/(2πk_Bc)

Both claim to give the same temperature. Let's verify.
"""

import numpy as np
from scipy import constants

# Physical constants (SI units)
c = constants.c          # Speed of light (m/s)
G = constants.G          # Gravitational constant (m³/(kg·s²))
hbar = constants.hbar    # Reduced Planck constant (J·s)
k_B = constants.k        # Boltzmann constant (J/K)
M_sun = 1.989e30         # Solar mass (kg)

print("=" * 80)
print("SURFACE GRAVITY AND HAWKING TEMPERATURE CONVENTION ANALYSIS")
print("=" * 80)
print()

# =============================================================================
# SECTION 1: Two Different Surface Gravity Conventions
# =============================================================================

print("SECTION 1: SURFACE GRAVITY CONVENTIONS")
print("-" * 80)

r_s = 2 * G * M_sun / c**2  # Schwarzschild radius

# Convention A: κ as inverse time (used in 5.2.5a after update)
# κ_A = c³/(4GM) = c/(2r_s)
kappa_A = c**3 / (4 * G * M_sun)
kappa_A_alt = c / (2 * r_s)

print("Convention A (5.2.5a): κ = c³/(4GM) = c/(2r_s)")
print(f"  κ_A = c³/(4GM) = {kappa_A:.6e}")
print(f"  κ_A = c/(2r_s) = {kappa_A_alt:.6e}")
print(f"  Match: {np.isclose(kappa_A, kappa_A_alt)}")
print(f"  Units: [c³]/[GM] = (m³/s³)/(m³/s²) = 1/s")
print()

# Convention B: κ as acceleration (used in 5.2.5b currently)
# κ_B = c⁴/(4GM) = c²/(2r_s)
kappa_B = c**4 / (4 * G * M_sun)
kappa_B_alt = c**2 / (2 * r_s)

print("Convention B (5.2.5b): κ = c⁴/(4GM) = c²/(2r_s)")
print(f"  κ_B = c⁴/(4GM) = {kappa_B:.6e}")
print(f"  κ_B = c²/(2r_s) = {kappa_B_alt:.6e}")
print(f"  Match: {np.isclose(kappa_B, kappa_B_alt)}")
print(f"  Units: [c⁴]/[GM] = (m⁴/s⁴)/(m³/s²) = m/s²")
print()

print("Relationship between conventions:")
print(f"  κ_B = κ_A × c")
print(f"  κ_B / κ_A = {kappa_B / kappa_A:.6e} = c = {c:.6e} ✓")
print()

# =============================================================================
# SECTION 2: Temperature Formulas in Each Convention
# =============================================================================

print("SECTION 2: HAWKING TEMPERATURE FORMULAS")
print("-" * 80)

# Convention A: T_H = ℏκ_A/(2πk_B)
T_H_A = hbar * kappa_A / (2 * np.pi * k_B)

print("Convention A: T_H = ℏκ/(2πk_B) [no c in denominator]")
print(f"  T_H = {T_H_A:.6e} K")
print(f"  Dimensional check: [ℏκ_A/(2πk_B)] = (J·s)(1/s)/(J/K) = K ✓")
print()

# Convention B: T_H = ℏκ_B/(2πk_Bc)
T_H_B = hbar * kappa_B / (2 * np.pi * k_B * c)

print("Convention B: T_H = ℏκ/(2πk_Bc) [with c in denominator]")
print(f"  T_H = {T_H_B:.6e} K")
print(f"  Dimensional check: [ℏκ_B/(2πk_Bc)] = (J·s)(m/s²)/[(J/K)(m/s)] = K ✓")
print()

# Direct formula (reference)
T_H_direct = hbar * c**3 / (8 * np.pi * k_B * G * M_sun)

print("Direct formula: T_H = ℏc³/(8πk_BGM)")
print(f"  T_H = {T_H_direct:.6e} K")
print()

print("VERIFICATION:")
print(f"  T_H (Convention A) = {T_H_A:.10e} K")
print(f"  T_H (Convention B) = {T_H_B:.10e} K")
print(f"  T_H (Direct)       = {T_H_direct:.10e} K")
print(f"  All equal: {np.allclose([T_H_A, T_H_B], T_H_direct)}")
print()

# =============================================================================
# SECTION 3: Which Convention Should We Use?
# =============================================================================

print("SECTION 3: STANDARD PHYSICS CONVENTION")
print("-" * 80)

print("""
In standard GR textbooks (Wald 1984, §12.5), surface gravity is defined via:

    κ² = -½(∇_μ ξ_ν)(∇^μ ξ^ν)|_horizon

For Schwarzschild in standard coordinates:

    κ = (c/2)|f'(r_H)| where f(r) = 1 - r_s/r

Since f'(r_s) = 1/r_s:

    κ = c/(2r_s) = c³/(4GM)  [units: 1/s]

This is CONVENTION A.

However, some authors (especially in thermodynamics contexts) define
"surface gravity" as the local acceleration at the horizon, which
would be κ_accel = c²/(2r_s) [units: m/s²]. This is CONVENTION B.

The difference is a factor of c:
    κ_accel = κ × c

The temperature formula must adjust accordingly:
    - If κ has units 1/s: T_H = ℏκ/(2πk_B)
    - If κ has units m/s²: T_H = ℏκ/(2πk_Bc)

Both give the same physical temperature!
""")

# =============================================================================
# SECTION 4: What Does Wald (1984) Say?
# =============================================================================

print("SECTION 4: WALD'S CONVENTION")
print("-" * 80)

print("""
From Wald (1984) §12.5, equation (12.5.14):

    κ = lim_{r→r_H} [(-g_tt,r / 2) × sqrt(-g^tt/g^rr)]

For Schwarzschild:
    g_tt = -(1 - r_s/r)c²
    g_tt,r = -c²r_s/r²

At horizon (r = r_s):
    g_tt,r = -c²/r_s
    sqrt(-g^tt/g^rr) → 1 (carefully)

So κ = c²/(2r_s) in Wald's notation.

BUT Wald uses units where c=1. When c≠1:
    κ = c²/(2r_s) with the factor of c² absorbed in the metric signature.

The key is: Wald's temperature formula is T = ℏκ/(2πk_B), which
in SI units with κ = c²/(2r_s) would give WRONG dimensions unless
we interpret κ as acceleration (m/s²) and include c in denominator.

RESOLUTION:
    Wald uses c=1. When restoring c:
    - κ = c³/(4GM) has units 1/s
    - T_H = ℏκ/(2πk_B) gives correct temperature

    OR equivalently:
    - κ = c⁴/(4GM) has units m/s²
    - T_H = ℏκ/(2πk_Bc) gives correct temperature
""")

# =============================================================================
# SECTION 5: Recommendation for Document Consistency
# =============================================================================

print("SECTION 5: RECOMMENDATION")
print("-" * 80)

print("""
The updated 5.2.5a document now uses:
    κ = c³/(4GM) with [κ] = 1/s
    T_H = ℏκ/(2πk_B)

For consistency, 5.2.5b should ALSO use:
    κ = c³/(4GM) with [κ] = 1/s
    T_H = ℏκ/(2πk_B)

REQUIRED CHANGES TO 5.2.5b:

1. Line 7: Change "T_H = ℏκ/(2πk_Bc)" to "T_H = ℏκ/(2πk_B)"
2. Line 68: Fix redshift calculation (remove extra c)
3. Line 71: Change boxed formula
4. Line 158: Change κ = c⁴/(4GM) to κ = c³/(4GM)
5. Line 160: Change dimensional check to [κ] = 1/s
6. Line 166: Fix temperature derivation
7. Line 168: Change boxed formula
8. Lines 179-181: Fix factor tracking table
9. Line 263: Fix summary formula (also c² → c³)
10. Line 296, 306, 333, 337, 352: Various formula updates
11. Line 318: Entropy derivation (check factors)

Let me verify the entropy derivation with the corrected convention...
""")

# =============================================================================
# SECTION 6: Entropy Derivation Check
# =============================================================================

print("SECTION 6: ENTROPY DERIVATION VERIFICATION")
print("-" * 80)

# From T_H = ℏκ/(2πk_B) and κ = c³/(4GM):
# T_H = ℏc³/(8πk_BGM)

# dS = dE/T = c²dM/T_H = c²dM × 8πk_BGM/(ℏc³)
#    = 8πk_BGM dM / (ℏc)

# Note: With κ = c³/(4GM), we have:
# 1/κ = 4GM/c³

print("Starting from T_H = ℏκ/(2πk_B) where κ = c³/(4GM):")
print()
print("dS = dE/T = c²dM / T_H")
print("   = c²dM × 2πk_B / (ℏκ)")
print("   = c²dM × 2πk_B × 4GM / (ℏc³)")
print("   = 8πk_BGM dM / (ℏc)")
print()
print("Integrating: S = 4πk_BGM² / (ℏc)")
print()

# Verify numerically
M = M_sun
S_calculated = 4 * np.pi * k_B * G * M**2 / (hbar * c)
print(f"For M = M_sun: S = {S_calculated:.6e} J/K")
print()

# Express in terms of area A = 4πr_s² = 16πG²M²/c⁴
A = 4 * np.pi * r_s**2
l_P_squared = G * hbar / c**3  # Planck length squared

print("Converting to area:")
print(f"  A = 4πr_s² = {A:.6e} m²")
print(f"  ℓ_P² = Gℏ/c³ = {l_P_squared:.6e} m²")
print()

print("From M² = c⁴A/(16πG²):")
print("  S = 4πk_BG/(ℏc) × c⁴A/(16πG²)")
print("    = k_Bc³A/(4Gℏ)")
print("    = k_BA/(4ℓ_P²)")
print()

S_from_area = k_B * A / (4 * l_P_squared)
print(f"S from area formula: {S_from_area:.6e} J/K")
print(f"S calculated directly: {S_calculated:.6e} J/K")
print(f"Match: {np.isclose(S_calculated, S_from_area)}")
print()

print("✅ ENTROPY DERIVATION VERIFIED: γ = 1/4 emerges correctly!")
print()

# =============================================================================
# SECTION 7: Summary of Required Changes
# =============================================================================

print("=" * 80)
print("SUMMARY: REQUIRED CHANGES TO DERIVATION-5.2.5b")
print("=" * 80)
print()

changes = [
    ("Line 7", "T_H = ℏκ/(2πk_Bc)", "T_H = ℏκ/(2πk_B)"),
    ("Line 58", "a_∞ = κc", "a_∞ = κc (KEEP - this is correct)"),
    ("Line 68", "ℏκc/(2πk_Bc) = ℏκ/(2πk_Bc)", "ℏκc/(2πk_Bc) = ℏκ/(2πk_B)"),
    ("Line 71", "T_H = ℏκ/(2πk_Bc)", "T_H = ℏκ/(2πk_B)"),
    ("Line 158", "κ = c²/(2r_s) = c⁴/(4GM)", "κ = c/(2r_s) = c³/(4GM)"),
    ("Line 160", "[κ] = LT⁻² (acceleration)", "[κ] = T⁻¹ (inverse time)"),
    ("Line 163", "r_s = c²/(2κ)", "r_s = c/(2κ)"),
    ("Line 166", "ℏc/(4πk_B) × 2κ/c² = ℏκ/(2πk_Bc)", "ℏc/(4πk_Br_s) = ℏκ/(2πk_B)"),
    ("Line 168", "T_H = ℏκ/(2πk_Bc)", "T_H = ℏκ/(2πk_B)"),
    ("Line 179", "κ = c²/(2r_s)", "κ = c/(2r_s)"),
    ("Line 180", "β = 2πc/κ", "β = 2π/κ"),
    ("Line 181", "T_H = ℏκ/(2πk_Bc)", "T_H = ℏκ/(2πk_B)"),
    ("Line 263", "ℏc²/(8πk_BGM)", "ℏc³/(8πk_BGM)"),
    ("Line 296", "T_H = ℏκ/(2πk_Bc)", "T_H = ℏκ/(2πk_B)"),
    ("Line 306", "κ = c²/(2r_s)", "κ = c/(2r_s)"),
    ("Line 318", "2πk_Bc/ℏκ", "2πk_B/ℏκ (already has 4GM/c³ correct)"),
    ("Line 333", "T_H = ℏκ/(2πk_B c)", "T_H = ℏκ/(2πk_B)"),
    ("Line 337", "ℏκ/(2πk_B c)", "ℏκ/(2πk_B)"),
    ("Line 352", "T_H = ℏκ/(2πk_Bc)", "T_H = ℏκ/(2πk_B)"),
]

print(f"{'Location':<12} | {'Current':<35} | {'Change To':<35}")
print("-" * 90)
for loc, old, new in changes:
    print(f"{loc:<12} | {old:<35} | {new:<35}")

print()
print("=" * 80)
print("VERIFICATION COMPLETE")
print("=" * 80)
