#!/usr/bin/env python3
"""
Hyperbolic Disk Efficiency Investigation for the 4/π Factor

This script investigates whether the factor 4/π in N_geo = (4/π) × ln(ξ)
arises from the "slow-roll efficiency" on the Poincaré disk — the ratio
of e-folds generated to geodesic distance traversed.

Key Hypothesis (Direction B from Resolution Plan):
The factor 4/π is the ratio (e-folds)/(geodesic length) for α = 1/3.

Background:
- For α-attractors, the field space is the Poincaré disk
- The geodesic distance from origin to radius r is arctanh(r)
- The canonical field φ = √(6α) M_P × arctanh(r)
- E-folds N = (3α/2) sinh²(φ/√(6α) M_P)

Author: Research investigation for Prop 0.0.17aa
Date: 2026-01-26
"""

import numpy as np
from scipy import integrate
from scipy.optimize import brentq
import warnings
warnings.filterwarnings('ignore')

# =============================================================================
# Constants
# =============================================================================
N_c = 3  # Number of colors
N_f = 3  # Number of flavors (topological)
alpha = 1/3  # α-attractor parameter for SU(3)

# Target values
ln_xi = 128 * np.pi / 9
N_geo_target = 512 / 9
four_over_pi = 4 / np.pi

print("=" * 75)
print("HYPERBOLIC DISK EFFICIENCY INVESTIGATION: Origin of 4/π")
print("=" * 75)

print(f"\nTarget values:")
print(f"  α = {alpha} = 1/3")
print(f"  ln(ξ) = 128π/9 = {ln_xi:.6f}")
print(f"  N_geo = 512/9 = {N_geo_target:.6f}")
print(f"  4/π = {four_over_pi:.6f}")

# =============================================================================
# Section 1: Poincaré Disk Geometry
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 1: Poincaré Disk Geometry")
print("=" * 75)

print("""
The Poincaré disk is the unit disk D = {z ∈ C : |z| < 1} with hyperbolic metric:
  ds² = 4|dz|²/(1 - |z|²)²

For α-attractors with parameter α, the metric is scaled:
  ds² = (3α/2) × 4|dz|²/(1 - |z|²)² = 6α |dz|²/(1 - |z|²)²

For α = 1/3:
  ds² = 2|dz|²/(1 - |z|²)²

The geodesic distance from origin to radius r (along a radial line):
  d(0, r) = ∫₀^r √(2/(1-s²)²) ds = √2 × arctanh(r)
""")

# Geodesic distance function
def geodesic_distance(r, alpha=1/3):
    """Geodesic distance from origin to radius r on α-attractor disk."""
    return np.sqrt(6 * alpha) * np.arctanh(r)

# Verify numerically
r_test = 0.9
d_analytic = geodesic_distance(r_test)
d_numerical, _ = integrate.quad(lambda s: np.sqrt(2) / (1 - s**2), 0, r_test)

print(f"Geodesic distance verification (r = {r_test}):")
print(f"  Analytic: d = √(6α) arctanh(r) = {d_analytic:.6f}")
print(f"  Numerical: ∫ √(2)/(1-s²) ds = {d_numerical:.6f}")
print(f"  Match: {np.isclose(d_analytic, d_numerical)}")

# =============================================================================
# Section 2: Canonical Field and E-folds
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 2: Canonical Field and E-folds")
print("=" * 75)

print("""
The canonical field φ equals the geodesic distance (in Planck units):
  φ = √(6α) M_P × arctanh(r) = d(0, r) × M_P

For α = 1/3:
  φ = √2 M_P × arctanh(r)

The number of e-folds from slow-roll is:
  N = (3α/2) × sinh²(φ/(√(6α) M_P))
    = (3α/2) × sinh²(arctanh(r))
    = (3α/2) × r²/(1 - r²)

For α = 1/3:
  N = (1/2) × r²/(1 - r²)
""")

def efolds_from_r(r, alpha=1/3):
    """E-folds from radius r for α-attractor."""
    return (3 * alpha / 2) * r**2 / (1 - r**2)

def efolds_from_phi(phi_MP, alpha=1/3):
    """E-folds from canonical field φ/M_P."""
    x = phi_MP / np.sqrt(6 * alpha)
    return (3 * alpha / 2) * np.sinh(x)**2

# Verify consistency
r_test = 0.99
phi_test = geodesic_distance(r_test)
N_from_r = efolds_from_r(r_test)
N_from_phi = efolds_from_phi(phi_test)

print(f"\nConsistency check (r = {r_test}):")
print(f"  φ/M_P = {phi_test:.6f}")
print(f"  N(from r) = {N_from_r:.6f}")
print(f"  N(from φ) = {N_from_phi:.6f}")
print(f"  Match: {np.isclose(N_from_r, N_from_phi)}")

# =============================================================================
# Section 3: The Efficiency Ratio
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 3: The Efficiency Ratio N/d(0,r)")
print("=" * 75)

print("""
The "slow-roll efficiency" is defined as:
  η_sr = N / d(0, r) = (e-folds) / (geodesic distance)

For α = 1/3:
  η_sr = [(1/2) r²/(1-r²)] / [√2 arctanh(r)]

Let's compute this for various r values and see if 4/π appears.
""")

def efficiency_ratio(r, alpha=1/3):
    """Ratio of e-folds to geodesic distance."""
    if r < 1e-10:
        return 0
    N = efolds_from_r(r, alpha)
    d = geodesic_distance(r, alpha)
    return N / d

print("\nEfficiency ratio η_sr = N/d for various r:")
print("-" * 60)
print(f"{'r':<10} {'N':<12} {'d':<12} {'η_sr':<12} {'η_sr × π/4':<12}")
print("-" * 60)

for r in [0.5, 0.9, 0.95, 0.99, 0.999, 0.9999]:
    N = efolds_from_r(r)
    d = geodesic_distance(r)
    eta = efficiency_ratio(r)
    print(f"{r:<10.4f} {N:<12.4f} {d:<12.4f} {eta:<12.4f} {eta * np.pi / 4:<12.4f}")

print(f"\nNote: If η_sr = 4/π = {four_over_pi:.6f}, then η_sr × π/4 = 1")
print("The efficiency ratio is NOT constant — it depends on r.")

# =============================================================================
# Section 4: Alternative Efficiency Definition
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 4: Alternative Efficiency - N/ln(1/(1-r))")
print("=" * 75)

print("""
Since arctanh(r) = (1/2)ln((1+r)/(1-r)) ≈ (1/2)ln(2/(1-r)) for r → 1,
let's define an alternative efficiency using ln(1/(1-r)):

  η_alt = N / ln(1/(1-r)) = [(1/2) r²/(1-r²)] / ln(1/(1-r))

Near the boundary (r → 1):
  N ≈ (1/2) × 1/(2(1-r)) = 1/(4(1-r))
  ln(1/(1-r)) → ∞
  η_alt ≈ [1/(4(1-r))] / ln(1/(1-r)) → 0 (slowly)

This doesn't give a constant either.
""")

def alt_efficiency(r, alpha=1/3):
    """Alternative efficiency ratio."""
    if r < 1e-10 or r > 1 - 1e-10:
        return float('nan')
    N = efolds_from_r(r, alpha)
    log_factor = np.log(1 / (1 - r))
    return N / log_factor

print("\nAlternative efficiency η_alt = N/ln(1/(1-r)):")
print("-" * 60)
for r in [0.5, 0.9, 0.95, 0.99, 0.999]:
    N = efolds_from_r(r)
    log_factor = np.log(1 / (1 - r))
    eta_alt = alt_efficiency(r)
    print(f"r = {r:.4f}: N = {N:.4f}, ln(1/(1-r)) = {log_factor:.4f}, η_alt = {eta_alt:.4f}")

# =============================================================================
# Section 5: The Key Insight - What Determines N_geo?
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 5: The Key Insight - What Determines N_geo?")
print("=" * 75)

print("""
The central question: what determines the specific value r_* such that
N(r_*) = N_geo = 512/9?

From the relation N = (1/2) r²/(1-r²):
  512/9 = (1/2) r_*²/(1-r_*²)
  1024/9 = r_*²/(1-r_*²)
  r_*² = (1024/9) × (1 - r_*²)
  r_*² (1 + 1024/9) = 1024/9
  r_*² = (1024/9) / (1033/9) = 1024/1033
  r_* = √(1024/1033) = 32/√1033
""")

# Calculate r_*
r_star_sq = 1024 / 1033
r_star = np.sqrt(r_star_sq)
print(f"\nr_* = √(1024/1033) = {r_star:.8f}")
print(f"1 - r_* = {1 - r_star:.8f}")

# Verify
N_check = efolds_from_r(r_star)
print(f"N(r_*) = {N_check:.6f}")
print(f"Target: 512/9 = {N_geo_target:.6f}")
print(f"Match: {np.isclose(N_check, N_geo_target)}")

# The geodesic distance at r_*
d_star = geodesic_distance(r_star)
print(f"\nGeodesic distance at r_*:")
print(f"d(0, r_*) = √2 arctanh(r_*) = {d_star:.6f}")

# =============================================================================
# Section 6: The Ratio N_geo/d_*
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 6: The Ratio N_geo/d_*")
print("=" * 75)

ratio_N_to_d = N_geo_target / d_star
print(f"\nN_geo / d(0, r_*) = {N_geo_target:.6f} / {d_star:.6f} = {ratio_N_to_d:.6f}")
print(f"Compare to 4/π = {four_over_pi:.6f}")
print(f"Match: {np.isclose(ratio_N_to_d, four_over_pi)}")

print("\nThe efficiency ratio at r_* is NOT equal to 4/π!")
print(f"Ratio: {ratio_N_to_d:.6f}")
print(f"4/π: {four_over_pi:.6f}")
print(f"Difference: {abs(ratio_N_to_d - four_over_pi):.6f}")

# =============================================================================
# Section 7: Another Approach - Ratio to ln(ξ)
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 7: Connecting Geodesic Distance to ln(ξ)")
print("=" * 75)

print("""
Instead of looking at efficiency, let's ask:
What is the relationship between d(0, r_*) and ln(ξ)?

If N_geo = (4/π) × ln(ξ), and N_geo = f(d_*) for some function f,
then we need to understand f.
""")

print(f"\nln(ξ) = {ln_xi:.6f}")
print(f"d(0, r_*) = {d_star:.6f}")
print(f"Ratio ln(ξ)/d_* = {ln_xi/d_star:.6f}")
print(f"Ratio d_*/ln(ξ) = {d_star/ln_xi:.6f}")

# Is there a simple relationship?
print(f"\nChecking various combinations:")
print(f"  d_* × (4/π) = {d_star * four_over_pi:.6f}")
print(f"  d_*² = {d_star**2:.6f}")
print(f"  d_* × π = {d_star * np.pi:.6f}")
print(f"  d_*/2 = {d_star/2:.6f}")

# =============================================================================
# Section 8: The Sinh Relationship
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 8: The Sinh Relationship")
print("=" * 75)

print("""
We have N = (3α/2) sinh²(d/√(6α) M_P) for geodesic distance d.

For α = 1/3 and d = d_*:
  N_geo = (1/2) sinh²(d_*/√2 M_P)

Solving for sinh:
  sinh(d_*/√2) = √(2 N_geo) = √(1024/9) = 32/3
  d_*/√2 = arcsinh(32/3)
  d_* = √2 × arcsinh(32/3)
""")

sinh_val = np.sqrt(2 * N_geo_target)
arcsinh_val = np.arcsinh(sinh_val)
d_star_from_sinh = np.sqrt(2) * arcsinh_val

print(f"sinh(d_*/√2) = √(2 × 512/9) = 32/3 = {sinh_val:.6f}")
print(f"arcsinh(32/3) = {arcsinh_val:.6f}")
print(f"d_* = √2 × arcsinh(32/3) = {d_star_from_sinh:.6f}")
print(f"Compare to direct calculation: {d_star:.6f}")

# =============================================================================
# Section 9: The Connection to ln(ξ)
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 9: The Connection to ln(ξ)")
print("=" * 75)

print("""
The key question: how is d_* related to ln(ξ)?

From the bootstrap: ln(ξ) = (N_c² - 1)² / (2b₀) = 128π/9
From geometry: d_* = √2 × arcsinh(32/3)

Let's check if there's a relationship:
""")

# Various combinations
print(f"\nln(ξ) = {ln_xi:.6f}")
print(f"d_* = {d_star:.6f}")
print(f"\nRatios and combinations:")
print(f"  ln(ξ) / d_* = {ln_xi / d_star:.6f}")
print(f"  d_* / ln(ξ) = {d_star / ln_xi:.6f}")
print(f"  (ln(ξ))² / d_* = {ln_xi**2 / d_star:.6f}")
print(f"  d_* × 4/π = {d_star * four_over_pi:.6f}")
print(f"  √(ln(ξ)) = {np.sqrt(ln_xi):.6f}")
print(f"  d_* / √(ln(ξ)) = {d_star / np.sqrt(ln_xi):.6f}")

# =============================================================================
# Section 10: The Slow-Roll Potential Origin
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 10: Where Does 4/π Enter in Slow-Roll?")
print("=" * 75)

print("""
The slow-roll approximation gives:
  N = ∫ (V/V') dφ/M_P² = ∫ (H²/ε) dt

For α-attractors with V = V₀ tanh²(φ/√(6α)):
  N = (3α/2) ∫ sinh(x) cosh(x) dx = (3α/4) sinh²(x)

where x = φ/(√(6α) M_P).

The 4/π factor must enter through the BOUNDARY CONDITION:
  - The value of φ (or x) at horizon exit, φ_*
  - The relationship between φ_* and ln(ξ)
""")

# The canonical field at horizon exit
phi_star = d_star  # In Planck units
x_star = phi_star / np.sqrt(6 * alpha)

print(f"\nAt horizon exit:")
print(f"  φ_*/M_P = {phi_star:.6f}")
print(f"  x_* = φ_*/(√(6α) M_P) = {x_star:.6f}")
print(f"  sinh(x_*) = {np.sinh(x_star):.6f}")
print(f"  cosh(x_*) = {np.cosh(x_star):.6f}")

# =============================================================================
# Section 11: The Arctanh Identity
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 11: The Arctanh Identity")
print("=" * 75)

print("""
We have:
  d_* = √2 × arctanh(r_*)

And sinh(d_*/√2) = 32/3 = √(1024/9).

Using the identity sinh(arctanh(r)) = r/√(1-r²):
  sinh(d_*/√2) = sinh(arctanh(r_*)) = r_*/√(1-r_*²)

For r_* = 32/√1033:
  r_*/√(1-r_*²) = (32/√1033) / √(1 - 1024/1033)
                = (32/√1033) / √(9/1033)
                = (32/√1033) × (√1033/3)
                = 32/3 ✓
""")

# Verify
r_star_explicit = 32 / np.sqrt(1033)
one_minus_r_sq = 1 - r_star_explicit**2
sinh_from_r = r_star_explicit / np.sqrt(one_minus_r_sq)
print(f"\nVerification:")
print(f"  r_* = 32/√1033 = {r_star_explicit:.8f}")
print(f"  1 - r_*² = {one_minus_r_sq:.8f}")
print(f"  r_*/√(1-r_*²) = {sinh_from_r:.6f}")
print(f"  Expected 32/3 = {32/3:.6f}")
print(f"  Match: {np.isclose(sinh_from_r, 32/3)}")

# =============================================================================
# Section 12: The 4/π in the Exponent?
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 12: Investigating 4/π in the Exponent")
print("=" * 75)

print("""
The relation N_geo = (4/π) × ln(ξ) can be rewritten using the sinh formula:

  N_geo = (1/2) sinh²(x_*)
  (4/π) × ln(ξ) = (1/2) sinh²(x_*)

Solving:
  sinh(x_*) = √(8 ln(ξ) / π)
  x_* = arcsinh(√(8 ln(ξ) / π))

Let's check if there's a simpler form.
""")

# Compute the argument of arcsinh
arg_arcsinh = np.sqrt(8 * ln_xi / np.pi)
print(f"\n√(8 ln(ξ) / π) = √(8 × {ln_xi:.4f} / π) = {arg_arcsinh:.6f}")
print(f"Compare to 32/3 = {32/3:.6f}")
print(f"Match: {np.isclose(arg_arcsinh, 32/3)}")

# Verify that 8 ln(ξ) / π = (32/3)² = 1024/9
check_val = 8 * ln_xi / np.pi
print(f"\n8 ln(ξ) / π = 8 × (128π/9) / π = 1024/9 = {check_val:.6f}")
print(f"Expected 1024/9 = {1024/9:.6f}")

# =============================================================================
# Section 13: The Algebraic Origin
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 13: The Algebraic Origin of 4/π")
print("=" * 75)

print("""
We now have a clearer picture:

  8 ln(ξ) / π = 1024/9 = (32/3)²

This comes from:
  ln(ξ) = 128π/9
  8 × (128π/9) / π = 1024/9

The factor 8/π comes from combining:
  - The factor 8 in N_geo = (4/π) × ln(ξ) (from 4/π × 2)
  - The factor π from the sinh² → N relationship

Let's verify:
  N_geo = (4/π) × ln(ξ)
        = (4/π) × (128π/9)
        = 512/9

  And sinh²(x_*) = 2 N_geo = 1024/9

  So sinh(x_*) = √(1024/9) = 32/3 ✓
""")

# =============================================================================
# Section 14: The Volume-to-E-fold Conversion
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 14: The Volume-to-E-fold Conversion")
print("=" * 75)

print("""
From the Kähler geometry investigation, we found:
  N = V/(2π)

where V = π r²/(1 - r²) is the Poincaré disk volume.

At r = r_*:
  V_* = π r_*²/(1 - r_*²) = π × (1024/9) / 1 = ...wait, let me recalculate.

Actually:
  V = π × sinh²(x) = π × (r²/(1-r²))   for the full disk integral

So:
  N = V/(2π) = sinh²(x) / 2 = (1/2) sinh²(x)   ✓

This matches our e-fold formula!
""")

# Calculate volumes
V_star = np.pi * sinh_val**2
N_from_V = V_star / (2 * np.pi)
print(f"\nVolume at r_*:")
print(f"  sinh²(x_*) = {sinh_val**2:.6f}")
print(f"  V_* = π × sinh²(x_*) = {V_star:.6f}")
print(f"  N = V_*/(2π) = {N_from_V:.6f}")
print(f"  Target N_geo = {N_geo_target:.6f}")
print(f"  Match: {np.isclose(N_from_V, N_geo_target)}")

# =============================================================================
# Section 15: The Complete Picture
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 15: The Complete Picture")
print("=" * 75)

print("""
SYNTHESIS: The 4/π factor connects three quantities:

1. From QCD bootstrap:
   ln(ξ) = (N_c² - 1)² / (2b₀) = 128π/9

2. From α-attractor geometry:
   N = (1/2) sinh²(x) = V/(2π)

   where x = φ/(√(6α) M_P) and V is the Poincaré disk volume

3. The connection:
   N_geo = (4/π) × ln(ξ)

   This implies:
   sinh²(x_*) = (8/π) × ln(ξ) = (8/π) × (128π/9) = 1024/9

The factor 4/π = (8/π) / 2 arises from:
  - The relation N = (1/2) sinh² (factor of 1/2)
  - The "angular" factor 8/π connecting ln(ξ) to sinh²

WHERE DOES 8/π COME FROM?

Observation: 8/π = 2 × 4/π = 2 × (N_c² - 1)/(2π) for N_c = 3
           = (N_c² - 1)/π = 8/π   ✓

So the complete formula is:
  sinh²(x_*) = [(N_c² - 1)/π] × ln(ξ)
             = [(N_c² - 1)/π] × [(N_c² - 1)² / (2b₀)]

For N_c = 3, N_f = 3:
  b₀ = 9/(4π)
  sinh²(x_*) = (8/π) × (64 / (9/(2π)))
             = (8/π) × (64 × 2π/9)
             = (8/π) × (128π/9)
             = 1024/9   ✓
""")

# =============================================================================
# Section 16: The (N_c² - 1)/π Factor
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 16: The (N_c² - 1)/π Factor")
print("=" * 75)

print("""
The factor 8/π = (N_c² - 1)/π for N_c = 3 suggests:

  sinh²(x_*) = [(N_c² - 1)/π] × ln(ξ)

This is the same as:
  N_geo = (1/2) × [(N_c² - 1)/π] × ln(ξ)
        = [(N_c² - 1)/(2π)] × ln(ξ)
        = (4/π) × ln(ξ)   for N_c = 3

The factor (N_c² - 1)/(2π) = 4/π is the CONVERSION between:
  - The bootstrap hierarchy ln(ξ) (from QCD)
  - The geometric e-folds N_geo (from inflation)

INTERPRETATION:
  - (N_c² - 1) = dim(SU(N_c)) = number of gauge generators
  - 2π = angular period of U(1)
  - The ratio converts "group-theoretic" quantities to "geometric" quantities
""")

print(f"\nNumerical verification:")
print(f"  (N_c² - 1)/(2π) = 8/(2π) = {(N_c**2 - 1)/(2*np.pi):.6f}")
print(f"  4/π = {four_over_pi:.6f}")
print(f"  Match: {np.isclose((N_c**2 - 1)/(2*np.pi), four_over_pi)}")

# =============================================================================
# Section 17: Conclusion
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 17: CONCLUSION")
print("=" * 75)

print("""
FINDINGS FROM HYPERBOLIC EFFICIENCY INVESTIGATION:

1. The "efficiency" N/d is NOT constant across the disk — it varies with r.
   Therefore, 4/π is NOT a universal "slow-roll efficiency."

2. The 4/π factor arises from the SPECIFIC relationship:

   N_geo = (4/π) × ln(ξ)

   This determines the field value φ_* (or equivalently r_*) at horizon exit.

3. The algebraic structure is:

   sinh²(φ_*/√2 M_P) = (8/π) × ln(ξ) = 1024/9

   where 8/π = (N_c² - 1)/π for N_c = 3.

4. The factor 4/π = (N_c² - 1)/(2π) converts between:
   - Group-theoretic data (SU(3) dimension)
   - Angular/geometric data (2π periodicity)

   This is NUMERICALLY EXACT for N_c = 3 only.

5. PHYSICAL INTERPRETATION:
   The 4/π factor represents the ratio:

   (# of gauge generators) / (angular period)
   = dim(SU(3)) / (2π)
   = 8 / (2π)
   = 4/π

STATUS: NOT A DERIVATION

While we understand the algebraic structure of 4/π = (N_c² - 1)/(2π),
this identity only holds for N_c = 3. It's a COINCIDENCE that:
  N_c² - 1 = 8 = 2 × 4

For other values of N_c (2, 4, 5, ...), the factor would be different.
Therefore, 4/π is NOT derived from first principles — it's specific to SU(3).

The question remains: WHY does the SU(3) dimension enter the conversion
between QCD hierarchy and inflationary e-folds?
""")

# =============================================================================
# Section 18: Numerical Summary
# =============================================================================
print("\n" + "=" * 75)
print("SECTION 18: NUMERICAL SUMMARY")
print("=" * 75)

print(f"\nKey values:")
print(f"  N_c = {N_c}")
print(f"  α = {alpha} = 1/3")
print(f"  ln(ξ) = 128π/9 = {ln_xi:.6f}")
print(f"  4/π = (N_c² - 1)/(2π) = {four_over_pi:.6f}")
print(f"  N_geo = 512/9 = {N_geo_target:.6f}")

print(f"\nField values at horizon exit:")
print(f"  r_* = 32/√1033 = {r_star:.8f}")
print(f"  φ_*/M_P = √2 × arctanh(r_*) = {phi_star:.6f}")
print(f"  x_* = φ_*/(√2 M_P) = {x_star:.6f}")
print(f"  sinh(x_*) = 32/3 = {np.sinh(x_star):.6f}")

print(f"\nConversion formula:")
print(f"  sinh²(x_*) = (8/π) × ln(ξ) = 1024/9")
print(f"  N_geo = (1/2) sinh²(x_*) = 512/9")
print(f"  Spectral index: n_s = 1 - 2/N_geo = {1 - 2/N_geo_target:.6f}")

print("\n" + "=" * 75)
print("Script completed successfully")
print("=" * 75)
