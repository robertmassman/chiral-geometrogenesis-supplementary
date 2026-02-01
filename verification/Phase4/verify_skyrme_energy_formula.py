#!/usr/bin/env python3
"""
Verify Skyrme Energy Formula Against Literature

The previous calculations gave E < Bogomolny bound, which is impossible.
This script verifies the energy formula against known analytical and numerical results.

Standard Skyrme Energy (static hedgehog, f_π = e = 1):
E = 4π ∫₀^∞ dr [f'² r² + 2sin²f + 2f'²sin²f + sin⁴f/r²]

This can be split into:
- Sigma model part: E_2 = 4π ∫ [f'² r² + 2sin²f] dr  (scales as f_π²)
- Skyrme part: E_4 = 4π ∫ [2f'²sin²f + sin⁴f/r²] dr  (scales as 1/e²)

Bogomolny bound: E ≥ 12π²|B| ≈ 118.44 for B=1

For optimal hedgehog f(r) = 2*arctan(R/r), the energy ratio is:
E/E_Bogomolny ≈ 1.232

Date: 2026-01-31
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
import warnings
warnings.filterwarnings('ignore')

# Bogomolny bound for B=1
BOGOMOLNY = 12 * np.pi**2

print("=" * 70)
print("SKYRME ENERGY FORMULA VERIFICATION")
print("=" * 70)
print(f"\nBogomolny bound for B=1: E_B = 12π² = {BOGOMOLNY:.4f}")
print(f"Expected optimal hedgehog: E ≈ 1.232 × E_B = {1.232 * BOGOMOLNY:.2f}")

# ==============================================================================
# CORRECT SKYRME ENERGY FORMULA
# ==============================================================================

def hedgehog_profile(r, R=1.0):
    """f(r) = 2*arctan(R/r)"""
    if r < 1e-15:
        return np.pi
    return 2 * np.arctan(R / r)

def hedgehog_derivative(r, R=1.0):
    """f'(r) = -2R/(r² + R²)"""
    return -2 * R / (r**2 + R**2)

def skyrme_energy_integrand(r, R=1.0):
    """
    Full Skyrme energy integrand (without 4π factor).

    The Skyrme static energy for hedgehog ansatz is:

    E = 4π ∫₀^∞ dr [ (f_π²/2)(f'²r² + 2sin²f) + (1/e²)(2f'²sin²f + sin⁴f/r²) ]

    With f_π = e = 1 (standard dimensionless units):
    E = 4π ∫₀^∞ dr [ (1/2)(f'²r² + 2sin²f) + (2f'²sin²f + sin⁴f/r²) ]

    NOTE: The literature often uses different conventions. Let me verify against
    Manton & Sutcliffe "Topological Solitons" and other standard references.
    """
    if r < 1e-10:
        return 0.0

    f = hedgehog_profile(r, R)
    fp = hedgehog_derivative(r, R)  # f' = df/dr

    sin_f = np.sin(f)
    sin2_f = sin_f**2
    sin4_f = sin2_f**2
    fp2 = fp**2

    # Sigma model (kinetic) term: (f_π²/2)(f'²r² + 2sin²f)
    # With f_π = 1:
    term_2 = 0.5 * (fp2 * r**2 + 2 * sin2_f)

    # Skyrme (quartic) term: (1/e²)(2f'²sin²f + sin⁴f/r²)
    # With e = 1:
    term_4 = 2 * fp2 * sin2_f + sin4_f / r**2

    return term_2 + term_4

def compute_skyrme_energy(R, r_max=50.0):
    """Compute total Skyrme energy for hedgehog with parameter R."""
    integrand = lambda r: skyrme_energy_integrand(r, R)
    result, error = quad(integrand, 1e-8, r_max, limit=1000)
    return 4 * np.pi * result

# ==============================================================================
# ALTERNATIVE FORMULA (check against different sources)
# ==============================================================================

def skyrme_energy_alt(r, R=1.0):
    """
    Alternative form of Skyrme energy density.

    From Adkins, Nappi, Witten (1983), the static energy is:
    E = (4π/e²) ∫₀^∞ dr [x²f'² + 2B sin²f (1 + f'²) + B² sin⁴f / x²]

    where x = efπr and B = 1/(ef_π)².

    With e = f_π = 1, we have x = r and B = 1:
    E = 4π ∫₀^∞ dr [r²f'² + 2sin²f(1 + f'²) + sin⁴f/r²]
      = 4π ∫₀^∞ dr [r²f'² + 2sin²f + 2f'²sin²f + sin⁴f/r²]

    This matches our formula above!
    """
    if r < 1e-10:
        return 0.0

    f = hedgehog_profile(r, R)
    fp = hedgehog_derivative(r, R)

    sin_f = np.sin(f)
    sin2_f = sin_f**2
    sin4_f = sin2_f**2
    fp2 = fp**2

    # Full integrand
    return r**2 * fp2 + 2*sin2_f + 2*fp2*sin2_f + sin4_f/r**2

def compute_skyrme_energy_alt(R, r_max=50.0):
    """Alternative energy calculation."""
    integrand = lambda r: skyrme_energy_alt(r, R)
    result, error = quad(integrand, 1e-8, r_max, limit=1000)
    return 4 * np.pi * result

# ==============================================================================
# VERIFY FORMULAS GIVE SAME RESULT
# ==============================================================================

print("\n" + "-" * 70)
print("PART 1: Verify different formula forms give same energy")
print("-" * 70)

R_test = 1.0
E1 = compute_skyrme_energy(R_test)
E2 = compute_skyrme_energy_alt(R_test)

print(f"\nFor R = {R_test}:")
print(f"   Formula 1 (separated terms):  E = {E1:.4f}")
print(f"   Formula 2 (combined):         E = {E2:.4f}")
print(f"   Difference: {abs(E1 - E2):.2e}")

# They should differ because Formula 1 has factor 0.5 in sigma term
# Let me fix this...

def skyrme_energy_correct(r, R=1.0):
    """
    CORRECTED Skyrme energy integrand.

    After checking multiple sources, the correct form with f_π = e = 1 is:

    E = 4π ∫₀^∞ dr [ r²f'² + 2sin²f + 2f'²sin²f + sin⁴f/r² ]

    The (1/2) factor in the sigma model term is WRONG - it's already included
    in the definition of f_π in the Lagrangian.
    """
    if r < 1e-10:
        return 0.0

    f = hedgehog_profile(r, R)
    fp = hedgehog_derivative(r, R)

    sin_f = np.sin(f)
    sin2_f = sin_f**2
    sin4_f = sin2_f**2
    fp2 = fp**2

    # Correct formula (no factor of 1/2)
    term_kinetic = r**2 * fp2 + 2*sin2_f
    term_skyrme = 2*fp2*sin2_f + sin4_f/r**2

    return term_kinetic + term_skyrme

def compute_skyrme_energy_correct(R, r_max=50.0):
    """Correct energy calculation."""
    integrand = lambda r: skyrme_energy_correct(r, R)
    result, error = quad(integrand, 1e-8, r_max, limit=1000)
    return 4 * np.pi * result

# ==============================================================================
# VERIFY AGAINST BOGOMOLNY BOUND
# ==============================================================================

print("\n" + "-" * 70)
print("PART 2: Verify energy respects Bogomolny bound")
print("-" * 70)

E_correct = compute_skyrme_energy_correct(R_test)
print(f"\nFor R = {R_test}:")
print(f"   Correct energy:   E = {E_correct:.4f}")
print(f"   Bogomolny bound:  E_B = {BOGOMOLNY:.4f}")
print(f"   Ratio E/E_B:      {E_correct/BOGOMOLNY:.4f}")

if E_correct < BOGOMOLNY:
    print("   ⚠️ STILL BELOW BOUND - formula may still be wrong")
else:
    print("   ✓ Above Bogomolny bound (as expected)")

# ==============================================================================
# SCAN OVER R TO FIND MINIMUM
# ==============================================================================

print("\n" + "-" * 70)
print("PART 3: Find optimal R and minimum energy")
print("-" * 70)

R_values = np.linspace(0.3, 3.0, 28)
E_values = [compute_skyrme_energy_correct(R) for R in R_values]

R_min_idx = np.argmin(E_values)
R_approx = R_values[R_min_idx]
E_approx = E_values[R_min_idx]

print(f"\nCoarse scan (R from 0.3 to 3.0):")
print(f"   Approximate minimum at R ≈ {R_approx:.2f}")
print(f"   Approximate energy E ≈ {E_approx:.2f}")

# Fine-tune
result = minimize_scalar(compute_skyrme_energy_correct, bounds=(0.5, 2.5), method='bounded')
R_optimal = result.x
E_optimal = result.fun

print(f"\nFine-tuned minimum:")
print(f"   R_optimal = {R_optimal:.6f}")
print(f"   E_optimal = {E_optimal:.4f}")
print(f"   E/E_Bogomolny = {E_optimal/BOGOMOLNY:.4f}")

expected_ratio = 1.232
print(f"\n   Expected ratio from literature: 1.232")
print(f"   Our ratio: {E_optimal/BOGOMOLNY:.4f}")
print(f"   Discrepancy: {100*(E_optimal/BOGOMOLNY - expected_ratio)/expected_ratio:+.1f}%")

# ==============================================================================
# VERIFY TOPOLOGICAL CHARGE
# ==============================================================================

print("\n" + "-" * 70)
print("PART 4: Verify topological charge")
print("-" * 70)

def topological_charge_integrand(r, R=1.0):
    """
    Topological charge density.

    B = -(2/π) ∫₀^∞ sin²f × f' dr
      = (1/π)[f - sin(2f)/2]₀^∞

    For f: π → 0 as r: 0 → ∞:
    B = (1/π)[(0-0) - (π-0)] = 1
    """
    f = hedgehog_profile(r, R)
    fp = hedgehog_derivative(r, R)
    return -2/np.pi * np.sin(f)**2 * fp

def compute_topological_charge(R, r_max=50.0):
    integrand = lambda r: topological_charge_integrand(r, R)
    result, _ = quad(integrand, 1e-8, r_max, limit=500)
    return result

B = compute_topological_charge(R_optimal)
print(f"\nTopological charge for R = {R_optimal:.3f}:")
print(f"   B = {B:.6f}")
print(f"   (should be exactly 1)")

# ==============================================================================
# COMPARE SEPARATE TERMS
# ==============================================================================

print("\n" + "-" * 70)
print("PART 5: Energy term breakdown")
print("-" * 70)

def compute_energy_parts(R, r_max=50.0):
    """Compute kinetic and Skyrme parts separately."""
    def kinetic(r):
        if r < 1e-10:
            return 0.0
        f = hedgehog_profile(r, R)
        fp = hedgehog_derivative(r, R)
        return r**2 * fp**2 + 2*np.sin(f)**2

    def skyrme(r):
        if r < 1e-10:
            return 0.0
        f = hedgehog_profile(r, R)
        fp = hedgehog_derivative(r, R)
        sin2 = np.sin(f)**2
        return 2*fp**2*sin2 + sin2**2/r**2

    E_kin, _ = quad(kinetic, 1e-8, r_max, limit=500)
    E_skyrme, _ = quad(skyrme, 1e-8, r_max, limit=500)

    return 4*np.pi*E_kin, 4*np.pi*E_skyrme

E_kin, E_skyrme = compute_energy_parts(R_optimal)
print(f"\nFor optimal R = {R_optimal:.3f}:")
print(f"   Kinetic (sigma model):  E_2 = {E_kin:.4f}")
print(f"   Skyrme (quartic):       E_4 = {E_skyrme:.4f}")
print(f"   Total:                  E = {E_kin + E_skyrme:.4f}")
print(f"   Ratio E_2/E_4:          {E_kin/E_skyrme:.4f}")

# ==============================================================================
# CONCLUSION
# ==============================================================================

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)

if E_optimal > BOGOMOLNY and abs(E_optimal/BOGOMOLNY - 1.232) < 0.1:
    print("\n✓ Energy formula is CORRECT")
    print("✓ Energy respects Bogomolny bound")
    print("✓ Ratio matches literature value (~1.232)")
    print("\nThe earlier result (E < Bogomolny) had an error in the formula.")
elif E_optimal > BOGOMOLNY:
    print("\n✓ Energy respects Bogomolny bound")
    print(f"⚠️ Ratio {E_optimal/BOGOMOLNY:.3f} differs from literature (1.232)")
    print("   This may be due to numerical integration or boundary effects")
else:
    print("\n⚠️ Energy STILL below Bogomolny bound")
    print("   Need to check formula more carefully")

print(f"\nFinal answer:")
print(f"   E_hedgehog = {E_optimal:.4f}")
print(f"   E_Bogomolny = {BOGOMOLNY:.4f}")
print(f"   E/E_B = {E_optimal/BOGOMOLNY:.4f}")
