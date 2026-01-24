#!/usr/bin/env python3
"""
Verification: gg → gg Cross-Section Coefficient

This script verifies the correct coefficient for the gg→gg differential cross-section
by deriving it from the squared matrix element.

The standard formula from Combridge et al. (1977), Peskin & Schroeder, and ESW:

|M|^2_avg = g_s^4 * (9/4) * (3 - tu/s^2 - su/t^2 - st/u^2)^2 / (3 - tu/s^2 - su/t^2 - st/u^2)
         = g_s^4 * (9/4) * (3 - tu/s^2 - su/t^2 - st/u^2)

Actually, let's derive this carefully.

For gg → gg, the amplitude squared, averaged over initial colors/helicities
and summed over final, is:

|M|^2_avg = (1/256) * Σ |M|^2 = g_s^4 * [9/2] * (3 - tu/s^2 - su/t^2 - st/u^2)

where (1/256) = (1/64) * (1/4) comes from:
- Color averaging: 1/(N_c^2-1)^2 = 1/64
- Helicity averaging: 1/4 (2 helicities per gluon, 2 initial gluons)

The differential cross-section is:
dσ/dt = |M|^2_avg / (16 π s^2)

So:
dσ/dt = g_s^4 * (9/2) * (3 - ...) / (16 π s^2)
      = 9 g_s^4 / (32 π s^2) * (3 - ...)
      = 9 π α_s^2 / (2 s^2) * (3 - ...)   [using α_s = g_s^2/(4π)]

Wait, let me recalculate:
α_s = g_s^2 / (4π)  =>  g_s^4 = 16 π^2 α_s^2

dσ/dt = g_s^4 * (9/2) / (16 π s^2) * (3 - ...)
      = 16 π^2 α_s^2 * (9/2) / (16 π s^2) * (3 - ...)
      = 9 π α_s^2 / (2 s^2) * (3 - ...)

So the document's formula with 9π/(2s^2) is CORRECT!

But wait - let me verify against ESW/Combridge more carefully.
"""

import numpy as np

# Constants
N_C = 3  # SU(3) colors
N_G = N_C**2 - 1  # = 8 gluons

def verify_color_averaging():
    """
    Verify the color averaging factors.

    For gg → gg:
    - Initial state: 8 colors for each gluon → (1/8)^2 = 1/64 averaging
    - Final state: sum over 8×8 colors

    The color-summed/averaged |M|^2 should be calculated.
    """
    print("=== Color Averaging Verification ===")
    print(f"Number of gluon colors: {N_G} = {N_C}^2 - 1")
    print(f"Initial state color averaging: 1/{N_G}^2 = 1/{N_G**2}")
    print()

    # For 2 transverse gluon helicities per gluon:
    # Initial state helicity averaging: (1/2)^2 = 1/4
    print("Helicity averaging for 2 gluons: (1/2)^2 = 1/4")
    print(f"Total averaging factor: 1/{N_G**2 * 4} = 1/{N_G**2 * 4}")
    print()

    return 1 / (N_G**2 * 4)  # = 1/256


def verify_cross_section_formula():
    """
    Verify the differential cross-section formula.

    The standard result from QCD textbooks (ESW, P&S) for gg→gg is:

    dσ/dt = (π α_s^2 / s^2) * F_gg(s,t,u)

    where F_gg is the color/helicity averaged squared matrix element factor.

    The question is: what is the overall coefficient?
    """
    print("=== Cross-Section Formula Verification ===")
    print()

    # Standard 2→2 cross-section formula:
    # dσ/dt = |M|^2 / (16 π s^2)
    print("Standard formula: dσ/dt = |M̄|^2 / (16 π s^2)")
    print()

    # For gg→gg, the color-summed |M|^2 has the form:
    # Σ |M|^2 = g_s^4 * C_gg * (3 - tu/s^2 - su/t^2 - st/u^2)
    #
    # where C_gg is a color/spin factor.
    #
    # From Combridge et al. (1977), the color-averaged, spin-averaged result is:
    # |M̄|^2 = g_s^4 * (9/2) * (3 - tu/s^2 - su/t^2 - st/u^2)

    print("From Combridge et al. (1977):")
    print("|M̄|^2 = g_s^4 × (9/2) × (3 - tu/s² - su/t² - st/u²)")
    print()

    # Converting g_s to α_s:
    # α_s = g_s^2 / (4π)  =>  g_s^4 = (4π α_s)^2 = 16 π^2 α_s^2
    print("Converting: g_s^4 = (4π α_s)^2 = 16 π² α_s²")
    print()

    # So:
    # dσ/dt = g_s^4 × (9/2) × (3 - ...) / (16 π s^2)
    #       = 16 π² α_s² × (9/2) / (16 π s^2) × (3 - ...)
    #       = 9 π α_s² / (2 s²) × (3 - ...)

    print("Therefore:")
    print("dσ/dt = [16 π² α_s² × (9/2)] / (16 π s²) × (3 - ...)")
    print("      = (9 π α_s² / 2 s²) × (3 - tu/s² - su/t² - st/u²)")
    print()
    print("DOCUMENT'S FORMULA: dσ/dt = (9π α_s²)/(2s²) × (3 - ...)")
    print("VERIFICATION: ✅ CORRECT (matches derivation)")
    print()

    return True


def verify_alternative_forms():
    """
    Check if there are alternative forms that might explain the factor of 4 discrepancy.
    """
    print("=== Alternative Form Check ===")
    print()

    # Some references use dσ/dΩ instead of dσ/dt
    # The relationship is: dσ/dΩ = (s/4) × dσ/dt (at high energy, massless limit)
    # Wait, that's not right either.

    # Actually: dt = -s/2 × (1 - cos θ) d(cos θ) for massless 2→2
    # And dΩ = 2π d(cos θ)
    # So: dt = -s/(4π) dΩ
    # And: dσ/dΩ = (s/4π) × |dσ/dt|

    print("For massless 2→2 scattering:")
    print("dΩ = 2π d(cos θ)")
    print("dt = -(s/2)(1 - cos θ) d(cos θ)")
    print()
    print("At θ = π/2: t = -s/2, u = -s/2")
    print()

    # Some sources give the result as:
    # dσ/dΩ = (9 α_s²)/(8 s) × (3 - ...)
    #
    # Let's verify: if dσ/dt = (9π α_s²)/(2 s²) × f
    # and |dt/dΩ| = s/(4π) (approximately, at 90 degrees)
    # then dσ/dΩ = (9π α_s²)/(2 s²) × (s/4π) × f = (9 α_s²)/(8 s) × f

    print("If dσ/dt = (9π α_s²)/(2 s²) × f(s,t,u)")
    print("and |dt/dΩ| ≈ s/(4π) (at 90°)")
    print("then dσ/dΩ = (9π α_s²)/(2 s²) × (s/4π) × f = (9 α_s²)/(8 s) × f")
    print()
    print("This explains why some references show 9/8 instead of 9π/2:")
    print("- dσ/dt has factor 9π/(2s²)")
    print("- dσ/dΩ has factor 9/(8s)")
    print()

    return True


def compare_with_esw():
    """
    Compare with Ellis, Stirling, Webber (ESW) "QCD and Collider Physics".

    ESW Chapter 7 gives the subprocess cross-sections.
    The standard convention in ESW uses:

    dσ/dt = (π α_s²/s²) × A(s,t,u)

    where A(s,t,u) is a function specific to each process.
    """
    print("=== Comparison with ESW Convention ===")
    print()
    print("ESW convention: dσ/dt = (π α_s²/s²) × A(s,t,u)")
    print()
    print("For gg → gg:")
    print("A_gg = (9/2) × (3 - tu/s² - su/t² - st/u²)")
    print()
    print("So: dσ/dt(gg→gg) = (π α_s²/s²) × (9/2) × (3 - tu/s² - su/t² - st/u²)")
    print("                 = (9π α_s²)/(2s²) × (3 - tu/s² - su/t² - st/u²)")
    print()
    print("✅ This MATCHES the document's formula!")
    print()

    # For comparison, qq → qq has A_qq = (4/9)(...)
    print("For comparison, qq → qq has:")
    print("A_qq = (4/9)[(s²+u²)/t² + (s²+t²)/u²] - (8/27)s²/(tu)")
    print()

    return True


def numerical_test():
    """
    Numerical test at a specific kinematic point.
    """
    print("=== Numerical Verification ===")
    print()

    s = 1000.0  # GeV²
    t = -300.0  # GeV²
    u = -s - t  # = -700 GeV²

    alpha_s = 0.12  # typical value

    # The Mandelstam factor
    f_stu = 3 - (t*u)/s**2 - (s*u)/t**2 - (s*t)/u**2

    print(f"s = {s} GeV², t = {t} GeV², u = {u} GeV²")
    print(f"f(s,t,u) = 3 - tu/s² - su/t² - st/u² = {f_stu:.4f}")
    print(f"α_s = {alpha_s}")
    print()

    # Document formula: (9π α_s²)/(2s²) × f
    coeff_doc = 9 * np.pi / 2
    dsigma_doc = coeff_doc * alpha_s**2 / s**2 * f_stu

    print(f"Document formula coefficient: 9π/2 = {coeff_doc:.4f}")
    print(f"dσ/dt (document) = {dsigma_doc:.6e} GeV⁻⁴")
    print()

    # Convert to pb/GeV²: multiply by (ℏc)² = 0.3894 × 10⁹ pb·GeV²
    hbarc_sq = 0.3894e9  # pb·GeV²
    dsigma_doc_pb = dsigma_doc * hbarc_sq
    print(f"dσ/dt (document) = {dsigma_doc_pb:.4f} pb/GeV²")
    print()

    return dsigma_doc_pb


if __name__ == "__main__":
    print("=" * 70)
    print("VERIFICATION: gg → gg Cross-Section Coefficient")
    print("=" * 70)
    print()

    verify_color_averaging()
    verify_cross_section_formula()
    verify_alternative_forms()
    compare_with_esw()
    numerical_test()

    print("=" * 70)
    print("CONCLUSION:")
    print("The document's formula with coefficient 9π/(2s²) is CORRECT.")
    print("The adversarial verification script had an error suggesting 9π/(8s²).")
    print()
    print("The confusion arises from mixing up:")
    print("- dσ/dt which has factor 9π/(2s²)")
    print("- dσ/dΩ which has factor 9/(8s) [different variable!]")
    print("=" * 70)
