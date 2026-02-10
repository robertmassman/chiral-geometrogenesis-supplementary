#!/usr/bin/env python3
"""
Theorem 5.3.2: Numerical Discrepancy Investigation
===================================================

The verification found discrepancies between:
- Applications §7.2 claim: 1.7×10⁻¹⁸ mas/yr
- JS §12 verification: 6.8×10⁻²⁰ mas/yr
- Python dimensional resolution: 6.8×10⁻¹⁷ mas/yr

This script investigates the source of these discrepancies.
"""

import numpy as np

# Physical constants
G = 6.67430e-11        # m³/(kg·s²)
c = 299792458.0        # m/s
hbar = 1.054571817e-34 # J·s

print("=" * 70)
print("NUMERICAL DISCREPANCY INVESTIGATION")
print("=" * 70)
print()

# ============================================================================
# STEP 1: Verify constants
# ============================================================================
print("STEP 1: VERIFY CONSTANTS")
print("-" * 50)

kappa_T = np.pi * G / c**4
print(f"κ_T = πG/c⁴ = {kappa_T:.6e} m⁻¹·kg⁻¹·s²")

kappa_T_c2 = kappa_T * c**2
print(f"κ_T × c² = {kappa_T_c2:.6e} m·kg⁻¹")

pi_G_c2 = np.pi * G / c**2
print(f"πG/c² = {pi_G_c2:.6e} m·kg⁻¹")

print(f"κ_T × c² = πG/c²? {np.isclose(kappa_T_c2, pi_G_c2)}")
print()

# ============================================================================
# STEP 2: Verify conversion factor
# ============================================================================
print("STEP 2: VERIFY CONVERSION FACTOR rad/s → mas/yr")
print("-" * 50)

# 1 rad = 180/π degrees = 180×3600×1000/π mas = 206265000 mas
rad_to_mas = 180 * 3600 * 1000 / np.pi
print(f"1 rad = {rad_to_mas:.6e} mas")

# 1 year = 365.25 × 24 × 3600 seconds
year_to_s = 365.25 * 24 * 3600
print(f"1 year = {year_to_s:.6e} s")

# 1 rad/s = rad_to_mas × year_to_s mas/yr
rad_s_to_mas_yr = rad_to_mas * year_to_s
print(f"1 rad/s = {rad_s_to_mas_yr:.6e} mas/yr")
print()

# ============================================================================
# STEP 3: Compute iron spin parameters
# ============================================================================
print("STEP 3: IRON SPIN PARAMETERS")
print("-" * 50)

n_Fe = 8.5e28  # atoms/m³
f_pol = 0.5    # polarization fraction
n_spin = n_Fe * f_pol

print(f"n_Fe = {n_Fe:.2e} atoms/m³")
print(f"Polarization = {f_pol}")
print(f"n_spin = {n_spin:.2e} m⁻³")
print()

# ============================================================================
# STEP 4: Compute J_5 (angular momentum density)
# ============================================================================
print("STEP 4: ANGULAR MOMENTUM DENSITY J_5")
print("-" * 50)

# J_5 = n_spin × ℏ
J_5 = n_spin * hbar

print(f"J_5 = n_spin × ℏ")
print(f"    = {n_spin:.2e} × {hbar:.6e}")
print(f"    = {J_5:.6e} J·s/m³ = [kg·m⁻¹·s⁻¹]")
print()

# ============================================================================
# STEP 5: Compute precession rate
# ============================================================================
print("STEP 5: PRECESSION RATE CALCULATION")
print("-" * 50)

# Method A: Using κ_T c²
Omega_A = kappa_T_c2 * J_5
print(f"Method A: Ω = κ_T × c² × J_5")
print(f"         = {kappa_T_c2:.6e} × {J_5:.6e}")
print(f"         = {Omega_A:.6e} rad/s")
print()

# Method B: Using πG/c²
Omega_B = pi_G_c2 * J_5
print(f"Method B: Ω = (πG/c²) × J_5")
print(f"         = {pi_G_c2:.6e} × {J_5:.6e}")
print(f"         = {Omega_B:.6e} rad/s")
print()

print(f"Methods agree? {np.isclose(Omega_A, Omega_B)}")
print()

# ============================================================================
# STEP 6: Convert to mas/yr
# ============================================================================
print("STEP 6: CONVERT TO mas/yr")
print("-" * 50)

Omega_mas_yr = Omega_A * rad_s_to_mas_yr
print(f"Ω = {Omega_A:.6e} rad/s × {rad_s_to_mas_yr:.6e} mas·s/(rad·yr)")
print(f"  = {Omega_mas_yr:.6e} mas/yr")
print()

# ============================================================================
# STEP 7: Compare with JS verification output
# ============================================================================
print("STEP 7: COMPARE WITH JS VERIFICATION")
print("-" * 50)

# From the JS code output in §12.2:
# "Torsion precession: 1.050e-32 rad/s"
# "Torsion precession: 6.827e-20 mas/yr"

js_rad_s = 1.050e-32
js_mas_yr = 6.827e-20

print(f"JS output:")
print(f"  Ω = {js_rad_s:.3e} rad/s")
print(f"  Ω = {js_mas_yr:.3e} mas/yr")
print()

# Check conversion
js_converted = js_rad_s * rad_s_to_mas_yr
print(f"JS rad/s converted to mas/yr:")
print(f"  {js_rad_s:.3e} × {rad_s_to_mas_yr:.3e} = {js_converted:.3e} mas/yr")
print()

# The JS output says 6.8e-20 but the calculation gives ~6.8e-17
# This is a factor of 1000 difference!
print("⚠️  DISCREPANCY FOUND!")
print(f"  JS claims: {js_mas_yr:.3e} mas/yr")
print(f"  Converting JS rad/s: {js_converted:.3e} mas/yr")
print(f"  Ratio: {js_converted / js_mas_yr:.1f}")
print()

# ============================================================================
# STEP 8: Check the JS conversion factor
# ============================================================================
print("STEP 8: CHECK JS CONVERSION FACTOR")
print("-" * 50)

# From the JS code:
# const rad_to_mas_per_yr = (180 * 3600 * 1000 / Math.PI) * (365.25 * 24 * 3600);
# Expected: 6.501e+12 (from JS output line 393)

js_conv = 6.501e12  # From JS output
print(f"JS conversion factor: {js_conv:.3e}")
print(f"Python conversion factor: {rad_s_to_mas_yr:.3e}")
print(f"Ratio: {rad_s_to_mas_yr / js_conv:.6f}")
print()

# They should be equal!
if np.isclose(rad_s_to_mas_yr, js_conv, rtol=0.01):
    print("✓ Conversion factors match")
else:
    print("✗ Conversion factors DON'T match!")
print()

# ============================================================================
# STEP 9: Identify the error
# ============================================================================
print("STEP 9: IDENTIFY THE ERROR")
print("-" * 50)

# The JS output line 463 says:
# "Torsion precession: 6.827e-20 mas/yr"
# But if Ω = 1.050e-32 rad/s, then:
# Ω = 1.050e-32 × 6.501e12 = 6.826e-20 mas/yr

# Wait - let me recalculate:
check = 1.050e-32 * 6.501e12
print(f"Check: {1.050e-32:.3e} rad/s × {6.501e12:.3e} = {check:.3e} mas/yr")
print()

# The JS IS correct!
# The issue is that 6.501e12 ≠ 6.509e15

print("The ACTUAL Python conversion should be:")
print(f"  {rad_to_mas:.6e} mas/rad × {year_to_s:.6e} s/yr")
print(f"  = {rad_to_mas * year_to_s:.6e}")
print()

# Let me recalculate step by step:
print("Step-by-step:")
print(f"  180 × 3600 × 1000 / π = {180 * 3600 * 1000 / np.pi:.6e}")
print(f"  365.25 × 24 × 3600 = {365.25 * 24 * 3600:.6e}")
print(f"  Product = {(180 * 3600 * 1000 / np.pi) * (365.25 * 24 * 3600):.6e}")
print()

# ============================================================================
# STEP 10: Find the issue
# ============================================================================
print("STEP 10: THE ISSUE")
print("-" * 50)

correct_conv = (180 * 3600 * 1000 / np.pi) * (365.25 * 24 * 3600)
print(f"Correct conversion: {correct_conv:.6e}")
print()

# Now compute correctly:
Omega_correct_mas_yr = Omega_A * correct_conv
print(f"Correct Ω in mas/yr:")
print(f"  = {Omega_A:.6e} rad/s × {correct_conv:.6e}")
print(f"  = {Omega_correct_mas_yr:.6e} mas/yr")
print()

# Compare with JS:
print("Comparison:")
print(f"  Python Ω: {Omega_A:.6e} rad/s")
print(f"  JS Ω:     {js_rad_s:.3e} rad/s")
print(f"  Ratio:    {Omega_A / js_rad_s:.3f}")
print()

# THE DISCREPANCY IS IN THE RAD/S VALUE!
# Python: 1.046e-32 rad/s
# JS:     1.050e-32 rad/s
# These are essentially the same.

# So the mas/yr values should also be the same:
print(f"  Python mas/yr: {Omega_A * correct_conv:.6e}")
print(f"  JS mas/yr:     {js_mas_yr:.3e}")
print(f"  Ratio:         {Omega_A * correct_conv / js_mas_yr:.3f}")
print()

# They differ by a factor of ~1000!

# Wait, let me check my calculation of Omega_A again
print("=" * 70)
print("RECHECKING CALCULATION")
print("=" * 70)
print()

# The formula is Ω = κ_T × c² × J_5
# where J_5 = n_spin × ℏ

print(f"κ_T = {kappa_T:.10e}")
print(f"c² = {c**2:.10e}")
print(f"κ_T × c² = {kappa_T * c**2:.10e}")
print()

print(f"n_spin = {n_spin:.10e}")
print(f"ℏ = {hbar:.10e}")
print(f"J_5 = n_spin × ℏ = {n_spin * hbar:.10e}")
print()

print(f"Ω = κ_T × c² × J_5")
print(f"  = {kappa_T * c**2:.10e} × {n_spin * hbar:.10e}")
print(f"  = {kappa_T * c**2 * n_spin * hbar:.10e} rad/s")
print()

# That's 1.046e-32 rad/s - matches JS's 1.050e-32 rad/s

# Now convert to mas/yr:
Omega_final = kappa_T * c**2 * n_spin * hbar
Omega_final_mas = Omega_final * correct_conv

print(f"In mas/yr:")
print(f"  {Omega_final:.10e} rad/s × {correct_conv:.10e}")
print(f"  = {Omega_final_mas:.10e} mas/yr")
print()

# That's 6.8e-17 mas/yr, but JS says 6.8e-20!
# Factor of 1000 difference

# THE BUG IS IN THE APPLICATIONS FILE'S CONVERSION!
# Let me check what 6.501e12 vs the correct value

print("THE BUG:")
print(f"  Correct conversion: {correct_conv:.3e}")
print(f"  JS used:           6.501e+12")
print()

# Oh wait - 6.501e12 IS correct!
# Let me verify the JS more carefully

# Actually, the issue is different. Let me trace through the JS:
# Line 462: const Omega_torsion_Fe = torsionPrecession(J5_Fe);
# torsionPrecession returns kappa_T * c * c * J5
# Then it multiplies by rad_to_mas_per_yr

# Let me verify the JS calculation manually:
print("JS calculation trace:")
kappa_T_js = np.pi * G / c**4
J5_Fe_js = n_spin * hbar  # Same as Python

Omega_js_check = kappa_T_js * c * c * J5_Fe_js
print(f"  κ_T × c² × J_5 = {Omega_js_check:.6e} rad/s")

rad_to_mas_per_yr_js = (180 * 3600 * 1000 / np.pi) * (365.25 * 24 * 3600)
print(f"  rad_to_mas_per_yr = {rad_to_mas_per_yr_js:.6e}")

Omega_js_mas = Omega_js_check * rad_to_mas_per_yr_js
print(f"  Final: {Omega_js_mas:.6e} mas/yr")
print()

# WAIT - the JS output says 6.827e-20 but we calculate 6.8e-17
# That's a factor of 1000 different!

# Looking at the JS code more carefully...
# Line 413-415:
# function torsionPrecession(J5) {
#     return kappa_T * c * c * J5;
# }

# The issue might be that the JS expected output in §12.2 is WRONG
# because it was copy-pasted incorrectly or there's a bug in the JS

print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()

print("The JavaScript expected output in §12.2 appears to have an error.")
print("The claimed output '6.827e-20 mas/yr' should be '6.806e-17 mas/yr'.")
print()
print("This is likely a typo or copy-paste error in the proof document.")
print()
print("CORRECT VALUES:")
print(f"  Ω_torsion = {Omega_final:.3e} rad/s")
print(f"            = {Omega_final_mas:.3e} mas/yr")
print()

# Also check the §7.2 claimed value
print("Comparison with §7.2 claim:")
print(f"  §7.2 claims: 1.7×10⁻¹⁸ mas/yr")
print(f"  Correct:     {Omega_final_mas:.3e} mas/yr")
print(f"  Ratio:       {Omega_final_mas / 1.7e-18:.1f}")
print()

# The §7.2 value is also wrong by a factor of ~40

print("=" * 70)
print("FINAL ANSWER")
print("=" * 70)
print()
print("Both the §7.2 text AND the §12.2 JS expected output are WRONG.")
print()
print("CORRECTIONS NEEDED:")
print("  1. §7.2 line 187: Change '1.7×10⁻¹⁸' to '6.8×10⁻¹⁷' mas/yr")
print("  2. §12.2 expected output: Change '6.827e-20' to '6.806e-17' mas/yr")
print()
print("The dimensional analysis IS correct:")
print("  Ω = (πG/c²) × (n_spin × ℏ)")
print("    = (2.33×10⁻²⁷ m/kg) × (4.48×10⁻⁶ J·s/m³)")
print("    = 1.05×10⁻³² rad/s")
print("    = 6.8×10⁻¹⁷ mas/yr")
