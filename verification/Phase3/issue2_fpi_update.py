#!/usr/bin/env python3
"""
Issue 2: f_π Update from 93 MeV to 92.1 MeV (PDG 2024)

This script calculates the impact of updating f_π and provides corrected values.

Date: 2025-12-14
"""

import numpy as np

print("=" * 70)
print("ISSUE 2: f_π UPDATE ANALYSIS")
print("=" * 70)

# Old vs new values
f_pi_old = 93.0  # MeV (document value)
f_pi_new = 92.1  # MeV (PDG 2024, Peskin-Schroeder convention)
f_pi_err = 0.6   # MeV uncertainty

print(f"\nOLD VALUE: f_π = {f_pi_old} MeV (document)")
print(f"NEW VALUE: f_π = {f_pi_new} ± {f_pi_err} MeV (PDG 2024)")
print(f"DIFFERENCE: {f_pi_new - f_pi_old:.1f} MeV ({100*(f_pi_new - f_pi_old)/f_pi_old:.2f}%)")

# Parameters
A = 0.25
lambda_coupling = 20.0
factor = (2*A - A**2)**2  # ≈ 0.19

print("\n" + "=" * 70)
print("IMPACT ON DERIVED QUANTITIES")
print("=" * 70)

# B_max = (λ/4)f_π⁴
B_max_old = (lambda_coupling/4) * f_pi_old**4
B_max_new = (lambda_coupling/4) * f_pi_new**4

print(f"\n1. Maximum Bag Constant B_max = (λ/4)f_π⁴:")
print(f"   OLD: B_max^(1/4) = {B_max_old**0.25:.1f} MeV")
print(f"   NEW: B_max^(1/4) = {B_max_new**0.25:.1f} MeV")
print(f"   CHANGE: {B_max_new**0.25 - B_max_old**0.25:.1f} MeV")

# B_eff = 0.19 × B_max
B_eff_old = factor * B_max_old
B_eff_new = factor * B_max_new

print(f"\n2. Effective Bag Constant B_eff = 0.19 × B_max:")
print(f"   OLD: B_eff^(1/4) = {B_eff_old**0.25:.1f} MeV")
print(f"   NEW: B_eff^(1/4) = {B_eff_new**0.25:.1f} MeV")
print(f"   CHANGE: {B_eff_new**0.25 - B_eff_old**0.25:.1f} MeV")

# χ(0) = (1-A)f_π
chi_0_old = (1 - A) * f_pi_old
chi_0_new = (1 - A) * f_pi_new

print(f"\n3. Central Condensate χ(0) = (1-A)f_π:")
print(f"   OLD: χ(0) = {chi_0_old:.2f} MeV")
print(f"   NEW: χ(0) = {chi_0_new:.2f} MeV")
print(f"   CHANGE: {chi_0_new - chi_0_old:.2f} MeV")

# Max gradient |∇χ|_max = Af_π/(σ√e)
sigma = 0.35  # fm
grad_max_old = A * f_pi_old / (sigma * np.sqrt(np.e))
grad_max_new = A * f_pi_new / (sigma * np.sqrt(np.e))

print(f"\n4. Maximum Gradient |∇χ|_max = Af_π/(σ√e):")
print(f"   OLD: |∇χ|_max = {grad_max_old:.1f} MeV/fm")
print(f"   NEW: |∇χ|_max = {grad_max_new:.1f} MeV/fm")
print(f"   CHANGE: {grad_max_new - grad_max_old:.1f} MeV/fm")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)

print("""
IMPACT ASSESSMENT:
   - All changes are < 1%
   - No qualitative changes to physics
   - Precision improved from ~±1% to ±0.6%

RECOMMENDATION:
   Update f_π from 93 MeV to 92.1 MeV
   This is a minor correction for accuracy

SPECIFIC CHANGES NEEDED IN Chi-Profile-Derivation.md:
   1. Line 106: Change "f_π = 93 MeV" → "f_π = 92.1 ± 0.6 MeV (PDG 2024)"
   2. Line 143: Recalculate with 92.1 MeV
   3. Line 222-226: Update numerical values
   4. Lines 282: Update the example formula

NUMERICAL VALUES WITH f_π = 92.1 MeV:
""")

print(f"   v_χ = f_π = {f_pi_new} MeV")
print(f"   χ(0) = (1-A)f_π = {chi_0_new:.1f} MeV")
print(f"   B_max^(1/4) = {B_max_new**0.25:.1f} MeV")
print(f"   B_eff^(1/4) = {B_eff_new**0.25:.1f} MeV")
print(f"   |∇χ|_max = {grad_max_new:.1f} MeV/fm")

# Also compute the 0.66 ratio
ratio = (B_eff_new**0.25) / (B_max_new**0.25)
print(f"   Ratio B_eff^(1/4)/B_max^(1/4) = {ratio:.2f}")

# Save results
import json
results = {
    'f_pi_old_MeV': f_pi_old,
    'f_pi_new_MeV': f_pi_new,
    'f_pi_err_MeV': f_pi_err,
    'percent_change': 100*(f_pi_new - f_pi_old)/f_pi_old,
    'B_max_quarter_old_MeV': B_max_old**0.25,
    'B_max_quarter_new_MeV': B_max_new**0.25,
    'B_eff_quarter_old_MeV': B_eff_old**0.25,
    'B_eff_quarter_new_MeV': B_eff_new**0.25,
    'chi_0_old_MeV': chi_0_old,
    'chi_0_new_MeV': chi_0_new,
    'grad_max_old_MeV_per_fm': grad_max_old,
    'grad_max_new_MeV_per_fm': grad_max_new
}

with open('issue2_fpi_results.json', 'w') as f:
    json.dump(results, f, indent=2)

print("\nResults saved to: issue2_fpi_results.json")
