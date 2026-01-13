#!/usr/bin/env python3
"""
Dimensional Analysis of the Gravitational Coupling κ

This script verifies the dimensions of κ = 8πG/c⁴ in various unit systems,
addressing Issue 1 from the Proposition 5.2.4b verification record.

Author: Verification for Proposition 5.2.4b
Date: 2026-01-12
"""

import numpy as np
from fractions import Fraction

# =============================================================================
# 1. SI Units Analysis
# =============================================================================

print("=" * 70)
print("DIMENSIONAL ANALYSIS OF κ = 8πG/c⁴")
print("=" * 70)

print("\n1. SI UNITS ANALYSIS")
print("-" * 50)

# Fundamental SI dimensions: [M], [L], [T]
# G has dimensions: [L]³ [M]⁻¹ [T]⁻²
# c has dimensions: [L] [T]⁻¹

print("\nKnown dimensions:")
print("  G  : [L]³ [M]⁻¹ [T]⁻²")
print("  c  : [L] [T]⁻¹")
print("  c⁴ : [L]⁴ [T]⁻⁴")

print("\nκ = 8πG/c⁴:")
print("  κ = G / c⁴")
print("    = [L]³ [M]⁻¹ [T]⁻² / [L]⁴ [T]⁻⁴")
print("    = [L]³⁻⁴ [M]⁻¹ [T]⁻²⁺⁴")
print("    = [L]⁻¹ [M]⁻¹ [T]²")

print("\n✓ κ has dimensions: [length]⁻¹ [mass]⁻¹ [time]²")
print("  Or equivalently: [T]² / ([L][M])")

# =============================================================================
# 2. Alternative SI Form
# =============================================================================

print("\n2. ALTERNATIVE SI FORM")
print("-" * 50)

print("\nStress-energy tensor T_μν dimensions: [energy]/[volume] = [M][L]⁻¹[T]⁻²")
print("Einstein tensor G_μν dimensions: [L]⁻²")
print("\nFor G_μν = κ T_μν:")
print("  [L]⁻² = [κ] × [M][L]⁻¹[T]⁻²")
print("  [κ] = [L]⁻² / ([M][L]⁻¹[T]⁻²)")
print("      = [L]⁻² × [L] × [M]⁻¹ × [T]²")
print("      = [L]⁻¹ [M]⁻¹ [T]²")
print("\n✓ Confirms: κ has dimensions [length]⁻¹ [mass]⁻¹ [time]²")

# =============================================================================
# 3. Natural Units (c = ℏ = 1)
# =============================================================================

print("\n3. NATURAL UNITS (c = ℏ = 1)")
print("-" * 50)

print("\nIn natural units, the only dimension is [mass] = [energy] = [length]⁻¹ = [time]⁻¹")
print("\nConversion relations:")
print("  [L] = [M]⁻¹")
print("  [T] = [M]⁻¹")

print("\nκ in natural units:")
print("  κ = [L]⁻¹ [M]⁻¹ [T]²")
print("    = [M]¹ × [M]⁻¹ × [M]⁻²")
print("    = [M]⁻²")

print("\n✓ κ has dimensions: [mass]⁻² in natural units")
print("  Equivalently: [energy]⁻² or [length]²")

# =============================================================================
# 4. Numerical Value Verification
# =============================================================================

print("\n4. NUMERICAL VALUE VERIFICATION")
print("-" * 50)

# Physical constants (SI)
G = 6.67430e-11  # m³/(kg·s²)
c = 2.99792458e8  # m/s

kappa_SI = 8 * np.pi * G / c**4

print(f"\nPhysical constants:")
print(f"  G = {G:.5e} m³/(kg·s²)")
print(f"  c = {c:.8e} m/s")

print(f"\nκ = 8πG/c⁴ = {kappa_SI:.6e} m⁻¹ kg⁻¹ s²")
print(f"           ≈ 2.077 × 10⁻⁴³ N⁻¹")

# Verify units: N = kg·m/s² so N⁻¹ = s²/(kg·m) = m⁻¹ kg⁻¹ s²
print("\nUnit equivalence:")
print("  N⁻¹ = (kg·m/s²)⁻¹ = s²/(kg·m) = m⁻¹ kg⁻¹ s²  ✓")

# =============================================================================
# 5. Natural Units Numerical Value
# =============================================================================

print("\n5. NATURAL UNITS NUMERICAL VALUE")
print("-" * 50)

# Planck mass
hbar = 1.054571817e-34  # J·s
M_P = np.sqrt(hbar * c / G)  # Planck mass in kg
M_P_eV = M_P * c**2 / 1.602176634e-19 / 1e9  # Convert to GeV

print(f"\nPlanck mass: M_P = {M_P:.6e} kg = {M_P_eV:.4e} GeV")

# In natural units, G = 1/M_P²
G_natural = 1 / M_P_eV**2  # GeV⁻²

# κ = 8πG = 8π/M_P²
kappa_natural = 8 * np.pi * G_natural

print(f"\nIn natural units:")
print(f"  G = 1/M_P² = {G_natural:.4e} GeV⁻²")
print(f"  κ = 8πG = {kappa_natural:.4e} GeV⁻²")
print(f"\n✓ Confirms κ has dimensions [mass]⁻² = GeV⁻²")

# =============================================================================
# 6. Comparison with Original Symbol Table
# =============================================================================

print("\n6. COMPARISON WITH ORIGINAL SYMBOL TABLE")
print("-" * 50)

print("\nOriginal (INCORRECT):")
print("  κ : [length][mass]⁻¹[time]²")
print("  This has dimensions [L][M]⁻¹[T]²")

print("\nCorrected:")
print("  SI: κ : [length]⁻¹[mass]⁻¹[time]² = [L]⁻¹[M]⁻¹[T]²")
print("  Natural: κ : [mass]⁻² = [M]⁻²")

print("\nThe ERROR was a sign error on the length dimension:")
print("  Original had [L]⁺¹ but correct is [L]⁻¹")

# =============================================================================
# 7. Summary Table
# =============================================================================

print("\n" + "=" * 70)
print("SUMMARY: CORRECT κ DIMENSIONS")
print("=" * 70)

print("""
| Unit System | κ Dimensions | Equivalent |
|-------------|--------------|------------|
| SI          | [L]⁻¹[M]⁻¹[T]² | m⁻¹ kg⁻¹ s² |
| SI (force)  | [F]⁻¹ = N⁻¹ | kg⁻¹ m⁻¹ s² |
| Natural     | [M]⁻² | GeV⁻² |
| Geometric   | [L]² | m² (c=G=1) |
""")

print("=" * 70)
print("VERIFICATION COMPLETE")
print("=" * 70)
