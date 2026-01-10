#!/usr/bin/env python3
"""
Proposition 0.0.17t: Central Charge Flow Calculation

Computes the central charges a_UV and a_IR for QCD and compares to the
hierarchy exponent from dimensional transmutation.

This supports the investigation of topological origins for the QCD-Planck hierarchy.
"""

import numpy as np

# =============================================================================
# Physical Constants and QCD Parameters
# =============================================================================

N_c = 3  # Number of colors (SU(3))
N_f = 3  # Number of light quark flavors (u, d, s)

# =============================================================================
# Central Charge Formulas (4D CFT)
# =============================================================================

def central_charge_a(N_s, N_f_dirac, N_v):
    """
    Euler anomaly coefficient 'a' for 4D CFT.

    a = (1/360) * (N_s + 11*N_f + 62*N_v)

    Parameters:
        N_s: Number of real scalars
        N_f_dirac: Number of Dirac fermions
        N_v: Number of vector fields
    """
    return (N_s + 11 * N_f_dirac + 62 * N_v) / 360

def central_charge_c(N_s, N_f_dirac, N_v):
    """
    Weyl anomaly coefficient 'c' for 4D CFT.

    c = (1/120) * (N_s + 6*N_f + 12*N_v)
    """
    return (N_s + 6 * N_f_dirac + 12 * N_v) / 120

# =============================================================================
# UV Calculation: Free QCD (Asymptotic Freedom)
# =============================================================================

def compute_a_UV(N_c, N_f):
    """
    Central charge a in the UV (free QCD limit).

    Degrees of freedom:
    - Gluons: N_v = N_c^2 - 1 (adjoint representation)
    - Quarks: N_f flavors × N_c colors = N_f * N_c Dirac fermions
    """
    N_v = N_c**2 - 1  # Gluons
    N_f_dirac = N_f * N_c  # Quarks (color × flavor)
    N_s = 0  # No scalars in QCD

    return central_charge_a(N_s, N_f_dirac, N_v)

def compute_c_UV(N_c, N_f):
    """Central charge c in the UV."""
    N_v = N_c**2 - 1
    N_f_dirac = N_f * N_c
    N_s = 0

    return central_charge_c(N_s, N_f_dirac, N_v)

# =============================================================================
# IR Calculation: Confined QCD (Pions)
# =============================================================================

def compute_a_IR(N_f):
    """
    Central charge a in the IR (confined phase).

    Degrees of freedom:
    - Pions (Goldstone bosons): N_π = N_f^2 - 1 real pseudoscalars
    - Heavy hadrons decouple at very low energy
    """
    N_s = N_f**2 - 1  # Pions
    N_f_dirac = 0  # No free fermions
    N_v = 0  # No free gauge bosons

    return central_charge_a(N_s, N_f_dirac, N_v)

def compute_c_IR(N_f):
    """Central charge c in the IR."""
    N_s = N_f**2 - 1
    N_f_dirac = 0
    N_v = 0

    return central_charge_c(N_s, N_f_dirac, N_v)

# =============================================================================
# Hierarchy Exponent from Prop 0.0.17q
# =============================================================================

def compute_hierarchy_exponent(N_c, N_f):
    """
    Compute the exponent in R_stella/ℓ_P = exp(exponent).

    exponent = (N_c^2 - 1)^2 / (2 * b_0)

    where b_0 = (11*N_c - 2*N_f) / (12*π)
    """
    dim_adj = N_c**2 - 1
    b_0_numerator = 11 * N_c - 2 * N_f  # The "index" per Costello-Bittleston
    b_0 = b_0_numerator / (12 * np.pi)

    exponent = dim_adj**2 / (2 * b_0)
    return exponent, b_0, b_0_numerator

# =============================================================================
# Main Calculation
# =============================================================================

def main():
    print("=" * 70)
    print("Proposition 0.0.17t: Central Charge Flow and Hierarchy")
    print("=" * 70)
    print()

    # --- UV Calculation ---
    print("## UV Calculation (Free QCD)")
    print("-" * 40)

    a_UV = compute_a_UV(N_c, N_f)
    c_UV = compute_c_UV(N_c, N_f)

    N_v = N_c**2 - 1
    N_f_dirac = N_f * N_c

    print(f"N_c = {N_c} (colors)")
    print(f"N_f = {N_f} (light flavors)")
    print(f"N_v = {N_v} (gluons = N_c² - 1)")
    print(f"N_f^Dirac = {N_f_dirac} (quarks = N_f × N_c)")
    print()
    print(f"a_UV = (0 + 11×{N_f_dirac} + 62×{N_v}) / 360")
    print(f"     = ({11*N_f_dirac} + {62*N_v}) / 360")
    print(f"     = {11*N_f_dirac + 62*N_v} / 360")
    print(f"     = {a_UV:.4f}")
    print()
    print(f"c_UV = (0 + 6×{N_f_dirac} + 12×{N_v}) / 120")
    print(f"     = {c_UV:.4f}")
    print()

    # --- IR Calculation ---
    print("## IR Calculation (Confined QCD)")
    print("-" * 40)

    a_IR = compute_a_IR(N_f)
    c_IR = compute_c_IR(N_f)

    N_pions = N_f**2 - 1

    print(f"Pions (Goldstones): N_π = N_f² - 1 = {N_pions}")
    print()
    print(f"a_IR = ({N_pions} + 0 + 0) / 360")
    print(f"     = {a_IR:.4f}")
    print()
    print(f"c_IR = ({N_pions} + 0 + 0) / 120")
    print(f"     = {c_IR:.4f}")
    print()

    # --- Central Charge Flow ---
    print("## Central Charge Flow (a-Theorem)")
    print("-" * 40)

    Delta_a = a_UV - a_IR
    Delta_c = c_UV - c_IR

    print(f"Δa = a_UV - a_IR = {a_UV:.4f} - {a_IR:.4f} = {Delta_a:.4f}")
    print(f"Δc = c_UV - c_IR = {c_UV:.4f} - {c_IR:.4f} = {Delta_c:.4f}")
    print()
    print(f"a-theorem satisfied: a_UV > a_IR? {a_UV > a_IR} ✓")
    print()

    # --- Hierarchy Exponent ---
    print("## Hierarchy Exponent (Prop 0.0.17q)")
    print("-" * 40)

    exponent, b_0, b_0_numerator = compute_hierarchy_exponent(N_c, N_f)
    dim_adj = N_c**2 - 1

    print(f"dim(adj) = N_c² - 1 = {dim_adj}")
    print(f"b₀ numerator = 11×{N_c} - 2×{N_f} = {b_0_numerator}")
    print(f"b₀ = {b_0_numerator}/(12π) = {b_0:.6f}")
    print()
    print(f"Hierarchy exponent = (N_c²-1)² / (2b₀)")
    print(f"                   = {dim_adj}² / (2 × {b_0:.6f})")
    print(f"                   = {dim_adj**2} / {2*b_0:.6f}")
    print(f"                   = {exponent:.4f}")
    print()
    print(f"R_stella/ℓ_P = exp({exponent:.2f}) ≈ {np.exp(exponent):.2e}")
    print()

    # --- Comparison ---
    print("## Comparison: Δa vs Hierarchy Exponent")
    print("-" * 40)

    ratio = exponent / Delta_a
    Delta_a_eff = dim_adj**2 / exponent  # What Δa_eff would need to be

    print(f"Exponent / Δa = {exponent:.4f} / {Delta_a:.4f} = {ratio:.2f}")
    print()
    print(f"If hierarchy = exp(dim(adj)² / Δa_eff), then:")
    print(f"Δa_eff = dim(adj)² / exponent = {dim_adj**2} / {exponent:.4f} = {Delta_a_eff:.4f}")
    print()
    print(f"Comparison: Δa = {Delta_a:.4f}, Δa_eff = {Delta_a_eff:.4f}")
    print(f"Agreement: {100 * min(Delta_a, Delta_a_eff) / max(Delta_a, Delta_a_eff):.1f}%")
    print()

    # --- Index Interpretation ---
    print("## Index Interpretation (Costello-Bittleston)")
    print("-" * 40)

    print(f"The β-function coefficient b₀ = {b_0_numerator}/(12π) has:")
    print(f"  - Numerator = 11N_c - 2N_f = {b_0_numerator} = 'index(D_β)'")
    print(f"  - The factor 12π converts index to β-function")
    print()
    print(f"Unified conjecture (§6C.2):")
    print(f"  R/ℓ_P = exp([index(D_adj)]² / [2 × index(D_β) / (12π)])")
    print(f"        = exp({dim_adj}² / [2 × {b_0_numerator}/(12π)])")
    print(f"        = exp({dim_adj**2} × 12π / [2 × {b_0_numerator}])")
    print(f"        = exp({dim_adj**2 * 12 * np.pi / (2 * b_0_numerator):.4f})")
    print(f"        = exp({exponent:.4f}) ✓")
    print()

    # --- Summary ---
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("| Quantity | Value |")
    print("|----------|-------|")
    print(f"| a_UV (free QCD) | {a_UV:.4f} |")
    print(f"| a_IR (confined) | {a_IR:.4f} |")
    print(f"| Δa | {Delta_a:.4f} |")
    print(f"| Δa_eff (needed) | {Delta_a_eff:.4f} |")
    print(f"| Agreement | {100 * min(Delta_a, Delta_a_eff) / max(Delta_a, Delta_a_eff):.1f}% |")
    print(f"| Hierarchy exponent | {exponent:.2f} |")
    print(f"| index(D_β) = 11N_c - 2N_f | {b_0_numerator} |")
    print(f"| dim(adj) = N_c² - 1 | {dim_adj} |")
    print()

    # --- Verification Tests ---
    print("=" * 70)
    print("VERIFICATION TESTS")
    print("=" * 70)
    print()

    tests_passed = 0
    tests_total = 6

    # Test 1: a-theorem
    test1 = a_UV > a_IR
    print(f"[{'PASS' if test1 else 'FAIL'}] Test 1: a_UV > a_IR (a-theorem)")
    if test1: tests_passed += 1

    # Test 2: Positive Δa
    test2 = Delta_a > 0
    print(f"[{'PASS' if test2 else 'FAIL'}] Test 2: Δa > 0")
    if test2: tests_passed += 1

    # Test 3: Hierarchy exponent positive
    test3 = exponent > 0
    print(f"[{'PASS' if test3 else 'FAIL'}] Test 3: Hierarchy exponent > 0")
    if test3: tests_passed += 1

    # Test 4: Hierarchy gives ~10^19
    expected_hierarchy = 2.5e19
    actual_hierarchy = np.exp(exponent)
    test4 = 0.1 < actual_hierarchy / expected_hierarchy < 10
    print(f"[{'PASS' if test4 else 'FAIL'}] Test 4: Hierarchy ~ 10^19 (actual: {actual_hierarchy:.1e})")
    if test4: tests_passed += 1

    # Test 5: Agreement Δa vs Δa_eff > 80%
    agreement = min(Delta_a, Delta_a_eff) / max(Delta_a, Delta_a_eff)
    test5 = agreement > 0.80
    print(f"[{'PASS' if test5 else 'FAIL'}] Test 5: Δa vs Δa_eff agreement > 80% (actual: {100*agreement:.1f}%)")
    if test5: tests_passed += 1

    # Test 6: b_0 numerator matches expected
    test6 = b_0_numerator == 27  # 11*3 - 2*3 = 27
    print(f"[{'PASS' if test6 else 'FAIL'}] Test 6: b₀ numerator = 27 (actual: {b_0_numerator})")
    if test6: tests_passed += 1

    print()
    print(f"Tests passed: {tests_passed}/{tests_total}")
    print()

    return tests_passed == tests_total

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
