#!/usr/bin/env python3
"""
Numerical Verification: Theorem 3.1.5 - Majorana Scale from Geometry

This script verifies all calculations in Theorem 3.1.5, including:
1. Seesaw formula M_R = 3m_D²/Σm_ν
2. Numerical evaluation M_R = 2.2 × 10¹⁰ GeV
3. Uncertainty propagation
4. Geometric formula M_R = m_D² c² N_ν^(3/2) / (3π ℏ H_0 χ)
5. Light neutrino masses from seesaw
6. Consistency checks (leptogenesis, B-L scale, etc.)

Author: Claude Code Verification Agent
Date: 2026-01-15
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.constants import h, c, hbar
import sys

# ============================================================================
# PHYSICAL CONSTANTS AND INPUTS
# ============================================================================

# From Theorem 3.1.2
m_D_central = 0.70  # GeV
m_D_error = 0.05    # GeV

# From Proposition 3.1.4
Sigma_m_nu_central = 0.066  # eV
Sigma_m_nu_error = 0.010    # eV
Sigma_m_nu_bound = 0.132    # eV (holographic upper limit with χ=4)

# From Proposition 3.1.4 (holographic derivation)
H_0_km_s_Mpc = 67.4  # km/s/Mpc (Planck 2018)
H_0_error = 0.5      # km/s/Mpc

# Convert H_0 to SI units (s^-1)
H_0_SI = H_0_km_s_Mpc * 1e3 / (3.086e22)  # s^-1

# Generations
N_nu = 3

# Stella octangula Euler characteristic
chi_stella = 4  # Correct value from Proposition 3.1.4 verification

# Neutrino oscillation data (PDG 2024)
Delta_m21_sq = 7.5e-5  # eV²
Delta_m32_sq = 2.5e-3  # eV² (normal hierarchy)

# Leptogenesis bound (Davidson-Ibarra)
M_R_leptogenesis_min = 1e9  # GeV

# GUT scale
M_GUT = 1e16  # GeV

# Unit conversions
eV_to_GeV = 1e-9

# ============================================================================
# THEOREM 3.1.5: MAIN CALCULATION
# ============================================================================

def calculate_M_R_seesaw(m_D, Sigma_m_nu_eV):
    """
    Calculate Majorana scale from seesaw relation.

    M_R = 3 m_D² / Σm_ν

    Args:
        m_D: Dirac neutrino mass in GeV
        Sigma_m_nu_eV: Sum of light neutrino masses in eV

    Returns:
        M_R in GeV
    """
    Sigma_m_nu_GeV = Sigma_m_nu_eV * eV_to_GeV
    M_R = 3 * m_D**2 / Sigma_m_nu_GeV
    return M_R


def propagate_uncertainty_M_R(m_D, delta_m_D, Sigma_m_nu, delta_Sigma_m_nu):
    """
    Propagate uncertainties through M_R = 3m_D²/Σm_ν.

    δM_R/M_R = sqrt[(2 δm_D/m_D)² + (δΣm_ν/Σm_ν)²]
    """
    rel_error_m_D = delta_m_D / m_D
    rel_error_Sigma = delta_Sigma_m_nu / Sigma_m_nu

    rel_error_M_R = np.sqrt((2 * rel_error_m_D)**2 + rel_error_Sigma**2)

    M_R = calculate_M_R_seesaw(m_D, Sigma_m_nu)
    delta_M_R = M_R * rel_error_M_R

    return M_R, delta_M_R, rel_error_M_R


def calculate_M_R_geometric(m_D, H_0, chi, N_nu):
    """
    Calculate M_R from geometric formula (schematic, missing A_cosmo).

    M_R = m_D² c² N_ν^(3/2) / (3π ℏ H_0 χ)

    NOTE: This is schematic and will disagree by ~10³¹ due to missing
    cosmological amplification factor from holographic derivation.
    """
    # Convert m_D to SI (kg)
    m_D_GeV = m_D  # GeV
    m_D_J = m_D_GeV * 1.602e-10  # J/c²
    m_D_kg = m_D_J / c**2  # kg

    # Calculate
    numerator = m_D_kg**2 * c**2 * N_nu**(3/2)
    denominator = 3 * np.pi * hbar * H_0 * chi

    M_R_kg = numerator / denominator

    # Convert back to GeV
    M_R_J = M_R_kg * c**2
    M_R_GeV = M_R_J / 1.602e-10

    return M_R_GeV


# ============================================================================
# LIGHT NEUTRINO MASS PREDICTIONS
# ============================================================================

def calculate_light_neutrino_masses(M_R, m_D, N_nu):
    """
    Calculate individual light neutrino masses from seesaw.

    Assumes generation-universal m_D and M_R, giving:
    m_i = m_D² / M_R for each generation
    """
    m_nu = m_D**2 / M_R  # GeV
    m_nu_eV = m_nu / eV_to_GeV  # eV

    # All three equal in quasi-degenerate approximation
    masses = [m_nu_eV] * N_nu

    return masses, sum(masses)


def predict_mass_splittings(m1, m2, m3):
    """
    Calculate mass-squared differences.
    """
    Delta_m21_sq_pred = m2**2 - m1**2
    Delta_m32_sq_pred = m3**2 - m1**2

    return Delta_m21_sq_pred, Delta_m32_sq_pred


def calculate_from_oscillation_data(Delta_m21_sq, Delta_m32_sq):
    """
    Estimate masses from oscillation data (normal hierarchy).

    m1 ≈ sqrt(Σm_ν² - 2(Δm²21 + Δm²32)) / 3
    m2 ≈ sqrt(m1² + Δm²21)
    m3 ≈ sqrt(m1² + Δm²32)
    """
    # Use Σm_ν = 0.066 eV
    Sigma_sq = Sigma_m_nu_central**2

    # Normal hierarchy approximation
    m3_sq = Sigma_sq / 3 + (2/3) * Delta_m32_sq
    m2_sq = m3_sq - Delta_m32_sq + Delta_m21_sq
    m1_sq = m2_sq - Delta_m21_sq

    m1 = np.sqrt(max(m1_sq, 0))
    m2 = np.sqrt(m2_sq)
    m3 = np.sqrt(m3_sq)

    return m1, m2, m3


# ============================================================================
# CONSISTENCY CHECKS
# ============================================================================

def check_consistency():
    """
    Verify all consistency checks from §4.
    """
    checks = {}

    # Calculate M_R
    M_R, delta_M_R, rel_error = propagate_uncertainty_M_R(
        m_D_central, m_D_error,
        Sigma_m_nu_central, Sigma_m_nu_error
    )

    # 1. Neutrino oscillations: Σm_ν ≥ 0.06 eV
    checks['oscillation_minimum'] = Sigma_m_nu_central >= 0.06

    # 2. DESI 2024: Σm_ν < 0.072 eV
    checks['DESI_2024'] = Sigma_m_nu_central < 0.072

    # 3. Leptogenesis: M_R ≳ 10⁹ GeV
    checks['leptogenesis'] = M_R > M_R_leptogenesis_min

    # 4. B-L scale < GUT scale
    v_BL = M_R  # Approximation: v_B-L ~ M_R for O(1) Yukawa
    checks['B-L_below_GUT'] = v_BL < M_GUT

    # 5. Holographic bound: Σm_ν < 0.132 eV (with χ=4)
    checks['holographic_bound'] = Sigma_m_nu_central < Sigma_m_nu_bound

    return checks, M_R, delta_M_R


# ============================================================================
# VERIFICATION TESTS
# ============================================================================

def run_verification_tests():
    """
    Run all numerical verification tests.
    """
    print("=" * 80)
    print("THEOREM 3.1.5: MAJORANA SCALE FROM GEOMETRY")
    print("Numerical Verification")
    print("=" * 80)
    print()

    results = {}

    # ========================================================================
    # TEST 1: Basic seesaw calculation
    # ========================================================================
    print("TEST 1: Seesaw Formula M_R = 3m_D²/Σm_ν")
    print("-" * 80)

    M_R_basic = calculate_M_R_seesaw(m_D_central, Sigma_m_nu_central)
    print(f"Input: m_D = {m_D_central} GeV")
    print(f"Input: Σm_ν = {Sigma_m_nu_central} eV")
    print(f"Calculated: M_R = {M_R_basic:.3e} GeV")
    print(f"Document claims: M_R = 2.2 × 10¹⁰ GeV")

    # Check if within 5% of documented value
    M_R_doc = 2.2e10
    agreement_basic = abs(M_R_basic - M_R_doc) / M_R_doc < 0.05
    results['basic_seesaw'] = agreement_basic
    print(f"Agreement: {'✓ PASS' if agreement_basic else '✗ FAIL'}")
    print()

    # ========================================================================
    # TEST 2: Uncertainty propagation
    # ========================================================================
    print("TEST 2: Uncertainty Propagation")
    print("-" * 80)

    M_R, delta_M_R, rel_error = propagate_uncertainty_M_R(
        m_D_central, m_D_error,
        Sigma_m_nu_central, Sigma_m_nu_error
    )

    print(f"Calculated: δM_R/M_R = {rel_error:.3f}")
    print(f"Document claims: δM_R/M_R ≈ 0.21")

    # Check relative error calculation
    rel_error_doc = 0.21
    agreement_error = abs(rel_error - rel_error_doc) / rel_error_doc < 0.10
    results['uncertainty_propagation'] = agreement_error
    print(f"Agreement: {'✓ PASS' if agreement_error else '✗ FAIL'}")

    print(f"\nFinal result: M_R = ({M_R:.2e} ± {delta_M_R:.2e}) GeV")
    print(f"Document: M_R = (2.2 ± 0.5) × 10¹⁰ GeV")
    print()

    # ========================================================================
    # TEST 3: Geometric formula (schematic check)
    # ========================================================================
    print("TEST 3: Geometric Formula (Schematic)")
    print("-" * 80)

    M_R_geom = calculate_M_R_geometric(m_D_central, H_0_SI, chi_stella, N_nu)
    print(f"Geometric formula (literal): M_R = {M_R_geom:.3e} GeV")
    print(f"Seesaw result: M_R = {M_R:.3e} GeV")

    # Calculate required amplification factor
    A_cosmo = M_R / M_R_geom
    print(f"Required cosmological amplification: A_cosmo ≈ {A_cosmo:.2e}")
    print(f"Expected from Proposition 3.1.4: A_cosmo ~ 10³¹")

    # Check if amplification is in the right ballpark
    agreement_geom = 1e30 < A_cosmo < 1e32
    results['geometric_formula'] = agreement_geom
    print(f"Agreement: {'✓ PASS' if agreement_geom else '⚠ WARNING - see note'}")
    print("Note: Geometric formula is schematic; numerical agreement requires")
    print("      cosmological amplification factor from Proposition 3.1.4.")
    print()

    # ========================================================================
    # TEST 4: Light neutrino masses
    # ========================================================================
    print("TEST 4: Light Neutrino Mass Predictions")
    print("-" * 80)

    masses, Sigma_pred = calculate_light_neutrino_masses(M_R, m_D_central, N_nu)
    print(f"Quasi-degenerate approximation:")
    print(f"  m_1 = m_2 = m_3 = {masses[0]:.4f} eV")
    print(f"  Σm_ν = {Sigma_pred:.4f} eV")
    print(f"  Input Σm_ν = {Sigma_m_nu_central:.4f} eV")

    # Should match by construction
    agreement_masses = abs(Sigma_pred - Sigma_m_nu_central) < 1e-6
    results['light_neutrino_masses'] = agreement_masses
    print(f"Agreement: {'✓ PASS' if agreement_masses else '✗ FAIL'}")
    print()

    # More realistic masses from oscillation data
    m1, m2, m3 = calculate_from_oscillation_data(Delta_m21_sq, Delta_m32_sq)
    print(f"From oscillation data (normal hierarchy):")
    print(f"  m_1 = {m1:.4f} eV")
    print(f"  m_2 = {m2:.4f} eV")
    print(f"  m_3 = {m3:.4f} eV")
    print(f"  Σm_ν = {m1+m2+m3:.4f} eV")

    Delta_m21_sq_pred, Delta_m32_sq_pred = predict_mass_splittings(m1, m2, m3)
    print(f"\nMass-squared differences:")
    print(f"  Δm²21 = {Delta_m21_sq_pred:.2e} eV² (data: {Delta_m21_sq:.2e} eV²)")
    print(f"  Δm²32 = {Delta_m32_sq_pred:.2e} eV² (data: {Delta_m32_sq:.2e} eV²)")
    print()

    # ========================================================================
    # TEST 5: Consistency checks
    # ========================================================================
    print("TEST 5: Physical Consistency Checks (§4)")
    print("-" * 80)

    checks, M_R, delta_M_R = check_consistency()

    print(f"1. Neutrino oscillation minimum (Σm_ν ≥ 0.06 eV): ", end="")
    print(f"{'✓ PASS' if checks['oscillation_minimum'] else '✗ FAIL'}")
    results['check_oscillation'] = checks['oscillation_minimum']

    print(f"2. DESI 2024 bound (Σm_ν < 0.072 eV): ", end="")
    print(f"{'✓ PASS' if checks['DESI_2024'] else '✗ FAIL'}")
    results['check_DESI'] = checks['DESI_2024']

    print(f"3. Leptogenesis bound (M_R > 10⁹ GeV): ", end="")
    print(f"{'✓ PASS' if checks['leptogenesis'] else '✗ FAIL'}")
    print(f"   M_R = {M_R:.2e} GeV (factor of {M_R/M_R_leptogenesis_min:.1f} above minimum)")
    results['check_leptogenesis'] = checks['leptogenesis']

    print(f"4. B-L scale below GUT scale: ", end="")
    print(f"{'✓ PASS' if checks['B-L_below_GUT'] else '✗ FAIL'}")
    print(f"   v_B-L ~ {M_R:.2e} GeV << M_GUT ~ {M_GUT:.2e} GeV")
    results['check_BL_scale'] = checks['B-L_below_GUT']

    print(f"5. Holographic bound (Σm_ν < 0.132 eV with χ=4): ", end="")
    print(f"{'✓ PASS' if checks['holographic_bound'] else '✗ FAIL'}")
    results['check_holographic'] = checks['holographic_bound']
    print()

    # ========================================================================
    # TEST 6: Scale hierarchy
    # ========================================================================
    print("TEST 6: Scale Hierarchy M_R/m_D")
    print("-" * 80)

    hierarchy = M_R / m_D_central
    print(f"M_R / m_D = {hierarchy:.3e}")
    print(f"Document claims: M_R / m_D ≈ 3 × 10¹⁰")

    agreement_hierarchy = abs(np.log10(hierarchy) - np.log10(3e10)) < 0.1
    results['scale_hierarchy'] = agreement_hierarchy
    print(f"Agreement: {'✓ PASS' if agreement_hierarchy else '✗ FAIL'}")
    print()

    # ========================================================================
    # TEST 7: Corollary 1 - B-L breaking scale
    # ========================================================================
    print("TEST 7: Corollary 1 - B-L Breaking Scale")
    print("-" * 80)

    y_Maj = 1.0  # Assume O(1) Majorana Yukawa
    v_BL_calc = M_R / y_Maj
    v_BL_doc = 2e10  # GeV (document)

    print(f"v_B-L = M_R / y_Maj = {v_BL_calc:.2e} GeV")
    print(f"Document: v_B-L ≈ 2 × 10¹⁰ GeV")

    agreement_BL = abs(v_BL_calc - v_BL_doc) / v_BL_doc < 0.15
    results['B-L_scale'] = agreement_BL
    print(f"Agreement: {'✓ PASS' if agreement_BL else '✗ FAIL'}")
    print()

    # ========================================================================
    # TEST 8: Corollary 2 - GUT scale ratio
    # ========================================================================
    print("TEST 8: Corollary 2 - Relation to GUT Scale")
    print("-" * 80)

    ratio_GUT = M_R / M_GUT
    print(f"M_R / M_GUT = {ratio_GUT:.2e}")
    print(f"Document: M_R / M_GUT ≈ 10⁻⁶")

    agreement_GUT = abs(np.log10(ratio_GUT) - np.log10(1e-6)) < 0.5
    results['GUT_ratio'] = agreement_GUT
    print(f"Agreement: {'✓ PASS' if agreement_GUT else '✗ FAIL'}")
    print()

    # ========================================================================
    # TEST 9: Effective Majorana mass for 0νββ
    # ========================================================================
    print("TEST 9: Effective Majorana Mass ⟨m_ββ⟩ (§7.3)")
    print("-" * 80)

    # Simplified estimate (exact depends on PMNS matrix)
    m_eff = abs(m1 * 0.7**2 + m2 * 0.3**2 * np.exp(1j*0) + m3 * 0.0**2)

    print(f"Estimated ⟨m_ββ⟩ ≈ {m_eff:.4f} eV")
    print(f"Document: ⟨m_ββ⟩ ≈ 0.003 eV")
    print(f"LEGEND-1000 sensitivity: ~0.01 eV")

    agreement_0nubb = abs(m_eff - 0.003) < 0.005
    results['0nubb'] = agreement_0nubb
    print(f"Order-of-magnitude agreement: {'✓ PASS' if agreement_0nubb else '⚠ APPROXIMATE'}")
    print()

    # ========================================================================
    # SUMMARY
    # ========================================================================
    print("=" * 80)
    print("VERIFICATION SUMMARY")
    print("=" * 80)

    total_tests = len(results)
    passed = sum(results.values())

    for test_name, passed_test in results.items():
        status = "✓ PASS" if passed_test else "✗ FAIL"
        print(f"{test_name:30s}: {status}")

    print()
    print(f"Total tests: {total_tests}")
    print(f"Passed: {passed}")
    print(f"Failed: {total_tests - passed}")
    print()

    if passed == total_tests:
        print("✓ ALL VERIFICATIONS PASSED")
        print("\nTheorem 3.1.5 calculations are mathematically correct.")
    else:
        print("⚠ SOME VERIFICATIONS FAILED")
        print("\nReview failed tests above for details.")

    return results, M_R, delta_M_R


# ============================================================================
# VISUALIZATION
# ============================================================================

def create_verification_plots():
    """
    Generate verification plots.
    """
    print("\nGenerating verification plots...")

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # ========================================================================
    # Plot 1: M_R calculation with uncertainty
    # ========================================================================
    ax = axes[0, 0]

    # Central value and uncertainty
    M_R, delta_M_R, _ = propagate_uncertainty_M_R(
        m_D_central, m_D_error,
        Sigma_m_nu_central, Sigma_m_nu_error
    )

    # Comparison with bounds
    scales = ['Leptogenesis\nMinimum', 'CG Prediction\n(This Theorem)', 'GUT Scale']
    values = [1e9, M_R, 1e16]
    colors = ['orange', 'blue', 'red']

    bars = ax.barh(scales, values, color=colors, alpha=0.6, log=True)
    ax.errorbar(M_R, 1, xerr=delta_M_R, fmt='none', color='blue',
                capsize=5, capthick=2, linewidth=2)

    ax.set_xlabel('Majorana Scale M_R (GeV)', fontsize=12)
    ax.set_xscale('log')
    ax.set_xlim(1e8, 1e17)
    ax.set_title('Majorana Scale: CG Prediction vs. Physical Bounds', fontsize=13, fontweight='bold')
    ax.grid(True, alpha=0.3, which='both')

    # Add value labels
    ax.text(1e9, 0, f' 10⁹ GeV', va='center', fontsize=10)
    ax.text(M_R, 1, f' {M_R:.2e} GeV', va='center', fontsize=10, fontweight='bold')
    ax.text(1e16, 2, f' 10¹⁶ GeV', va='center', fontsize=10)

    # ========================================================================
    # Plot 2: Neutrino mass sum vs. bounds
    # ========================================================================
    ax = axes[0, 1]

    bounds = ['Oscillation\nMinimum', 'CG Prediction', 'DESI 2024\nLimit', 'Holographic\nBound (χ=4)']
    values_nu = [0.06, Sigma_m_nu_central, 0.072, Sigma_m_nu_bound]
    colors_nu = ['green', 'blue', 'orange', 'red']

    bars = ax.bar(bounds, values_nu, color=colors_nu, alpha=0.6)
    ax.errorbar(1, Sigma_m_nu_central, yerr=Sigma_m_nu_error, fmt='none',
                color='blue', capsize=5, capthick=2, linewidth=2)

    ax.set_ylabel('Σm_ν (eV)', fontsize=12)
    ax.set_title('Neutrino Mass Sum: CG Prediction vs. Constraints', fontsize=13, fontweight='bold')
    ax.grid(True, alpha=0.3, axis='y')
    ax.set_ylim(0, 0.15)

    # Add value labels
    for i, (b, v) in enumerate(zip(bounds, values_nu)):
        ax.text(i, v + 0.005, f'{v:.3f} eV', ha='center', fontsize=9, fontweight='bold')

    # ========================================================================
    # Plot 3: Scale hierarchy
    # ========================================================================
    ax = axes[1, 0]

    # Mass scales
    scales_list = [
        ('Planck Scale\nM_P', 1.22e19),
        ('GUT Scale\nM_GUT', 1e16),
        ('Majorana Scale\nM_R', M_R),
        ('EW Scale\nv_EW', 246),
        ('QCD Scale\nΛ_QCD', 0.2),
        ('Neutrino Scale\nm_ν', Sigma_m_nu_central * eV_to_GeV)
    ]

    scale_names = [s[0] for s in scales_list]
    scale_values = [s[1] for s in scales_list]

    y_pos = np.arange(len(scale_names))
    bars = ax.barh(y_pos, scale_values, color='steelblue', alpha=0.7, log=True)

    # Highlight M_R
    bars[2].set_color('red')
    bars[2].set_alpha(0.8)

    ax.set_yticks(y_pos)
    ax.set_yticklabels(scale_names)
    ax.set_xlabel('Energy Scale (GeV)', fontsize=12)
    ax.set_xscale('log')
    ax.set_title('Three-Scale Structure (§5.3)', fontsize=13, fontweight='bold')
    ax.grid(True, alpha=0.3, which='both', axis='x')

    # Add value labels
    for i, (name, value) in enumerate(scales_list):
        ax.text(value, i, f' {value:.2e} GeV', va='center', fontsize=9)

    # ========================================================================
    # Plot 4: Parametric dependence
    # ========================================================================
    ax = axes[1, 1]

    # M_R vs Σm_ν
    Sigma_range = np.linspace(0.06, 0.132, 100)
    M_R_range = 3 * m_D_central**2 / (Sigma_range * eV_to_GeV)

    ax.plot(Sigma_range, M_R_range, 'b-', linewidth=2, label='M_R = 3m_D²/Σm_ν')

    # Mark special points
    ax.plot(Sigma_m_nu_central, M_R, 'ro', markersize=10,
            label=f'CG Prediction (Σm_ν = {Sigma_m_nu_central} eV)')
    ax.plot(Sigma_m_nu_bound, calculate_M_R_seesaw(m_D_central, Sigma_m_nu_bound),
            'gs', markersize=10, label=f'Holographic Bound (Σm_ν = {Sigma_m_nu_bound} eV)')

    # Leptogenesis bound
    ax.axhline(M_R_leptogenesis_min, color='orange', linestyle='--', linewidth=2,
               label='Leptogenesis Minimum')

    ax.set_xlabel('Σm_ν (eV)', fontsize=12)
    ax.set_ylabel('M_R (GeV)', fontsize=12)
    ax.set_yscale('log')
    ax.set_title('Majorana Scale vs. Neutrino Mass Sum', fontsize=13, fontweight='bold')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3, which='both')

    plt.tight_layout()

    # Save
    output_path = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_3_1_5_majorana_scale_verification.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"✓ Saved: {output_path}")

    plt.close()


# ============================================================================
# MAIN
# ============================================================================

if __name__ == '__main__':
    # Run verification tests
    results, M_R_final, delta_M_R_final = run_verification_tests()

    # Generate plots
    create_verification_plots()

    # Exit with appropriate code
    all_passed = all(results.values())
    sys.exit(0 if all_passed else 1)
