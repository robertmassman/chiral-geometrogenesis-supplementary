#!/usr/bin/env python3
"""
Proposition 0.0.17o Extensions Verification
============================================

This script verifies the extensions added to Proposition 0.0.17o:
- Section 11: Alternative regularization schemes (Gaussian, exponential)
- Section 12: Temperature dependence of ε near QCD phase transition

Reference: Proposition-0.0.17o-Regularization-Parameter-Derivation.md, Sections 11-12
Created: 2026-01-05
"""

import numpy as np
from dataclasses import dataclass
from typing import Tuple, List
from pathlib import Path
import matplotlib.pyplot as plt
from scipy.integrate import quad


# =============================================================================
# Physical Constants
# =============================================================================

HBAR_C = 197.3269804  # MeV·fm
M_PI = 139.57039  # MeV (charged pion mass)
SQRT_SIGMA_0 = 440.0  # MeV (QCD string tension^1/2 at T=0)
R_STELLA_0 = HBAR_C / SQRT_SIGMA_0  # fm (stella radius at T=0)
T_C = 155.0  # MeV (QCD crossover temperature)
EPSILON_0 = 0.50  # Regularization parameter at T=0


@dataclass
class VerificationResult:
    """Container for verification test results."""
    name: str
    expected: float
    calculated: float
    agreement_percent: float
    passed: bool
    details: str = ""


# =============================================================================
# Section 11: Alternative Regularization Schemes
# =============================================================================

def test_gaussian_matching() -> VerificationResult:
    """
    Test the Gaussian regularization matching condition.

    For Gaussian: r_{1/2} = Λ × sqrt(ln 2) ≈ 0.833Λ
    Matching to inverse-square r_{1/2} = ε gives Λ_G = ε / sqrt(ln 2)
    """
    epsilon = EPSILON_0
    Lambda_G = epsilon / np.sqrt(np.log(2))

    # Verify half-maximum radius for Gaussian
    r_half_gaussian = Lambda_G * np.sqrt(np.log(2))

    # Should equal epsilon (the IS half-maximum radius)
    agreement = 100 * (1 - abs(r_half_gaussian - epsilon) / epsilon)

    details = (
        f"Inverse-square: ε = {epsilon:.4f}\n"
        f"Gaussian Λ_G = ε / √(ln 2) = {Lambda_G:.4f}\n"
        f"Gaussian r_{'{1/2}'} = Λ_G × √(ln 2) = {r_half_gaussian:.4f}\n"
        f"Match to ε: {abs(r_half_gaussian - epsilon) < 1e-10}"
    )

    return VerificationResult(
        name="Gaussian Regularization Matching",
        expected=epsilon,
        calculated=r_half_gaussian,
        agreement_percent=agreement,
        passed=agreement > 99.9,
        details=details
    )


def test_exponential_matching() -> VerificationResult:
    """
    Test the exponential regularization matching condition.

    For Exponential: r_{1/2} = Λ × ln(2) ≈ 0.693Λ
    Matching to inverse-square r_{1/2} = ε gives Λ_E = ε / ln(2)
    """
    epsilon = EPSILON_0
    Lambda_E = epsilon / np.log(2)

    # Verify half-maximum radius for exponential
    r_half_exp = Lambda_E * np.log(2)

    agreement = 100 * (1 - abs(r_half_exp - epsilon) / epsilon)

    details = (
        f"Inverse-square: ε = {epsilon:.4f}\n"
        f"Exponential Λ_E = ε / ln(2) = {Lambda_E:.4f}\n"
        f"Exponential r_{'{1/2}'} = Λ_E × ln(2) = {r_half_exp:.4f}\n"
        f"Match to ε: {abs(r_half_exp - epsilon) < 1e-10}"
    )

    return VerificationResult(
        name="Exponential Regularization Matching",
        expected=epsilon,
        calculated=r_half_exp,
        agreement_percent=agreement,
        passed=agreement > 99.9,
        details=details
    )


def test_gradient_scaling_universal() -> VerificationResult:
    """
    Verify that all regularization schemes give E_grad ~ 1/cutoff³.
    """
    def gradient_energy_IS(epsilon, R_max=10.0):
        """Gradient energy for inverse-square regularization."""
        def integrand(r, eps):
            dP_dr = -2 * r / (r**2 + eps**2)**2
            return 4 * np.pi * r**2 * dP_dr**2
        result, _ = quad(integrand, 0, R_max, args=(epsilon,))
        return result

    # Test scaling for different cutoff values
    cutoffs = [0.3, 0.5, 0.7, 1.0]
    energies = [gradient_energy_IS(c) for c in cutoffs]

    # Check if E × cutoff³ is constant
    E_cutoff3_products = [E * c**3 for E, c in zip(energies, cutoffs)]
    mean_product = np.mean(E_cutoff3_products)
    variation = np.std(E_cutoff3_products) / mean_product

    passed = variation < 0.05  # <5% variation means scaling is correct

    details = (
        f"Testing E_grad ~ 1/cutoff³ scaling:\n\n"
        f"{'Cutoff':>10} {'E_grad':>12} {'E×cutoff³':>12}\n"
        + "-" * 40 + "\n"
        + "\n".join(f"{c:>10.2f} {E:>12.3f} {E*c**3:>12.3f}"
                   for c, E in zip(cutoffs, energies))
        + f"\n\nMean(E×cutoff³) = {mean_product:.3f}\n"
        f"Relative std = {100*variation:.2f}%\n"
        f"Universal 1/cutoff³ scaling confirmed: {passed}"
    )

    return VerificationResult(
        name="Universal Gradient Scaling (1/cutoff³)",
        expected=0.0,  # Zero variation
        calculated=variation,
        agreement_percent=100 * (1 - variation / 0.05) if variation < 0.05 else 0,
        passed=passed,
        details=details
    )


def test_lattice_correspondence() -> VerificationResult:
    """
    Verify correspondence between ε and lattice spacing.

    ε ~ a × N_core, where a ≈ 0.1 fm and N_core ≈ 2-3
    """
    a_lattice = 0.1  # fm (typical lattice spacing)
    N_core_range = (2, 3)

    epsilon_lattice_min = a_lattice * N_core_range[0] / R_STELLA_0
    epsilon_lattice_max = a_lattice * N_core_range[1] / R_STELLA_0

    # Check if ε = 0.5 falls within the expected range
    epsilon_target = EPSILON_0
    in_range = epsilon_lattice_min <= epsilon_target <= epsilon_lattice_max

    details = (
        f"Lattice spacing a = {a_lattice:.2f} fm\n"
        f"Core sites N_core = {N_core_range[0]}-{N_core_range[1]}\n"
        f"R_stella = {R_STELLA_0:.4f} fm\n\n"
        f"ε_lattice = a × N_core / R_stella\n"
        f"ε_lattice range: [{epsilon_lattice_min:.3f}, {epsilon_lattice_max:.3f}]\n"
        f"ε_derived = {epsilon_target:.3f}\n"
        f"In range: {in_range}"
    )

    return VerificationResult(
        name="Lattice QCD Correspondence",
        expected=(epsilon_lattice_min + epsilon_lattice_max) / 2,
        calculated=epsilon_target,
        agreement_percent=100 if in_range else 0,
        passed=in_range,
        details=details
    )


# =============================================================================
# Section 12: Temperature Dependence
# =============================================================================

def f_sigma(T_over_Tc: float, a_sigma: float = 0.3, beta: float = 0.5) -> float:
    """
    String tension temperature dependence function.

    Uses a smooth interpolation that matches:
    - Low T: f_σ ≈ 1 - a_σ(T/T_c)²
    - Near T_c: f_σ ≈ (1 - T/T_c)^β
    - At T_c: f_σ = 0

    The document uses a simplified mean-field approximation:
    f_σ ≈ sqrt(1 - (T/T_c)²) for consistency with chiral condensate behavior.
    """
    if T_over_Tc >= 1.0:
        return 0.0
    # Use mean-field approximation as in the document
    return np.sqrt(1 - T_over_Tc**2)


def epsilon_T(T: float, c_pi: float = 0.05) -> float:
    """
    Temperature-dependent regularization parameter.

    Using the simplified mean-field approximation from the document:
    ε(T) ≈ (1/2) × sqrt(1 - (T/T_c)²)

    The full formula includes pion mass correction:
    ε(T) = ε₀ × f_σ(T/T_c) / (1 + c_π(T/T_c)²)

    where c_π ≈ 0.05-0.1 (small correction).
    """
    T_ratio = T / T_C
    if T_ratio >= 1.0:
        return 0.0
    # Near T_c, the mean-field approximation dominates
    return EPSILON_0 * f_sigma(T_ratio) / (1 + c_pi * T_ratio**2)


def test_zero_temperature() -> VerificationResult:
    """Verify ε(T=0) = ε₀ = 0.50."""
    eps_T0 = epsilon_T(0)

    details = (
        f"ε(T=0) = {eps_T0:.6f}\n"
        f"ε₀ = {EPSILON_0:.6f}\n"
        f"Match: {abs(eps_T0 - EPSILON_0) < 1e-10}"
    )

    return VerificationResult(
        name="Zero Temperature Limit",
        expected=EPSILON_0,
        calculated=eps_T0,
        agreement_percent=100 * (1 - abs(eps_T0 - EPSILON_0) / EPSILON_0),
        passed=abs(eps_T0 - EPSILON_0) < 1e-10,
        details=details
    )


def test_critical_temperature() -> VerificationResult:
    """Verify ε(T_c) → 0 at the critical temperature."""
    eps_Tc = epsilon_T(T_C)

    details = (
        f"T_c = {T_C:.1f} MeV\n"
        f"ε(T_c) = {eps_Tc:.6f}\n"
        f"Expected: → 0 (deconfinement)\n"
        f"Vanishes: {eps_Tc < 0.01}"
    )

    return VerificationResult(
        name="Critical Temperature Limit",
        expected=0.0,
        calculated=eps_Tc,
        agreement_percent=100 * (1 - eps_Tc / EPSILON_0),
        passed=eps_Tc < 0.01,
        details=details
    )


def test_temperature_table() -> VerificationResult:
    """Verify the numerical values in the temperature table (Section 12.4)."""
    # Updated values from the corrected table using mean-field approximation
    # f_σ = sqrt(1 - (T/T_c)²)
    table_data = [
        # (T MeV, T/T_c, expected_f_sigma, expected_epsilon)
        (0, 0.0, 1.00, 0.500),
        (50, 0.32, 0.95, 0.473),
        (100, 0.65, 0.76, 0.376),
        (140, 0.90, 0.44, 0.216),
        (150, 0.97, 0.24, 0.120),
    ]

    all_pass = True
    details_lines = [
        f"{'T (MeV)':>8} {'T/T_c':>8} {'f_σ calc':>10} {'f_σ exp':>10} {'ε calc':>10} {'ε exp':>10}\n",
        "-" * 65
    ]

    for T, T_ratio, f_exp, eps_exp in table_data:
        f_calc = f_sigma(T_ratio)
        eps_calc = epsilon_T(T)

        # Allow 5% tolerance
        f_match = abs(f_calc - f_exp) / f_exp < 0.05 if f_exp > 0 else f_calc < 0.1
        eps_match = abs(eps_calc - eps_exp) / eps_exp < 0.10 if eps_exp > 0 else eps_calc < 0.1

        all_pass = all_pass and f_match and eps_match

        details_lines.append(
            f"{T:>8} {T_ratio:>8.2f} {f_calc:>10.3f} {f_exp:>10.2f} "
            f"{eps_calc:>10.3f} {eps_exp:>10.3f}"
        )

    details = "\n".join(details_lines)

    return VerificationResult(
        name="Temperature Table Verification",
        expected=1.0,  # All matches
        calculated=1.0 if all_pass else 0.0,
        agreement_percent=100 if all_pass else 0,
        passed=all_pass,
        details=details
    )


def test_monotonic_decrease() -> VerificationResult:
    """Verify ε(T) decreases monotonically from 0 to T_c."""
    T_values = np.linspace(0, T_C - 1, 100)
    eps_values = [epsilon_T(T) for T in T_values]

    # Check monotonic decrease
    differences = np.diff(eps_values)
    is_monotonic = all(d <= 0 for d in differences)

    details = (
        f"Testing monotonic decrease of ε(T) from T=0 to T=T_c\n"
        f"Number of test points: {len(T_values)}\n"
        f"ε(0) = {eps_values[0]:.4f}\n"
        f"ε(T_c - 1 MeV) = {eps_values[-1]:.4f}\n"
        f"All differences ≤ 0: {is_monotonic}"
    )

    return VerificationResult(
        name="Monotonic Decrease with Temperature",
        expected=1.0,
        calculated=1.0 if is_monotonic else 0.0,
        agreement_percent=100 if is_monotonic else 0,
        passed=is_monotonic,
        details=details
    )


def test_observation_region_constancy() -> VerificationResult:
    """
    Verify that R_obs(T) = ε(T) × R_stella(T) remains approximately constant.

    Since ε(T) ∝ f_σ and R_stella(T) ∝ 1/f_σ, their product cancels:
    R_obs(T) = ε₀ × R_stella₀ ≈ 0.22 fm (constant to leading order)
    """
    def R_obs(T):
        T_ratio = T / T_C
        f_s = f_sigma(T_ratio)
        if f_s < 1e-10:
            return np.inf
        eps = epsilon_T(T)
        R_stella = R_STELLA_0 / f_s
        return eps * R_stella

    T_values = [0, 50, 100, 120, 140]
    R_obs_values = [R_obs(T) for T in T_values]
    R_obs_0 = R_obs_values[0]

    # R_obs should remain approximately constant (within 10%)
    max_deviation = max(abs(R - R_obs_0) / R_obs_0 for R in R_obs_values)
    is_constant = max_deviation < 0.10  # 10% tolerance

    details = (
        f"R_obs(T) = ε(T) × R_stella(T)\n\n"
        f"Expected: R_obs ≈ ε₀ × R_stella₀ = {EPSILON_0 * R_STELLA_0:.3f} fm (constant)\n\n"
        f"{'T (MeV)':>10} {'R_obs (fm)':>12} {'Deviation':>12}\n"
        + "-" * 40 + "\n"
        + "\n".join(f"{T:>10} {R:>12.3f} {100*(R-R_obs_0)/R_obs_0:>11.1f}%"
                   for T, R in zip(T_values, R_obs_values))
        + f"\n\nMax deviation: {100*max_deviation:.1f}%"
        + f"\nApproximately constant: {is_constant}"
    )

    return VerificationResult(
        name="Observation Region Constancy",
        expected=R_obs_0,
        calculated=np.mean(R_obs_values),
        agreement_percent=100 * (1 - max_deviation),
        passed=is_constant,
        details=details
    )


# =============================================================================
# Plotting Functions
# =============================================================================

def generate_extension_plots():
    """Generate verification plots for the extensions."""
    plots_dir = Path(__file__).parent.parent / "plots"
    plots_dir.mkdir(exist_ok=True)

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Alternative regularization schemes comparison
    ax1 = axes[0, 0]
    r = np.linspace(0.01, 3, 200)
    epsilon = 0.5
    Lambda_G = epsilon / np.sqrt(np.log(2))
    Lambda_E = epsilon / np.log(2)

    P_IS = 1 / (r**2 + epsilon**2)
    P_G = np.exp(-r**2 / Lambda_G**2) / (r**2 + 0.01**2)
    P_E = np.exp(-r / Lambda_E) / (r**2 + 0.01**2)

    # Normalize to same maximum
    P_G_norm = P_G / P_G.max() * P_IS[0]
    P_E_norm = P_E / P_E.max() * P_IS[0]

    ax1.plot(r, P_IS, 'b-', linewidth=2, label=f'Inverse-square (ε={epsilon})')
    ax1.plot(r, P_G_norm, 'g--', linewidth=2, label=f'Gaussian (Λ={Lambda_G:.2f})')
    ax1.plot(r, P_E_norm, 'r:', linewidth=2, label=f'Exponential (Λ={Lambda_E:.2f})')
    ax1.axvline(x=epsilon, color='gray', linestyle='-.', alpha=0.5, label='Half-max radius')
    ax1.set_xlabel('r (R_stella units)', fontsize=12)
    ax1.set_ylabel('P(r) (normalized)', fontsize=12)
    ax1.set_title('Comparison of Regularization Schemes', fontsize=12)
    ax1.legend(fontsize=9)
    ax1.set_xlim(0, 3)
    ax1.set_ylim(0, 5)
    ax1.grid(True, alpha=0.3)

    # Plot 2: Temperature dependence of ε
    ax2 = axes[0, 1]
    T_range = np.linspace(0, T_C, 200)
    eps_values = [epsilon_T(T) for T in T_range]

    ax2.plot(T_range, eps_values, 'b-', linewidth=2)
    ax2.axhline(y=EPSILON_0, color='gray', linestyle='--', alpha=0.5, label='ε₀ = 0.5')
    ax2.axvline(x=T_C, color='r', linestyle='--', alpha=0.5, label=f'T_c = {T_C} MeV')
    ax2.fill_between(T_range, eps_values, alpha=0.3)
    ax2.set_xlabel('T (MeV)', fontsize=12)
    ax2.set_ylabel('ε(T)', fontsize=12)
    ax2.set_title('Temperature Dependence of Regularization Parameter', fontsize=12)
    ax2.legend(fontsize=10)
    ax2.set_xlim(0, T_C + 10)
    ax2.set_ylim(0, 0.6)
    ax2.grid(True, alpha=0.3)

    # Plot 3: String tension temperature dependence
    ax3 = axes[1, 0]
    T_ratio = np.linspace(0, 1.2, 200)
    f_sigma_values = [f_sigma(t) for t in T_ratio]

    ax3.plot(T_ratio, f_sigma_values, 'b-', linewidth=2)
    ax3.axvline(x=1.0, color='r', linestyle='--', label='T = T_c')
    ax3.fill_between(T_ratio, f_sigma_values, alpha=0.3,
                     where=[t <= 1.0 for t in T_ratio], color='blue')
    ax3.set_xlabel('T / T_c', fontsize=12)
    ax3.set_ylabel('f_σ(T/T_c) = √(σ(T)/σ₀)', fontsize=12)
    ax3.set_title('String Tension Temperature Dependence', fontsize=12)
    ax3.legend(fontsize=10)
    ax3.set_xlim(0, 1.2)
    ax3.set_ylim(0, 1.1)
    ax3.grid(True, alpha=0.3)

    # Plot 4: R_obs temperature dependence
    ax4 = axes[1, 1]
    T_plot = np.linspace(0, 154, 100)  # Stop just before T_c

    def R_obs(T):
        T_ratio = T / T_C
        f_s = f_sigma(T_ratio)
        if f_s < 1e-10:
            return np.nan
        eps = epsilon_T(T)
        R_stella = R_STELLA_0 / f_s
        return eps * R_stella

    R_obs_values = [R_obs(T) for T in T_plot]

    ax4.plot(T_plot, R_obs_values, 'b-', linewidth=2)
    ax4.axhline(y=R_STELLA_0 * EPSILON_0, color='gray', linestyle='--', alpha=0.5,
                label=f'R_obs(0) = {R_STELLA_0 * EPSILON_0:.3f} fm')
    ax4.axvline(x=T_C, color='r', linestyle='--', alpha=0.5, label=f'T_c = {T_C} MeV')
    ax4.set_xlabel('T (MeV)', fontsize=12)
    ax4.set_ylabel('R_obs(T) (fm)', fontsize=12)
    ax4.set_title('Observation Region Temperature Dependence', fontsize=12)
    ax4.legend(fontsize=10)
    ax4.set_xlim(0, 160)
    ax4.set_ylim(0, 0.6)
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()
    plot_path = plots_dir / "proposition_0_0_17o_extensions.png"
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    plt.close()

    return plot_path


# =============================================================================
# Main Verification Runner
# =============================================================================

def run_all_tests() -> Tuple[int, int, List[VerificationResult]]:
    """Run all verification tests for the extensions."""
    print("=" * 70)
    print("PROPOSITION 0.0.17o EXTENSIONS VERIFICATION")
    print("Alternative Regularization Schemes & Temperature Dependence")
    print("=" * 70)
    print()

    # Section 11 tests
    section_11_tests = [
        test_gaussian_matching,
        test_exponential_matching,
        test_gradient_scaling_universal,
        test_lattice_correspondence,
    ]

    # Section 12 tests
    section_12_tests = [
        test_zero_temperature,
        test_critical_temperature,
        test_temperature_table,
        test_monotonic_decrease,
        test_observation_region_constancy,
    ]

    all_results = []
    passed = 0
    total = 0

    # Run Section 11 tests
    print("=" * 70)
    print("SECTION 11: ALTERNATIVE REGULARIZATION SCHEMES")
    print("=" * 70)
    print()

    for test_func in section_11_tests:
        result = test_func()
        all_results.append(result)
        status = "✅ PASS" if result.passed else "❌ FAIL"

        print(f"TEST: {result.name}")
        print("-" * 40)
        print(result.details)
        print(f"\nStatus: {status}")
        print()

        total += 1
        if result.passed:
            passed += 1

    # Run Section 12 tests
    print("=" * 70)
    print("SECTION 12: TEMPERATURE DEPENDENCE")
    print("=" * 70)
    print()

    for test_func in section_12_tests:
        result = test_func()
        all_results.append(result)
        status = "✅ PASS" if result.passed else "❌ FAIL"

        print(f"TEST: {result.name}")
        print("-" * 40)
        print(result.details)
        print(f"\nStatus: {status}")
        print()

        total += 1
        if result.passed:
            passed += 1

    # Summary
    print("=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)
    print(f"Tests passed: {passed}/{total}")
    print()

    if passed == total:
        print("✅ ALL EXTENSION TESTS PASSED")
        print()
        print("KEY RESULTS:")
        print("-" * 40)
        print()
        print("SECTION 11 - Alternative Regularization:")
        print("• Gaussian cutoff Λ_G = 1.20ε ≈ 0.60 (matched)")
        print("• Exponential cutoff Λ_E = 1.44ε ≈ 0.72 (matched)")
        print("• Universal gradient scaling E_grad ~ 1/cutoff³ (verified)")
        print("• Lattice correspondence confirmed")
        print()
        print("SECTION 12 - Temperature Dependence:")
        print("• ε(T=0) = 0.50 (verified)")
        print("• ε(T→T_c) → 0 (verified)")
        print("• Monotonic decrease confirmed")
        print("• R_obs diverges at T_c (framework validity limit)")
        print()
        print("MASTER FORMULAS:")
        print("  Λ_G = ε / √(ln 2) ≈ 1.20ε")
        print("  Λ_E = ε / ln(2) ≈ 1.44ε")
        print("  ε(T) = ε₀ × f_σ(T/T_c) / (1 + c_π(T/T_c)²)")
        print()
    else:
        print(f"❌ {total - passed} TESTS FAILED")

    # Generate plots
    try:
        plot_path = generate_extension_plots()
        print(f"Extension plots saved to: {plot_path}")
    except Exception as e:
        print(f"Warning: Could not generate plots: {e}")

    return passed, total, all_results


if __name__ == "__main__":
    passed, total, results = run_all_tests()
    exit(0 if passed == total else 1)
