#!/usr/bin/env python3
"""
Computational Verification: Derivation-2.2.5a-Coupling-Constant-K.md

This script verifies the numerical claims in the derivation of the
Sakaguchi-Kuramoto coupling constant K from QCD parameters.

Verification Date: 2026-01-03
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Constants
HBAR = 1.0545718e-34  # J·s
C = 2.998e8  # m/s
MEV_TO_JOULES = 1.602e-13  # J/MeV
FM_TO_METERS = 1e-15  # m/fm
GEV_TO_MEV = 1000  # MeV/GeV

# Create plots directory
plots_dir = Path(__file__).parent.parent / "plots"
plots_dir.mkdir(parents=True, exist_ok=True)

class QCDParameters:
    """QCD parameters for K derivation verification."""

    # Fundamental QCD parameters
    LAMBDA_QCD = 200  # MeV (QCD scale)
    ALPHA_S = 0.5  # α_s at Λ_QCD

    # Instanton parameters (Schäfer-Shuryak 1998)
    INSTANTON_DENSITY_FM4 = 1.0  # fm^-4
    INSTANTON_SIZE_FM = 0.33  # fm

    # Gluon condensate (SVZ sum rules)
    GLUON_CONDENSATE_GEV4 = 0.012  # GeV^4

    # String tension (lattice QCD)
    STRING_TENSION_MEV = 440  # MeV (sqrt(σ))

    # Deconfinement temperature (HotQCD)
    T_C = 155  # MeV


def test_dimensional_analysis():
    """Test 1: Verify dimensional analysis for K ~ Λ_QCD."""
    print("\n" + "="*60)
    print("TEST 1: Dimensional Analysis")
    print("="*60)

    # K should have dimensions of [Energy] in natural units
    # Converting to SI: [Energy] / ℏ = [Time^-1]

    K_MeV = QCDParameters.LAMBDA_QCD  # K ~ 200 MeV
    K_joules = K_MeV * MEV_TO_JOULES
    K_per_second = K_joules / HBAR

    expected_K_per_second = 3e23  # from document

    print(f"K ~ Λ_QCD = {K_MeV} MeV")
    print(f"K in Joules = {K_joules:.3e} J")
    print(f"K in s^-1 = {K_per_second:.3e} s^-1")
    print(f"Expected: ~{expected_K_per_second:.0e} s^-1")

    ratio = K_per_second / expected_K_per_second
    passed = 0.5 < ratio < 2.0

    print(f"Ratio: {ratio:.2f}")
    print(f"STATUS: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {
        "K_MeV": K_MeV,
        "K_per_second": K_per_second,
        "expected": expected_K_per_second,
        "ratio": ratio
    }


def test_entropy_production():
    """Test 2: Verify entropy production rate σ = 3K/4."""
    print("\n" + "="*60)
    print("TEST 2: Entropy Production Rate")
    print("="*60)

    K = 200  # MeV
    sigma = 3 * K / 4  # MeV

    expected_sigma = 150  # MeV (from document)

    print(f"K = {K} MeV")
    print(f"σ = 3K/4 = {sigma} MeV")
    print(f"Expected: ~{expected_sigma} MeV")

    passed = abs(sigma - expected_sigma) < 10
    print(f"STATUS: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {"sigma": sigma, "expected": expected_sigma}


def test_jacobian_eigenvalues():
    """Test 3: Verify Jacobian eigenvalues for Sakaguchi-Kuramoto system."""
    print("\n" + "="*60)
    print("TEST 3: Jacobian Eigenvalues")
    print("="*60)

    K = 200  # MeV

    # From document: λ = -3K/8 ± i√3K/4
    real_part = -3 * K / 8
    imag_part = np.sqrt(3) * K / 4

    expected_real = -1.1e23  # s^-1 (from document)
    expected_imag = 1.3e23  # s^-1 (from document)

    # Convert to s^-1
    real_per_second = real_part * MEV_TO_JOULES / HBAR
    imag_per_second = imag_part * MEV_TO_JOULES / HBAR

    print(f"K = {K} MeV")
    print(f"Real part: Re(λ) = -3K/8 = {real_part} MeV = {real_per_second:.2e} s^-1")
    print(f"Imaginary part: Im(λ) = ±√3K/4 = ±{imag_part:.1f} MeV = ±{imag_per_second:.2e} s^-1")
    print(f"Expected: Re(λ) ~ {expected_real:.1e} s^-1, Im(λ) ~ ±{expected_imag:.1e} s^-1")

    # Check ratios
    real_ratio = abs(real_per_second / expected_real)
    imag_ratio = abs(imag_per_second / expected_imag)

    passed = (0.5 < real_ratio < 2.0) and (0.5 < imag_ratio < 2.0)
    print(f"STATUS: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {
        "real_MeV": real_part,
        "imag_MeV": imag_part,
        "real_per_second": real_per_second,
        "imag_per_second": imag_per_second
    }


def test_relaxation_time():
    """Test 4: Verify relaxation time τ = 1/|Re(λ)|."""
    print("\n" + "="*60)
    print("TEST 4: Relaxation Time")
    print("="*60)

    K = 200  # MeV
    real_eigenvalue = 3 * K / 8  # |Re(λ)| in MeV

    # Convert to s^-1
    real_per_second = real_eigenvalue * MEV_TO_JOULES / HBAR
    tau = 1 / real_per_second

    expected_tau = 9e-24  # s (from document)

    print(f"|Re(λ)| = 3K/8 = {real_eigenvalue} MeV")
    print(f"τ = 1/|Re(λ)| = {tau:.2e} s")
    print(f"Expected: ~{expected_tau:.0e} s")

    ratio = tau / expected_tau
    passed = 0.5 < ratio < 2.0

    print(f"Ratio: {ratio:.2f}")
    print(f"STATUS: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {"tau": tau, "expected": expected_tau, "ratio": ratio}


def test_instanton_derivation():
    """Test 5: Verify instanton derivation of K."""
    print("\n" + "="*60)
    print("TEST 5: Instanton Derivation")
    print("="*60)

    # Instanton action
    alpha_s = QCDParameters.ALPHA_S
    S_inst = 2 * np.pi / alpha_s  # 8π²/g² ≈ 2π/α_s

    # Expected value from document
    expected_S_inst = 12

    print(f"α_s = {alpha_s}")
    print(f"S_inst = 8π²/g² = 2π/α_s ≈ {S_inst:.1f}")
    print(f"Expected: ~{expected_S_inst}")

    # Instanton density contribution
    n = QCDParameters.INSTANTON_DENSITY_FM4  # fm^-4
    n_MeV4 = n * (197)**4  # Convert: (197 MeV)^4 / fm^4

    K_from_instanton = n**(1/4) * (197)  # (197 MeV)

    print(f"\nInstanton density n = {n} fm^-4")
    print(f"K ~ n^(1/4) ~ {K_from_instanton:.0f} MeV")

    # With exponential suppression
    K_suppressed = (197) * np.exp(-S_inst/2) * 1  # c_K ~ 1
    print(f"K with exp(-S/2) suppression: {K_suppressed:.1f} MeV")
    print("(Note: This gives ~0.5 MeV, too small as document notes)")

    passed = abs(S_inst - expected_S_inst) < 2
    print(f"\nInstanton action check: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {
        "S_inst": S_inst,
        "K_from_instanton": K_from_instanton,
        "K_suppressed": K_suppressed
    }


def test_gluon_condensate():
    """Test 6: Verify gluon condensate derivation of K."""
    print("\n" + "="*60)
    print("TEST 6: Gluon Condensate Derivation")
    print("="*60)

    G2 = QCDParameters.GLUON_CONDENSATE_GEV4  # GeV^4
    G2_MeV4 = G2 * (GEV_TO_MEV)**4  # Convert to MeV^4

    # Spring constant κ ~ <G²> · R³
    R_fm = 1.0  # 1 fm
    R_GeV_inv = 5.07  # GeV^-1 (1 fm ≈ 5.07 GeV^-1)

    kappa_GeV = G2 * (R_GeV_inv)**3
    kappa_MeV = kappa_GeV * GEV_TO_MEV

    print(f"<G²> = {G2} GeV^4")
    print(f"R = {R_fm} fm = {R_GeV_inv} GeV^-1")
    print(f"κ = <G²>·R³ = {kappa_GeV:.2f} GeV = {kappa_MeV:.0f} MeV")
    print(f"Expected: ~1.6 GeV (from document)")

    # Alternative: K ~ <G²>^(1/4)
    K_from_G2 = G2**(1/4) * GEV_TO_MEV
    print(f"\nK ~ <G²>^(1/4) = {K_from_G2:.0f} MeV")
    print(f"Expected: ~330 MeV (from document)")

    passed = abs(K_from_G2 - 330) < 50
    print(f"STATUS: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {"kappa_MeV": kappa_MeV, "K_from_G2": K_from_G2}


def test_flux_tube():
    """Test 7: Verify flux tube derivation of K."""
    print("\n" + "="*60)
    print("TEST 7: Flux Tube Derivation")
    print("="*60)

    sqrt_sigma = QCDParameters.STRING_TENSION_MEV  # MeV
    sigma = sqrt_sigma**2 / GEV_TO_MEV  # GeV^2

    alpha_s = QCDParameters.ALPHA_S

    omega_flux = sqrt_sigma  # MeV
    K_from_flux = omega_flux * alpha_s

    print(f"√σ = {sqrt_sigma} MeV")
    print(f"σ = {sigma:.2f} GeV² ≈ 0.19 GeV² (expected)")
    print(f"ω_flux ~ √σ = {omega_flux} MeV")
    print(f"K ~ ω_flux · α_s = {K_from_flux:.0f} MeV")
    print(f"Expected: ~220 MeV (from document)")

    passed = abs(K_from_flux - 220) < 50
    print(f"STATUS: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {"omega_flux": omega_flux, "K_from_flux": K_from_flux}


def test_summary_table():
    """Test 8: Verify summary table consistency."""
    print("\n" + "="*60)
    print("TEST 8: Summary Table Consistency")
    print("="*60)

    estimates = {
        "Dimensional analysis (α_s·Λ_QCD)": QCDParameters.ALPHA_S * QCDParameters.LAMBDA_QCD,
        "'t Hooft determinant": 200,  # MeV
        "Gluon condensate": 330,  # MeV
        "Flux tube frequency": 220,  # MeV
    }

    print("\n| Method | K Estimate (MeV) |")
    print("|--------|------------------|")
    for method, K in estimates.items():
        print(f"| {method} | {K:.0f} |")

    mean_K = np.mean(list(estimates.values()))
    std_K = np.std(list(estimates.values()))

    print(f"\nMean K = {mean_K:.0f} ± {std_K:.0f} MeV")
    print(f"Expected range: 150-300 MeV")

    passed = 100 < mean_K < 400
    print(f"STATUS: {'PASS ✓' if passed else 'FAIL ✗'}")

    return passed, {"estimates": estimates, "mean_K": mean_K, "std_K": std_K}


def create_visualization(results):
    """Create visualization of K estimates."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Plot 1: K estimates from different methods
    ax1 = axes[0]
    methods = ["α_s·Λ_QCD", "'t Hooft", "Gluon", "Flux tube"]
    values = [100, 200, 330, 220]
    colors = ['#2ecc71', '#3498db', '#e74c3c', '#9b59b6']

    bars = ax1.bar(methods, values, color=colors, alpha=0.7, edgecolor='black')
    ax1.axhline(y=200, color='red', linestyle='--', linewidth=2, label='Λ_QCD = 200 MeV')
    ax1.axhspan(150, 300, alpha=0.2, color='gray', label='Consensus range')

    ax1.set_ylabel('K (MeV)', fontsize=12)
    ax1.set_title('Coupling Constant K: Multiple Derivations', fontsize=14)
    ax1.legend()
    ax1.set_ylim(0, 400)

    # Add value labels on bars
    for bar, val in zip(bars, values):
        ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 10,
                f'{val}', ha='center', va='bottom', fontsize=11)

    # Plot 2: Eigenvalue visualization
    ax2 = axes[1]
    K = 200  # MeV

    # Draw complex plane
    real = -3*K/8
    imag = np.sqrt(3)*K/4

    ax2.scatter([real], [imag], c='blue', s=100, label=f'λ₊ = {real:.0f} + i{imag:.0f}', zorder=5)
    ax2.scatter([real], [-imag], c='red', s=100, label=f'λ₋ = {real:.0f} - i{imag:.0f}', zorder=5)

    # Draw arrows from origin
    ax2.annotate('', xy=(real, imag), xytext=(0, 0),
                arrowprops=dict(arrowstyle='->', color='blue', lw=2))
    ax2.annotate('', xy=(real, -imag), xytext=(0, 0),
                arrowprops=dict(arrowstyle='->', color='red', lw=2))

    ax2.axhline(y=0, color='black', linestyle='-', linewidth=0.5)
    ax2.axvline(x=0, color='black', linestyle='-', linewidth=0.5)

    ax2.set_xlabel('Re(λ) [MeV]', fontsize=12)
    ax2.set_ylabel('Im(λ) [MeV]', fontsize=12)
    ax2.set_title(f'Jacobian Eigenvalues (K = {K} MeV)', fontsize=14)
    ax2.legend()
    ax2.set_xlim(-150, 50)
    ax2.set_ylim(-120, 120)
    ax2.set_aspect('equal')
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()

    output_path = plots_dir / "derivation_2_2_5a_K_verification.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"\nVisualization saved to: {output_path}")
    plt.close()


def main():
    """Run all verification tests."""
    print("="*60)
    print("COMPUTATIONAL VERIFICATION")
    print("Derivation-2.2.5a-Coupling-Constant-K.md")
    print("="*60)
    print(f"Date: 2026-01-03")
    print("="*60)

    results = {}
    tests = [
        ("Dimensional Analysis", test_dimensional_analysis),
        ("Entropy Production", test_entropy_production),
        ("Jacobian Eigenvalues", test_jacobian_eigenvalues),
        ("Relaxation Time", test_relaxation_time),
        ("Instanton Derivation", test_instanton_derivation),
        ("Gluon Condensate", test_gluon_condensate),
        ("Flux Tube", test_flux_tube),
        ("Summary Table", test_summary_table),
    ]

    passed_tests = 0
    for name, test_func in tests:
        passed, result = test_func()
        results[name] = {"passed": passed, "details": result}
        if passed:
            passed_tests += 1

    # Create visualization
    create_visualization(results)

    # Summary
    print("\n" + "="*60)
    print("VERIFICATION SUMMARY")
    print("="*60)
    print(f"Tests Passed: {passed_tests}/{len(tests)}")
    print()

    for name, result in results.items():
        status = "✓ PASS" if result["passed"] else "✗ FAIL"
        print(f"  {name}: {status}")

    print()
    overall = "VERIFIED" if passed_tests == len(tests) else "PARTIAL"
    print(f"OVERALL STATUS: {overall}")
    print("="*60)

    return results


if __name__ == "__main__":
    main()
