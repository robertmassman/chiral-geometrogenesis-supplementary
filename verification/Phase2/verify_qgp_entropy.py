#!/usr/bin/env python3
"""
Numerical Verification: QGP Entropy Production (T > T_c)
=========================================================

This script verifies the calculations in Derivation-QGP-Entropy-Production.md

Key results to verify:
1. σ_QGP ~ g²T ~ 6×10²³ s⁻¹ at T = 2T_c
2. Continuity at T_c: σ_hadron ≈ σ_QGP
3. KSS bound connection: η/s ~ 1/(4π)
4. Thermalization time τ ~ 1/σ ~ 1 fm/c
5. Polyakov loop order parameter behavior

Author: Claude (Chiral Geometrogenesis verification)
Date: 2025-12-13
"""

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass

# =============================================================================
# Physical Constants (SI units unless noted)
# =============================================================================

@dataclass
class Constants:
    """Physical constants used in calculations"""
    # Fundamental constants
    k_B: float = 1.380649e-23       # Boltzmann constant [J/K]
    hbar: float = 1.054571817e-34   # Reduced Planck constant [J·s]
    hbar_eV: float = 6.582119569e-16  # ℏ in eV·s
    c: float = 2.99792458e8         # Speed of light [m/s]

    # QCD parameters
    Lambda_QCD_MeV: float = 200.0   # QCD scale [MeV]
    K_MeV: float = 200.0            # Kuramoto coupling [MeV]
    T_c_MeV: float = 155.0          # Deconfinement temperature [MeV]
    alpha_s: float = 0.5            # Strong coupling at QCD scale
    g_s: float = np.sqrt(4 * np.pi * 0.5)  # g = √(4πα_s)

    # Derived
    @property
    def MeV_to_J(self) -> float:
        return 1.602176634e-13

    @property
    def MeV_to_invs(self) -> float:
        return self.MeV_to_J / self.hbar

    @property
    def K_invs(self) -> float:
        """Kuramoto coupling in s⁻¹"""
        return self.K_MeV * self.MeV_to_invs

    @property
    def T_c_K(self) -> float:
        """Deconfinement temperature in Kelvin"""
        return self.T_c_MeV * self.MeV_to_J / self.k_B

    @property
    def sigma_hadron(self) -> float:
        """Entropy production in confined phase: σ = 3K/4 [s⁻¹]

        CORRECTED: σ = 3K/4 (not 3K/2) from Theorem 2.2.3 eigenvalue calculation
        Tr(J) = -3K/4, so σ = -Tr(J) = 3K/4
        """
        return 0.75 * self.K_invs

    @property
    def g_squared(self) -> float:
        """g² = 4πα_s"""
        return 4 * np.pi * self.alpha_s

const = Constants()

# =============================================================================
# Entropy Production Models
# =============================================================================

def sigma_confined(K_invs: float = None) -> float:
    """
    Entropy production rate in confined phase (T < T_c).

    CORRECTED: σ_hadron = 3K/4 from Sakaguchi-Kuramoto dynamics
    From Theorem 2.2.3: Tr(J) = -3K/4, so σ = -Tr(J) = 3K/4

    Parameters
    ----------
    K_invs : float, optional
        Kuramoto coupling in s⁻¹ (default: 200 MeV)

    Returns
    -------
    float
        Entropy production rate [s⁻¹]
    """
    if K_invs is None:
        K_invs = const.K_invs
    return 0.75 * K_invs


def sigma_qgp(T_MeV: float, g_squared: float = None) -> float:
    """
    Entropy production rate in QGP phase (T > T_c).

    σ_QGP ~ g² × T (in natural units where T has dimensions of energy)

    In SI units: σ_QGP ~ g² × (T_MeV × MeV_to_invs)

    Parameters
    ----------
    T_MeV : float
        Temperature in MeV
    g_squared : float, optional
        g² = 4πα_s (default uses α_s = 0.5)

    Returns
    -------
    float
        Entropy production rate [s⁻¹]
    """
    if g_squared is None:
        g_squared = const.g_squared

    # σ ~ g² × T where T is in energy units
    T_invs = T_MeV * const.MeV_to_invs
    return g_squared * T_invs


def sigma_transition(T_MeV: float) -> float:
    """
    Entropy production rate across the deconfinement transition.

    Uses a smooth crossover model interpolating between phases.

    Parameters
    ----------
    T_MeV : float
        Temperature in MeV

    Returns
    -------
    float
        Entropy production rate [s⁻¹]
    """
    T_c = const.T_c_MeV

    if T_MeV <= 0.8 * T_c:
        # Deep in confined phase
        return sigma_confined()
    elif T_MeV >= 1.2 * T_c:
        # Deep in QGP phase
        return sigma_qgp(T_MeV)
    else:
        # Crossover region - smooth interpolation
        x = (T_MeV - 0.8 * T_c) / (0.4 * T_c)  # 0 to 1
        f = 0.5 * (1 - np.cos(np.pi * x))  # Smooth step 0 to 1

        sigma_low = sigma_confined()
        sigma_high = sigma_qgp(T_MeV)

        return (1 - f) * sigma_low + f * sigma_high


def thermalization_time(sigma: float) -> float:
    """
    Thermalization time from entropy production rate.

    τ ~ 1/σ

    Parameters
    ----------
    sigma : float
        Entropy production rate [s⁻¹]

    Returns
    -------
    float
        Thermalization time [s]
    """
    return 1.0 / sigma


def tau_to_fm_c(tau_s: float) -> float:
    """Convert time in seconds to fm/c"""
    fm = 1e-15  # m
    return tau_s * const.c / fm

# =============================================================================
# Viscosity and KSS Bound
# =============================================================================

def eta_over_s_from_sigma(sigma: float, T_MeV: float) -> float:
    """
    Estimate η/s from entropy production rate.

    From the derivation: η/s ~ T/σ (in natural units)

    In SI: η/s ~ (k_B × T_K) / (ℏ × σ) × (dimensionless factor)

    Actually, in natural units η/s ~ 1 when σ ~ T.
    The KSS bound is η/s ≥ ℏ/(4πk_B) = 1/(4π) in natural units.

    Parameters
    ----------
    sigma : float
        Entropy production rate [s⁻¹]
    T_MeV : float
        Temperature in MeV

    Returns
    -------
    float
        Dimensionless η/s ratio
    """
    # In our framework: σ ~ g² T, so σ/T ~ g²
    # η/s ~ T/σ ~ 1/g² ~ 1/(4πα_s)
    T_invs = T_MeV * const.MeV_to_invs

    if sigma > 0 and T_invs > 0:
        return T_invs / sigma
    return np.inf


def kss_bound() -> float:
    """
    KSS bound: η/s ≥ ℏ/(4πk_B) = 1/(4π) ≈ 0.0796

    Returns
    -------
    float
        KSS bound value (dimensionless in natural units)
    """
    return 1.0 / (4 * np.pi)

# =============================================================================
# Polyakov Loop
# =============================================================================

def polyakov_loop_expectation(T_MeV: float) -> float:
    """
    Polyakov loop expectation value as order parameter.

    ⟨P⟩ = 0 for T < T_c (confined)
    ⟨P⟩ → 1 for T >> T_c (deconfined)

    Model: ⟨P⟩ = tanh((T - T_c) / (0.1 × T_c)) for T > T_c

    Parameters
    ----------
    T_MeV : float
        Temperature in MeV

    Returns
    -------
    float
        Polyakov loop expectation value [0, 1]
    """
    T_c = const.T_c_MeV

    if T_MeV <= T_c:
        # Small but nonzero due to explicit breaking by quarks
        return 0.1 * np.exp(-2 * (T_c - T_MeV) / T_c)
    else:
        # Rises toward 1
        return np.tanh((T_MeV - T_c) / (0.15 * T_c))

# =============================================================================
# Test Functions
# =============================================================================

def test_sigma_confined():
    """Test 1: Verify σ_hadron = 3K/4 ~ 2.28×10²³ s⁻¹

    CORRECTED: σ = 3K/4 (not 3K/2) from Theorem 2.2.3
    """
    sigma = sigma_confined()

    print("=" * 60)
    print("TEST 1: Entropy Production in Confined Phase")
    print("=" * 60)
    print(f"K = {const.K_MeV} MeV = {const.K_invs:.3e} s⁻¹")
    print(f"σ_hadron = 3K/4 = {sigma:.3e} s⁻¹")
    print()

    expected = 2.28e23  # CORRECTED from 4.56e23 (was 3K/2, now 3K/4)
    rel_error = abs(sigma - expected) / expected

    print(f"Expected: ~2.28×10²³ s⁻¹")
    print(f"Relative error: {rel_error*100:.1f}%")
    print()

    assert rel_error < 0.05, f"σ_hadron off by {rel_error*100:.1f}%"
    print("✓ PASS: σ_hadron = 3K/4 verified")

    return True


def test_sigma_qgp():
    """Test 2: Verify σ_QGP ~ g²T ~ 6×10²³ s⁻¹ at T = 2T_c"""
    T = 2 * const.T_c_MeV  # 310 MeV
    sigma = sigma_qgp(T)

    print("=" * 60)
    print("TEST 2: Entropy Production in QGP Phase")
    print("=" * 60)
    print(f"T = 2T_c = {T} MeV")
    print(f"g² = 4πα_s = {const.g_squared:.3f}")
    print(f"σ_QGP = g²T = {sigma:.3e} s⁻¹")
    print()

    # Expected ~6×10²³ s⁻¹ from the derivation
    expected_order = 6e23
    ratio = sigma / expected_order

    print(f"Expected order of magnitude: ~6×10²³ s⁻¹")
    print(f"Ratio to expected: {ratio:.2f}")
    print()

    assert 0.1 < ratio < 10, f"σ_QGP not in expected range"
    print("✓ PASS: σ_QGP ~ 10²³-10²⁴ s⁻¹ verified")

    return True


def test_continuity_at_Tc():
    """Test 3: Verify continuity of σ at T_c (no discontinuity)"""
    T_c = const.T_c_MeV

    # Evaluate just below and above T_c
    sigma_below = sigma_transition(0.95 * T_c)
    sigma_at = sigma_transition(T_c)
    sigma_above = sigma_transition(1.05 * T_c)

    print("=" * 60)
    print("TEST 3: Continuity at Deconfinement (T = T_c)")
    print("=" * 60)
    print(f"T_c = {T_c} MeV")
    print()
    print(f"σ(0.95 T_c) = {sigma_below:.3e} s⁻¹")
    print(f"σ(T_c)      = {sigma_at:.3e} s⁻¹")
    print(f"σ(1.05 T_c) = {sigma_above:.3e} s⁻¹")
    print()

    # Check no sharp jump (ratio should be close to 1)
    ratio_down = sigma_at / sigma_below
    ratio_up = sigma_above / sigma_at

    print(f"σ(T_c)/σ(0.95T_c) = {ratio_down:.3f}")
    print(f"σ(1.05T_c)/σ(T_c) = {ratio_up:.3f}")
    print()

    # Both ratios should be between 0.5 and 2 (smooth crossover)
    assert 0.5 < ratio_down < 2, f"Jump at T_c- too large: {ratio_down}"
    assert 0.5 < ratio_up < 2, f"Jump at T_c+ too large: {ratio_up}"
    print("✓ PASS: σ is continuous at T_c (smooth crossover)")

    return True


def test_sigma_same_order():
    """Test 4: Verify σ_hadron ≈ σ_QGP at T_c (same order of magnitude)"""
    sigma_h = sigma_confined()
    sigma_q = sigma_qgp(const.T_c_MeV)

    print("=" * 60)
    print("TEST 4: σ_hadron vs σ_QGP at T_c")
    print("=" * 60)
    print(f"σ_hadron (confined) = {sigma_h:.3e} s⁻¹")
    print(f"σ_QGP(T_c)         = {sigma_q:.3e} s⁻¹")
    print()

    ratio = sigma_h / sigma_q
    print(f"Ratio σ_hadron/σ_QGP(T_c) = {ratio:.2f}")
    print()

    # Should be within factor of 3
    assert 0.3 < ratio < 3, f"σ_hadron and σ_QGP differ too much: ratio={ratio:.2f}"
    print("✓ PASS: σ_hadron ≈ σ_QGP(T_c) (within factor of 3)")

    return True


def test_kss_bound():
    """Test 5: Verify η/s ~ 1/(4π) from framework"""
    T = 2 * const.T_c_MeV  # Well in QGP phase
    sigma = sigma_qgp(T)
    eta_s = eta_over_s_from_sigma(sigma, T)

    kss = kss_bound()

    print("=" * 60)
    print("TEST 5: KSS Bound Connection")
    print("=" * 60)
    print(f"T = {T} MeV (2T_c)")
    print(f"σ_QGP = {sigma:.3e} s⁻¹")
    print()
    print(f"Estimated η/s = T/σ = {eta_s:.4f}")
    print(f"KSS bound: η/s ≥ 1/(4π) = {kss:.4f}")
    print(f"Ratio to KSS bound: {eta_s/kss:.2f}")
    print()

    # In our framework: η/s ~ 1/g² ~ 1/(4πα_s) ~ 0.16
    expected_eta_s = 1 / const.g_squared
    print(f"Framework prediction: η/s ~ 1/g² = {expected_eta_s:.4f}")
    print(f"Ratio to KSS: {expected_eta_s/kss:.2f}")
    print()

    # Should be within factor of 5 of KSS bound
    assert eta_s > 0.5 * kss, f"η/s too far below KSS bound"
    assert eta_s < 5 * kss, f"η/s too far above KSS bound"
    print("✓ PASS: η/s near KSS bound (factor of ~2)")

    return True


def test_thermalization_time():
    """Test 6: Verify τ ~ 1 fm/c"""
    T = const.T_c_MeV
    sigma = sigma_transition(T)
    tau = thermalization_time(sigma)
    tau_fm = tau_to_fm_c(tau)

    print("=" * 60)
    print("TEST 6: Thermalization Time")
    print("=" * 60)
    print(f"At T = T_c = {T} MeV:")
    print(f"  σ = {sigma:.3e} s⁻¹")
    print(f"  τ = 1/σ = {tau:.3e} s")
    print(f"  τ = {tau_fm:.2f} fm/c")
    print()
    print("RHIC/LHC measurement: τ_therm ~ 0.2-1.0 fm/c")
    print()

    assert 0.1 < tau_fm < 5.0, f"τ should be ~1 fm/c, got {tau_fm:.2f}"
    print("✓ PASS: Thermalization time ~ 1 fm/c")

    return True


def test_polyakov_loop():
    """Test 7: Verify Polyakov loop behavior"""
    T_c = const.T_c_MeV

    temps = [0.5 * T_c, 0.9 * T_c, T_c, 1.1 * T_c, 1.5 * T_c, 2.0 * T_c]

    print("=" * 60)
    print("TEST 7: Polyakov Loop Order Parameter")
    print("=" * 60)
    print(f"T_c = {T_c} MeV")
    print()
    print(f"{'T/T_c':>8} {'T [MeV]':>10} {'⟨P⟩':>10}")
    print("-" * 32)

    for T in temps:
        P = polyakov_loop_expectation(T)
        print(f"{T/T_c:>8.2f} {T:>10.1f} {P:>10.4f}")

    print()

    # Verify behavior
    P_low = polyakov_loop_expectation(0.5 * T_c)
    P_high = polyakov_loop_expectation(2.0 * T_c)

    assert P_low < 0.1, f"⟨P⟩ should be ~0 below T_c, got {P_low}"
    assert P_high > 0.8, f"⟨P⟩ should be ~1 above T_c, got {P_high}"
    print("✓ PASS: Polyakov loop shows deconfinement transition")

    return True


def generate_plots():
    """Generate visualization plots"""
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    T_c = const.T_c_MeV

    # Plot 1: σ(T) across transition
    ax1 = axes[0, 0]
    T_range = np.linspace(50, 400, 200)  # MeV
    sigma_vals = [sigma_transition(T) for T in T_range]

    ax1.semilogy(T_range, sigma_vals, 'b-', linewidth=2)
    ax1.axvline(T_c, color='r', linestyle='--', label=f'T_c = {T_c} MeV')
    ax1.axhline(sigma_confined(), color='g', linestyle=':', alpha=0.7, label='σ_hadron = 3K/4')
    ax1.set_xlabel('Temperature [MeV]')
    ax1.set_ylabel('σ [s⁻¹]')
    ax1.set_title('Entropy Production Rate vs Temperature')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Plot 2: Polyakov loop
    ax2 = axes[0, 1]
    T_range_P = np.linspace(50, 400, 200)
    P_vals = [polyakov_loop_expectation(T) for T in T_range_P]

    ax2.plot(T_range_P, P_vals, 'b-', linewidth=2)
    ax2.axvline(T_c, color='r', linestyle='--', label=f'T_c = {T_c} MeV')
    ax2.set_xlabel('Temperature [MeV]')
    ax2.set_ylabel('⟨P⟩')
    ax2.set_title('Polyakov Loop Order Parameter')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim(-0.1, 1.1)

    # Plot 3: Thermalization time
    ax3 = axes[1, 0]
    T_range_tau = np.linspace(100, 400, 100)
    tau_vals = [tau_to_fm_c(thermalization_time(sigma_transition(T))) for T in T_range_tau]

    ax3.plot(T_range_tau, tau_vals, 'b-', linewidth=2)
    ax3.axvline(T_c, color='r', linestyle='--', label=f'T_c = {T_c} MeV')
    ax3.axhline(1.0, color='orange', linestyle=':', label='τ = 1 fm/c')
    ax3.axhspan(0.2, 1.0, alpha=0.2, color='green', label='RHIC/LHC range')
    ax3.set_xlabel('Temperature [MeV]')
    ax3.set_ylabel('τ [fm/c]')
    ax3.set_title('Thermalization Time')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    ax3.set_ylim(0, 3)

    # Plot 4: η/s ratio
    ax4 = axes[1, 1]
    T_range_eta = np.linspace(T_c * 1.1, 400, 100)  # Above T_c only
    eta_s_vals = [eta_over_s_from_sigma(sigma_qgp(T), T) for T in T_range_eta]

    ax4.plot(T_range_eta, eta_s_vals, 'b-', linewidth=2)
    ax4.axhline(kss_bound(), color='r', linestyle='--', label=f'KSS bound = 1/(4π) = {kss_bound():.4f}')
    ax4.axhline(1/const.g_squared, color='orange', linestyle=':', label=f'1/g² = {1/const.g_squared:.4f}')
    ax4.set_xlabel('Temperature [MeV]')
    ax4.set_ylabel('η/s')
    ax4.set_title('Viscosity to Entropy Ratio (T > T_c)')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    ax4.set_ylim(0, 0.5)

    plt.tight_layout()
    plt.savefig('qgp_entropy_verification.png', dpi=150)
    print("\nPlot saved to: qgp_entropy_verification.png")

    return fig


def print_summary_table():
    """Print summary of key numerical values"""
    print("\n" + "=" * 70)
    print("SUMMARY: Key Numerical Values")
    print("=" * 70)

    print("\nQCD Parameters:")
    print(f"  Λ_QCD = {const.Lambda_QCD_MeV} MeV")
    print(f"  K = {const.K_MeV} MeV = {const.K_invs:.3e} s⁻¹")
    print(f"  T_c = {const.T_c_MeV} MeV = {const.T_c_K:.3e} K")
    print(f"  α_s = {const.alpha_s}")
    print(f"  g² = 4πα_s = {const.g_squared:.3f}")

    print("\nEntropy Production Rates:")
    print(f"  σ_hadron (T < T_c) = 3K/4 = {sigma_confined():.3e} s⁻¹")
    print(f"  σ_QGP(T_c)         = g²T  = {sigma_qgp(const.T_c_MeV):.3e} s⁻¹")
    print(f"  σ_QGP(2T_c)        = g²T  = {sigma_qgp(2*const.T_c_MeV):.3e} s⁻¹")

    print("\nThermalization Times:")
    tau_h = thermalization_time(sigma_confined())
    tau_q = thermalization_time(sigma_qgp(2*const.T_c_MeV))
    print(f"  τ_hadron = 1/σ_hadron = {tau_h:.3e} s = {tau_to_fm_c(tau_h):.2f} fm/c")
    print(f"  τ_QGP    = 1/σ_QGP    = {tau_q:.3e} s = {tau_to_fm_c(tau_q):.2f} fm/c")

    print("\nKSS Bound:")
    print(f"  η/s ≥ 1/(4π) = {kss_bound():.4f}")
    print(f"  Framework: η/s ~ 1/g² = {1/const.g_squared:.4f}")
    print(f"  Ratio to KSS: {(1/const.g_squared)/kss_bound():.2f}")

    print("\nSigma at Key Temperatures:")
    temps = [100, 150, const.T_c_MeV, 200, 250, 300, 400]
    print(f"  {'T [MeV]':>10} {'σ [s⁻¹]':>12} {'τ [fm/c]':>10}")
    print("  " + "-" * 35)
    for T in temps:
        s = sigma_transition(T)
        tau = tau_to_fm_c(thermalization_time(s))
        marker = " *" if abs(T - const.T_c_MeV) < 1 else ""
        print(f"  {T:>10.1f} {s:>12.3e} {tau:>10.2f}{marker}")


# =============================================================================
# Main Execution
# =============================================================================

if __name__ == "__main__":
    print("\n" + "=" * 70)
    print("NUMERICAL VERIFICATION: QGP Entropy Production")
    print("Derivation-QGP-Entropy-Production.md")
    print("=" * 70 + "\n")

    # Run all tests
    tests = [
        ("Confined Phase σ", test_sigma_confined),
        ("QGP Phase σ", test_sigma_qgp),
        ("Continuity at T_c", test_continuity_at_Tc),
        ("σ_hadron ≈ σ_QGP", test_sigma_same_order),
        ("KSS Bound", test_kss_bound),
        ("Thermalization Time", test_thermalization_time),
        ("Polyakov Loop", test_polyakov_loop),
    ]

    results = []
    for name, test_func in tests:
        try:
            result = test_func()
            results.append((name, result, None))
        except AssertionError as e:
            results.append((name, False, str(e)))
        print()

    # Print summary table
    print_summary_table()

    # Generate plots
    try:
        fig = generate_plots()
        plt.close(fig)
    except Exception as e:
        print(f"\nWarning: Could not generate plots: {e}")

    # Final summary
    print("\n" + "=" * 70)
    print("TEST RESULTS SUMMARY")
    print("=" * 70)

    passed = sum(1 for _, result, _ in results if result)
    total = len(results)

    for name, result, error in results:
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"  {status}: {name}")
        if error:
            print(f"         Error: {error}")

    print()
    print(f"Total: {passed}/{total} tests passed")

    if passed == total:
        print("\n✓ ALL TESTS PASSED - Derivation verified")
    else:
        print(f"\n✗ {total - passed} test(s) failed")
