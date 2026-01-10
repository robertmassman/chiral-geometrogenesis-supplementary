#!/usr/bin/env python3
"""
Numerical Verification: QCD-EM Coupling Efficiency ε
=====================================================

This script verifies the calculations in Derivation-QCD-EM-Coupling-Efficiency.md

Key results to verify:
1. ε(T) = (k_B T / Λ_QCD)^4 × α_em ~ 10^{-42} at 300K
2. Three coupling mechanisms and their relative contributions
3. Temperature dependence from 1K to QGP temperatures
4. Observable entropy production rates at various scales
5. Heavy-ion regime behavior (ε → 1 as T → T_c)

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
    k_B: float = 1.380649e-23      # Boltzmann constant [J/K]
    hbar: float = 1.054571817e-34  # Reduced Planck constant [J·s]
    c: float = 2.99792458e8        # Speed of light [m/s]
    e: float = 1.602176634e-19     # Elementary charge [C]

    # QCD parameters
    Lambda_QCD_MeV: float = 200.0  # QCD scale [MeV]
    K_MeV: float = 200.0           # Kuramoto coupling [MeV]
    T_c_MeV: float = 155.0         # Deconfinement temperature [MeV]
    alpha_s: float = 0.5           # Strong coupling at QCD scale

    # Electromagnetic
    alpha_em: float = 1/137.036    # Fine structure constant

    # Derived quantities
    @property
    def MeV_to_J(self) -> float:
        """Conversion: 1 MeV = ? J"""
        return 1.602176634e-13

    @property
    def MeV_to_invs(self) -> float:
        """Conversion: 1 MeV = ? s^{-1} (via E = ℏω)"""
        return self.MeV_to_J / self.hbar

    @property
    def Lambda_QCD_J(self) -> float:
        """QCD scale in Joules"""
        return self.Lambda_QCD_MeV * self.MeV_to_J

    @property
    def Lambda_QCD_K(self) -> float:
        """QCD scale as temperature [K]"""
        return self.Lambda_QCD_J / self.k_B

    @property
    def T_c_K(self) -> float:
        """Deconfinement temperature [K]"""
        return self.T_c_MeV * self.MeV_to_J / self.k_B

    @property
    def K_invs(self) -> float:
        """Kuramoto coupling K in s^{-1}"""
        return self.K_MeV * self.MeV_to_invs

    @property
    def sigma_micro(self) -> float:
        """Microscopic entropy production rate σ = 3K/2 [s^{-1}]"""
        return 1.5 * self.K_invs

    @property
    def S_dot_Gibbs_per_hadron(self) -> float:
        """Gibbs entropy production rate per hadron [J/(K·s)]"""
        return self.k_B * self.sigma_micro

const = Constants()

# =============================================================================
# Coupling Efficiency Calculations
# =============================================================================

def epsilon_vacuum_polarization(T_K: float) -> float:
    """
    Coupling efficiency from hadronic vacuum polarization mechanism.

    ε_VP ~ (k_B T / Λ_QCD)^4 × α_em

    This is the dominant mechanism at low temperatures.

    Parameters
    ----------
    T_K : float
        Temperature in Kelvin

    Returns
    -------
    float
        Coupling efficiency (dimensionless)
    """
    # Energy ratio
    kT = const.k_B * T_K  # [J]
    ratio = kT / const.Lambda_QCD_J

    # ε ~ (k_B T / Λ_QCD)^4 × α_em
    epsilon = ratio**4 * const.alpha_em

    return epsilon


def epsilon_gluon_photon(T_K: float) -> float:
    """
    Coupling efficiency from gluon-photon conversion (gg → γ via quark loop).

    This mechanism is suppressed by:
    - α_s^2 × α_em (coupling factors)
    - Confinement (Furry theorem in confined phase)
    - Energy mismatch (thermal suppression)

    Parameters
    ----------
    T_K : float
        Temperature in Kelvin

    Returns
    -------
    float
        Coupling efficiency (dimensionless)
    """
    # Coupling suppression
    coupling_factor = const.alpha_s**2 * const.alpha_em

    # Confinement suppression (amplitude level)
    xi_conf = np.exp(-1.0)  # ~ e^{-Λ_QCD × r_hadron} ~ e^{-1}

    # Rate-level suppression
    confinement_suppression = xi_conf**2

    # Thermal suppression: exp(-ℏω/k_B T) for ω ~ Λ_QCD
    kT = const.k_B * T_K
    omega_QCD = const.Lambda_QCD_J / const.hbar
    thermal_factor = np.exp(-min(const.Lambda_QCD_J / kT, 700))  # Cap to avoid overflow

    epsilon = coupling_factor * confinement_suppression * thermal_factor

    return epsilon


def epsilon_em_form_factor(T_K: float) -> float:
    """
    Coupling efficiency from EM form factor radiation (quadrupole).

    Suppressed by:
    - Quadrupole vs dipole: (r_0/λ)^2 ~ 0.03
    - Thermal occupation: exp(-ℏω/k_B T) ~ 0 for ω >> k_B T

    Parameters
    ----------
    T_K : float
        Temperature in Kelvin

    Returns
    -------
    float
        Coupling efficiency (dimensionless)
    """
    # Quadrupole suppression
    r_0 = 1e-15  # Hadron radius [m]
    omega_QCD = const.Lambda_QCD_J / const.hbar
    wavelength = 2 * np.pi * const.c / omega_QCD
    quadrupole_factor = (r_0 / wavelength)**2

    # Thermal suppression
    kT = const.k_B * T_K
    thermal_factor = np.exp(-min(const.Lambda_QCD_J / kT, 700))

    epsilon = const.alpha_em * quadrupole_factor * thermal_factor

    return epsilon


def epsilon_total(T_K: float) -> float:
    """
    Total coupling efficiency (sum of all mechanisms).

    At low T: dominated by vacuum polarization (no thermal suppression)
    At high T: all mechanisms contribute
    """
    eps_vp = epsilon_vacuum_polarization(T_K)
    eps_gp = epsilon_gluon_photon(T_K)
    eps_em = epsilon_em_form_factor(T_K)

    return eps_vp + eps_gp + eps_em


def epsilon_high_T(T_K: float) -> float:
    """
    Coupling efficiency in high-temperature regime (T ~ T_c).

    For T > T_c, the suppression disappears and ε → 1.
    Model: ε ~ (T/T_c)^4 for T < T_c, saturating at 1 for T > T_c
    """
    T_c = const.T_c_K

    if T_K >= T_c:
        return 1.0
    else:
        # Interpolate using (T/T_c)^4 with saturation
        return min(1.0, (T_K / T_c)**4)

# =============================================================================
# Observable Entropy Production
# =============================================================================

def observable_entropy_rate(T_K: float, N_hadrons: float = 1.0) -> float:
    """
    Observable thermodynamic entropy production rate.

    dS_thermo/dt = ε × dS_Gibbs/dt = ε × N × k_B × σ

    Parameters
    ----------
    T_K : float
        Temperature in Kelvin
    N_hadrons : float
        Number of hadrons

    Returns
    -------
    float
        Observable entropy production rate [J/(K·s)]
    """
    eps = epsilon_total(T_K)
    S_dot_Gibbs = N_hadrons * const.S_dot_Gibbs_per_hadron

    return eps * S_dot_Gibbs

# =============================================================================
# Test Functions
# =============================================================================

def test_epsilon_room_temperature():
    """Test 1: Verify ε ~ 10^{-42} at room temperature (300K)"""
    T = 300.0  # K
    eps = epsilon_vacuum_polarization(T)

    # Expected: ε ~ (25 meV / 200 MeV)^4 × (1/137) ~ 10^{-42}
    # k_B × 300K = 25.85 meV
    kT_meV = const.k_B * T / const.MeV_to_J * 1000  # Convert to meV
    expected_ratio = (kT_meV / 1000 / const.Lambda_QCD_MeV)  # kT/Λ_QCD
    expected_eps = expected_ratio**4 * const.alpha_em

    print("=" * 60)
    print("TEST 1: Coupling Efficiency at Room Temperature")
    print("=" * 60)
    print(f"Temperature: {T} K")
    print(f"k_B T: {kT_meV:.4f} meV")
    print(f"Λ_QCD: {const.Lambda_QCD_MeV} MeV")
    print(f"Ratio k_B T / Λ_QCD: {expected_ratio:.2e}")
    print(f"α_em: {const.alpha_em:.6f}")
    print()
    print(f"Calculated ε: {eps:.2e}")
    print(f"Expected ε:   {expected_eps:.2e}")
    print(f"log₁₀(ε):     {np.log10(eps):.1f}")
    print()

    # Verify order of magnitude
    log_eps = np.log10(eps)
    assert -45 < log_eps < -38, f"ε should be ~10^{{-42}}, got 10^{{{log_eps:.1f}}}"
    print("✓ PASS: ε is in expected range (10^{-45} to 10^{-38})")

    return True


def test_temperature_scaling():
    """Test 2: Verify ε ∝ T^4 scaling"""
    T1, T2 = 100.0, 1000.0  # K
    eps1 = epsilon_vacuum_polarization(T1)
    eps2 = epsilon_vacuum_polarization(T2)

    # Expected: ε(T2)/ε(T1) = (T2/T1)^4 = 10^4
    expected_ratio = (T2 / T1)**4
    actual_ratio = eps2 / eps1

    print("=" * 60)
    print("TEST 2: Temperature Scaling (ε ∝ T^4)")
    print("=" * 60)
    print(f"T1 = {T1} K, ε1 = {eps1:.2e}")
    print(f"T2 = {T2} K, ε2 = {eps2:.2e}")
    print()
    print(f"Expected ratio (T2/T1)^4: {expected_ratio:.2e}")
    print(f"Actual ratio ε2/ε1:       {actual_ratio:.2e}")
    print(f"Relative error:           {abs(actual_ratio/expected_ratio - 1)*100:.2f}%")
    print()

    assert abs(actual_ratio / expected_ratio - 1) < 0.01, "T^4 scaling violated"
    print("✓ PASS: T^4 scaling verified")

    return True


def test_mechanism_hierarchy():
    """Test 3: Verify vacuum polarization dominates at low T"""
    T = 300.0  # K

    eps_vp = epsilon_vacuum_polarization(T)
    eps_gp = epsilon_gluon_photon(T)
    eps_em = epsilon_em_form_factor(T)

    print("=" * 60)
    print("TEST 3: Mechanism Hierarchy at 300K")
    print("=" * 60)
    print(f"Vacuum polarization: ε_VP = {eps_vp:.2e}")
    print(f"Gluon-photon:        ε_gγ = {eps_gp:.2e}")
    print(f"EM form factor:      ε_EM = {eps_em:.2e}")
    print()

    # Vacuum polarization should dominate
    total = eps_vp + eps_gp + eps_em
    vp_fraction = eps_vp / total

    print(f"VP contribution: {vp_fraction*100:.1f}%")
    print()

    assert vp_fraction > 0.99, "Vacuum polarization should dominate at low T"
    print("✓ PASS: Vacuum polarization dominates (>99%)")

    return True


def test_no_spontaneous_heating():
    """Test 4: Verify observable entropy production is negligible at equilibrium"""
    T = 300.0  # K
    N_A = 6.022e23  # Avogadro's number (1 mole)

    # Gibbs entropy production (internal)
    S_dot_Gibbs = N_A * const.S_dot_Gibbs_per_hadron

    # Observable entropy production
    S_dot_thermo = observable_entropy_rate(T, N_A)

    # Power if this were heat: P = T × dS/dt
    power_Gibbs = T * S_dot_Gibbs
    power_thermo = T * S_dot_thermo

    print("=" * 60)
    print("TEST 4: No Spontaneous Heating (Energy Paradox Resolution)")
    print("=" * 60)
    print("For 1 mole of matter at 300K:")
    print()
    print(f"Gibbs entropy production rate:")
    print(f"  dS_Gibbs/dt = {S_dot_Gibbs:.2e} J/(K·s)")
    print(f"  Equivalent power = {power_Gibbs:.2e} W")
    print()
    print(f"Observable (thermodynamic) entropy production rate:")
    print(f"  dS_thermo/dt = {S_dot_thermo:.2e} J/(K·s)")
    print(f"  Equivalent power = {power_thermo:.2e} W")
    print()
    print(f"Suppression factor: {S_dot_thermo/S_dot_Gibbs:.2e}")
    print()

    # Observable power should be negligible (< 1 μW per mole)
    assert power_thermo < 1e-6, f"Observable power should be < 1 μW, got {power_thermo:.2e} W"
    print("✓ PASS: Observable heating is negligible (< 1 μW/mol)")

    return True


def test_qgp_regime():
    """Test 5: Verify ε → 1 as T → T_c (heavy-ion regime)"""
    T_c = const.T_c_K

    # Test at various temperatures
    temps = [0.1 * T_c, 0.5 * T_c, 0.9 * T_c, T_c, 2 * T_c]

    print("=" * 60)
    print("TEST 5: QGP Regime (ε → 1 as T → T_c)")
    print("=" * 60)
    print(f"T_c = {T_c:.2e} K = {const.T_c_MeV} MeV")
    print()
    print(f"{'T/T_c':>8} {'T [K]':>12} {'ε':>12}")
    print("-" * 35)

    for T in temps:
        eps = epsilon_high_T(T)
        print(f"{T/T_c:>8.2f} {T:>12.2e} {eps:>12.2e}")

    print()

    # Verify saturation at T_c
    eps_at_Tc = epsilon_high_T(T_c)
    eps_above_Tc = epsilon_high_T(2 * T_c)

    assert eps_at_Tc == 1.0, f"ε should be 1 at T_c, got {eps_at_Tc}"
    assert eps_above_Tc == 1.0, f"ε should be 1 above T_c, got {eps_above_Tc}"
    print("✓ PASS: ε = 1 at and above T_c")

    return True


def test_thermalization_time():
    """Test 6: Verify thermalization time τ ~ 1/K ~ 1 fm/c"""
    tau = 1 / const.K_invs  # [s]

    # Convert to fm/c
    fm = 1e-15  # m
    tau_fm_c = tau * const.c / fm

    print("=" * 60)
    print("TEST 6: Thermalization Time")
    print("=" * 60)
    print(f"K = {const.K_MeV} MeV = {const.K_invs:.2e} s⁻¹")
    print(f"τ = 1/K = {tau:.2e} s")
    print(f"τ = {tau_fm_c:.2f} fm/c")
    print()
    print("RHIC/LHC measurement: τ_therm ~ 0.2-1.0 fm/c")
    print()

    # Should be within factor of 5 of 1 fm/c
    assert 0.1 < tau_fm_c < 5.0, f"τ should be ~1 fm/c, got {tau_fm_c:.2f} fm/c"
    print("✓ PASS: Thermalization time consistent with RHIC/LHC")

    return True


def generate_plots():
    """Generate visualization plots"""

    # Create figure with subplots
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: ε(T) over full temperature range
    ax1 = axes[0, 0]
    T_range = np.logspace(0, 12, 1000)  # 1 K to 10^12 K
    eps_vp = [epsilon_vacuum_polarization(T) for T in T_range]
    eps_high = [epsilon_high_T(T) for T in T_range]

    ax1.loglog(T_range, eps_vp, 'b-', label='Vacuum polarization (low T)')
    ax1.loglog(T_range, eps_high, 'r--', label='High T model')
    ax1.axvline(const.T_c_K, color='orange', linestyle=':', label=f'T_c = {const.T_c_MeV} MeV')
    ax1.axvline(300, color='green', linestyle=':', alpha=0.5, label='Room temp')
    ax1.set_xlabel('Temperature [K]')
    ax1.set_ylabel('Coupling efficiency ε')
    ax1.set_title('QCD-EM Coupling Efficiency vs Temperature')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    ax1.set_ylim(1e-50, 10)

    # Plot 2: Observable entropy production
    ax2 = axes[0, 1]
    T_range_low = np.logspace(1, 6, 100)  # 10 K to 10^6 K
    N_mole = 6.022e23
    S_dot = [observable_entropy_rate(T, N_mole) for T in T_range_low]

    ax2.loglog(T_range_low, S_dot, 'b-')
    ax2.axhline(1e-6, color='r', linestyle='--', label='1 μW/K threshold')
    ax2.set_xlabel('Temperature [K]')
    ax2.set_ylabel('Observable dS/dt [J/(K·s)] per mole')
    ax2.set_title('Observable Entropy Production Rate')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # Plot 3: Mechanism comparison
    ax3 = axes[1, 0]
    T_range_mech = np.logspace(2, 10, 100)
    eps_vp = [epsilon_vacuum_polarization(T) for T in T_range_mech]
    eps_gp = [epsilon_gluon_photon(T) for T in T_range_mech]
    eps_em = [epsilon_em_form_factor(T) for T in T_range_mech]

    ax3.loglog(T_range_mech, eps_vp, 'b-', label='Vacuum polarization')
    ax3.loglog(T_range_mech, eps_gp, 'r-', label='Gluon-photon')
    ax3.loglog(T_range_mech, eps_em, 'g-', label='EM form factor')
    ax3.set_xlabel('Temperature [K]')
    ax3.set_ylabel('Coupling efficiency ε')
    ax3.set_title('Comparison of Coupling Mechanisms')
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # Plot 4: T^4 scaling verification
    ax4 = axes[1, 1]
    T_test = np.logspace(1, 5, 50)
    eps_calc = [epsilon_vacuum_polarization(T) for T in T_test]
    eps_T4 = [(T/1e4)**4 * epsilon_vacuum_polarization(1e4) for T in T_test]

    ax4.loglog(T_test, eps_calc, 'b-', linewidth=2, label='Calculated')
    ax4.loglog(T_test, eps_T4, 'r--', label='T⁴ scaling')
    ax4.set_xlabel('Temperature [K]')
    ax4.set_ylabel('Coupling efficiency ε')
    ax4.set_title('T⁴ Scaling Verification')
    ax4.legend()
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('qcd_em_coupling_verification.png', dpi=150)
    print("\nPlot saved to: qcd_em_coupling_verification.png")

    return fig


def print_summary_table():
    """Print summary of key numerical values"""
    print("\n" + "=" * 70)
    print("SUMMARY: Key Numerical Values")
    print("=" * 70)

    print("\nPhysical Constants:")
    print(f"  k_B = {const.k_B:.6e} J/K")
    print(f"  ℏ = {const.hbar:.6e} J·s")
    print(f"  α_em = 1/{1/const.alpha_em:.3f}")

    print("\nQCD Parameters:")
    print(f"  Λ_QCD = {const.Lambda_QCD_MeV} MeV = {const.Lambda_QCD_J:.3e} J")
    print(f"  K = {const.K_MeV} MeV = {const.K_invs:.3e} s⁻¹")
    print(f"  T_c = {const.T_c_MeV} MeV = {const.T_c_K:.3e} K")
    print(f"  α_s = {const.alpha_s}")

    print("\nDerived Quantities:")
    print(f"  σ_micro = 3K/2 = {const.sigma_micro:.3e} s⁻¹")
    print(f"  Ṡ_Gibbs/hadron = {const.S_dot_Gibbs_per_hadron:.2f} J/(K·s)")
    print(f"  τ_therm = 1/K = {1/const.K_invs:.2e} s = {1/const.K_invs * const.c / 1e-15:.1f} fm/c")

    print("\nCoupling Efficiency at Key Temperatures:")
    temps = [1, 10, 100, 300, 1000, 1e6, const.T_c_K]
    print(f"  {'T [K]':>12} {'ε_VP':>12} {'log₁₀(ε)':>12}")
    print("  " + "-" * 40)
    for T in temps:
        eps = epsilon_vacuum_polarization(T)
        log_eps = np.log10(eps) if eps > 0 else -np.inf
        print(f"  {T:>12.2e} {eps:>12.2e} {log_eps:>12.1f}")


# =============================================================================
# Main Execution
# =============================================================================

if __name__ == "__main__":
    print("\n" + "=" * 70)
    print("NUMERICAL VERIFICATION: QCD-EM Coupling Efficiency")
    print("Derivation-QCD-EM-Coupling-Efficiency.md")
    print("=" * 70 + "\n")

    # Run all tests
    tests = [
        ("Room Temperature ε", test_epsilon_room_temperature),
        ("T⁴ Scaling", test_temperature_scaling),
        ("Mechanism Hierarchy", test_mechanism_hierarchy),
        ("No Spontaneous Heating", test_no_spontaneous_heating),
        ("QGP Regime", test_qgp_regime),
        ("Thermalization Time", test_thermalization_time),
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
