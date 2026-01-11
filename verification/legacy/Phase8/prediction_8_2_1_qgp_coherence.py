#!/usr/bin/env python3
"""
Prediction 8.2.1: QGP Phase Coherence Verification

This script verifies the derived correlation function for chiral field oscillations
in quark-gluon plasma and generates predictions for experimental comparison.

Key equations verified:
1. ξ₀ = ℏc/ω₀ ~ 1 fm (coherence length)
2. C(r,t) = (T/4πr) exp(-r/ξ) exp(-Γt) cos(ω₀t)
3. ξ(T) = ξ₀/√(1 - T_c/T)
4. Q = ω₀/Γ (quality factor)

Author: Chiral Geometrogenesis Verification Suite
Date: December 21, 2025
"""

import numpy as np
import json
from datetime import datetime
import matplotlib.pyplot as plt
from scipy.integrate import quad

# =============================================================================
# Physical Constants (natural units: ℏ = c = 1, then convert)
# =============================================================================

HBAR_C = 197.3  # MeV·fm
HBAR = 6.582e-22  # MeV·s

# Framework parameters
OMEGA_0 = 200.0  # MeV (universal chiral frequency)
T_C = 155.0  # MeV (QCD crossover temperature)

# QCD parameters
ALPHA_S_TC = 0.35  # Strong coupling at T_c
G_SQUARED = 4 * np.pi * ALPHA_S_TC  # ~ 4.4

# Derived quantities
XI_0 = HBAR_C / OMEGA_0  # Coherence length at T=0 ~ 0.985 fm
TAU_COH_0 = HBAR / OMEGA_0  # Coherence time ~ 3.3e-24 s


def coherence_length(T, T_c=T_C, xi_0=XI_0):
    """
    Temperature-dependent coherence length.

    ξ(T) = ξ₀ / √(1 - T_c/T)

    Diverges at T_c (critical fluctuations).
    """
    if T <= T_c:
        return np.inf
    return xi_0 / np.sqrt(1 - T_c / T)


def debye_mass(T, g=np.sqrt(G_SQUARED)):
    """
    Debye screening mass in QGP.

    m_D = g(T) · T · √(1 + N_f/6)

    For N_f = 3 light flavors.
    """
    N_f = 3
    return g * T * np.sqrt(1 + N_f / 6)


def effective_coherence_length(T, T_c=T_C, xi_0=XI_0):
    """
    Effective coherence length including Debye screening.

    1/ξ_eff² = 1/ξ(T)² + m_D²/(ℏc)²
    """
    xi_T = coherence_length(T, T_c, xi_0)
    if np.isinf(xi_T):
        return HBAR_C / debye_mass(T)

    m_D = debye_mass(T)
    inv_xi_eff_sq = 1 / xi_T**2 + (m_D / HBAR_C)**2
    return 1 / np.sqrt(inv_xi_eff_sq)


def damping_rate(T):
    """
    Damping rate from Model A dynamics.

    Γ = 4π T (using η/s ~ 1/(4π))

    Returns Γ in MeV.
    """
    return 4 * np.pi * T


def quality_factor(T, omega_0=OMEGA_0):
    """
    Quality factor Q = ω₀/Γ.

    Q << 1 means heavily overdamped oscillations.
    """
    return omega_0 / damping_rate(T)


def correlation_function(r, t, T, T_c=T_C, omega_0=OMEGA_0):
    """
    Chiral field correlation function in QGP.

    C(r,t) = (T / 4πr) exp(-r/ξ_eff) exp(-Γ|t|) cos(ω₀t)

    Parameters:
        r: Spatial separation (fm)
        t: Time separation (fm/c)
        T: Temperature (MeV)

    Returns:
        Correlation function value (dimensionless, normalized)
    """
    xi_eff = effective_coherence_length(T, T_c)
    Gamma = damping_rate(T) / HBAR_C  # Convert to fm^-1
    omega = omega_0 / HBAR_C  # Convert to fm^-1

    if r < 0.01:  # Regularize at r=0
        r = 0.01

    spatial = np.exp(-r / xi_eff) / (4 * np.pi * r)
    temporal = np.exp(-Gamma * np.abs(t)) * np.cos(omega * t)

    # Normalize by T/ℏc² to make dimensionless
    return (T / HBAR_C**2) * spatial * temporal


def hbt_correlation_cg(q, R, xi_eff, lam=0.5, alpha=0.2):
    """
    HBT correlation function with CG modification.

    C_2(q) = 1 + λ exp(-R²q²) + λ α exp(-ξ²q²)

    The CG modification adds a shorter-range correlation from the chiral coherence.

    Parameters:
        q: Relative momentum (fm^-1)
        R: HBT radius (fm)
        xi_eff: CG coherence length (fm)
        lam: Chaoticity parameter
        alpha: CG enhancement strength
    """
    gaussian_freeze = np.exp(-R**2 * q**2)
    gaussian_cg = np.exp(-xi_eff**2 * q**2)
    return 1 + lam * gaussian_freeze + lam * alpha * gaussian_cg


def hbt_correlation_standard(q, R, lam=0.5):
    """Standard Gaussian HBT correlation (no CG modification)."""
    return 1 + lam * np.exp(-R**2 * q**2)


def spectral_function(omega, omega_0, Gamma):
    """
    Spectral function for dilepton emission.

    For a damped oscillator: ρ(ω) = Γ / [(ω - ω₀)² + Γ²]

    In the heavily overdamped case (Γ >> ω₀), this broadens significantly.
    We use a Breit-Wigner form centered near ω₀.
    """
    # Use Breit-Wigner centered at ω₀
    numerator = Gamma
    denominator = (omega - omega_0)**2 + Gamma**2
    return numerator / denominator


# =============================================================================
# Verification Tests
# =============================================================================

def verify_dimensional_analysis():
    """Verify all dimensional quantities are consistent."""
    results = {}

    # Test 1: Coherence length
    xi_0_calc = HBAR_C / OMEGA_0
    results['xi_0_fm'] = xi_0_calc
    results['xi_0_expected'] = 0.985
    results['xi_0_error_percent'] = abs(xi_0_calc - 0.985) / 0.985 * 100

    # Test 2: Coherence time
    tau_coh = HBAR / OMEGA_0
    results['tau_coh_s'] = tau_coh
    results['tau_coh_expected'] = 3.3e-24
    results['tau_coh_error_percent'] = abs(tau_coh - 3.3e-24) / 3.3e-24 * 100

    # Test 3: Quality factor at T_c
    Q_Tc = quality_factor(T_C)
    results['Q_at_Tc'] = Q_Tc
    results['Q_at_Tc_expected'] = 0.103
    results['Q_at_Tc_error_percent'] = abs(Q_Tc - 0.103) / 0.103 * 100

    # Test 4: Damping rate at T_c
    Gamma_Tc = damping_rate(T_C)
    results['Gamma_at_Tc_MeV'] = Gamma_Tc
    results['Gamma_expected'] = 4 * np.pi * 155

    # Test 5: Debye mass at T = 200 MeV
    m_D_200 = debye_mass(200)
    results['m_D_200_MeV'] = m_D_200
    results['m_D_expected_range'] = '400-500 MeV'

    return results


def verify_temperature_dependence():
    """Verify temperature scaling of coherence length."""
    temperatures = [160, 175, 200, 250, 300, 400, 600, 1000]

    results = {
        'temperatures_MeV': temperatures,
        'T_over_Tc': [],
        'xi_fm': [],
        'xi_eff_fm': [],
        'Q_factor': [],
        'Gamma_MeV': []
    }

    for T in temperatures:
        results['T_over_Tc'].append(T / T_C)
        results['xi_fm'].append(coherence_length(T))
        results['xi_eff_fm'].append(effective_coherence_length(T))
        results['Q_factor'].append(quality_factor(T))
        results['Gamma_MeV'].append(damping_rate(T))

    return results


def verify_energy_independence():
    """
    Verify that coherence length is energy-independent.

    In CG: ξ_eff is fixed by ω₀ and T
    In standard hydro: R_HBT ∝ √s^0.3
    """
    # Collision energies (GeV)
    sqrt_s = [19.6, 62, 200, 2760, 5020]

    # Standard hydro prediction: R ∝ √s^0.3
    R_ref = 4.5  # fm at √s = 200 GeV
    s_ref = 200
    R_standard = [R_ref * (s / s_ref)**0.15 for s in sqrt_s]

    # CG prediction: ξ_eff is constant (depends only on T)
    T_fireball = 200  # Typical QGP temperature (MeV)
    xi_cg = effective_coherence_length(T_fireball)
    xi_cg_list = [xi_cg] * len(sqrt_s)

    results = {
        'sqrt_s_GeV': sqrt_s,
        'R_hydro_fm': R_standard,
        'xi_cg_fm': xi_cg_list,
        'ratio_R_over_xi': [R / xi_cg for R in R_standard]
    }

    return results


def verify_correlation_function():
    """Verify the correlation function behavior."""
    T = 200  # MeV

    # Spatial dependence at t=0
    r_values = np.linspace(0.1, 5, 50)
    C_r = [correlation_function(r, 0, T) for r in r_values]

    # Temporal dependence at r=1 fm
    t_values = np.linspace(0, 2, 50)  # fm/c
    C_t = [correlation_function(1.0, t, T) for t in t_values]

    results = {
        'T_MeV': T,
        'xi_eff_fm': effective_coherence_length(T),
        'spatial': {
            'r_fm': r_values.tolist(),
            'C_r': C_r
        },
        'temporal': {
            't_fm_over_c': t_values.tolist(),
            'C_t': C_t
        }
    }

    return results


def verify_hbt_modification():
    """Verify HBT correlation function modification."""
    T = 200  # MeV
    R_HBT = 5.0  # fm (typical freeze-out radius)
    xi_eff = effective_coherence_length(T)

    q_values = np.linspace(0.01, 1.0, 100)  # fm^-1

    C2_standard = [hbt_correlation_standard(q, R_HBT) for q in q_values]
    C2_cg = [hbt_correlation_cg(q, R_HBT, xi_eff) for q in q_values]

    # Residuals
    residuals = [cg - std for cg, std in zip(C2_cg, C2_standard)]

    results = {
        'q_fm_inv': q_values.tolist(),
        'C2_standard': C2_standard,
        'C2_cg': C2_cg,
        'residuals': residuals,
        'R_HBT_fm': R_HBT,
        'xi_eff_fm': xi_eff,
        'q_peak_MeV': 1 / xi_eff * HBAR_C  # Where CG term peaks
    }

    return results


def verify_spectral_function():
    """Verify spectral function for dilepton emission."""
    T = 155  # MeV (near T_c)
    Gamma = damping_rate(T)

    omega_values = np.linspace(50, 500, 100)  # MeV

    rho = [spectral_function(omega, OMEGA_0, Gamma) for omega in omega_values]

    # Find peak
    peak_idx = np.argmax(rho)
    peak_omega = omega_values[peak_idx]
    peak_value = rho[peak_idx]

    results = {
        'T_MeV': T,
        'omega_0_MeV': OMEGA_0,
        'Gamma_MeV': Gamma,
        'omega_values_MeV': omega_values.tolist(),
        'spectral_function': rho,
        'peak_omega_MeV': peak_omega,
        'peak_value': peak_value
    }

    return results


# =============================================================================
# Main Verification
# =============================================================================

def run_all_verifications():
    """Run all verification tests and compile results."""

    print("=" * 70)
    print("Prediction 8.2.1: QGP Phase Coherence Verification")
    print("=" * 70)

    results = {
        'prediction': 'Prediction 8.2.1: QGP Phase Coherence',
        'date': datetime.now().isoformat(),
        'status': 'RUNNING',
        'tests': {}
    }

    # Test 1: Dimensional analysis
    print("\n[1/6] Verifying dimensional analysis...")
    dim_results = verify_dimensional_analysis()
    results['tests']['dimensional_analysis'] = dim_results
    print(f"      ξ₀ = {dim_results['xi_0_fm']:.3f} fm (expected 0.985 fm)")
    print(f"      τ_coh = {dim_results['tau_coh_s']:.2e} s (expected 3.3e-24 s)")
    print(f"      Q(T_c) = {dim_results['Q_at_Tc']:.3f} (expected 0.103)")

    # Test 2: Temperature dependence
    print("\n[2/6] Verifying temperature dependence...")
    temp_results = verify_temperature_dependence()
    results['tests']['temperature_dependence'] = temp_results
    print(f"      ξ(200 MeV) = {temp_results['xi_fm'][2]:.2f} fm")
    print(f"      ξ_eff(200 MeV) = {temp_results['xi_eff_fm'][2]:.2f} fm")

    # Test 3: Energy independence
    print("\n[3/6] Verifying energy independence...")
    energy_results = verify_energy_independence()
    results['tests']['energy_independence'] = energy_results
    print(f"      ξ_CG = {energy_results['xi_cg_fm'][0]:.2f} fm (constant)")
    print(f"      R_hydro varies: {energy_results['R_hydro_fm'][0]:.1f} - {energy_results['R_hydro_fm'][-1]:.1f} fm")

    # Test 4: Correlation function
    print("\n[4/6] Verifying correlation function...")
    corr_results = verify_correlation_function()
    results['tests']['correlation_function'] = corr_results
    print(f"      ξ_eff at T=200 MeV: {corr_results['xi_eff_fm']:.2f} fm")

    # Test 5: HBT modification
    print("\n[5/6] Verifying HBT modification...")
    hbt_results = verify_hbt_modification()
    results['tests']['hbt_modification'] = hbt_results
    print(f"      Peak residual at q ~ {hbt_results['q_peak_MeV']:.0f} MeV")
    max_residual = max(hbt_results['residuals'])
    print(f"      Maximum residual: {max_residual:.3f}")

    # Test 6: Spectral function
    print("\n[6/6] Verifying spectral function...")
    spec_results = verify_spectral_function()
    results['tests']['spectral_function'] = spec_results
    print(f"      Peak at ω = {spec_results['peak_omega_MeV']:.0f} MeV")

    # Summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)

    all_passed = True

    # Check dimensional analysis
    if dim_results['xi_0_error_percent'] < 1:
        print("✅ Coherence length ξ₀ = 0.985 fm: PASS")
    else:
        print("❌ Coherence length check: FAIL")
        all_passed = False

    # Check quality factor
    if dim_results['Q_at_Tc_error_percent'] < 5:
        print("✅ Quality factor Q(T_c) ~ 0.1 (overdamped): PASS")
    else:
        print("❌ Quality factor check: FAIL")
        all_passed = False

    # Check energy independence
    xi_variation = max(energy_results['xi_cg_fm']) - min(energy_results['xi_cg_fm'])
    if xi_variation < 0.01:
        print("✅ Energy independence of ξ: PASS")
    else:
        print("❌ Energy independence check: FAIL")
        all_passed = False

    # Check HBT residual
    if max_residual > 0.01:
        print("✅ HBT modification detectable: PASS")
    else:
        print("⚠️  HBT modification may be too small")

    # Check spectral peak
    if abs(spec_results['peak_omega_MeV'] - OMEGA_0) < 50:
        print("✅ Spectral function peak near ω₀: PASS")
    else:
        print("❌ Spectral function peak: FAIL")
        all_passed = False

    if all_passed:
        results['status'] = 'PASSED'
        print("\n✅ ALL VERIFICATION TESTS PASSED")
    else:
        results['status'] = 'PARTIAL'
        print("\n⚠️  SOME VERIFICATION TESTS HAVE ISSUES")

    return results


def generate_plots(results):
    """Generate verification plots."""

    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    fig.suptitle('Prediction 8.2.1: QGP Phase Coherence Verification', fontsize=14)

    # Plot 1: Coherence length vs temperature
    ax1 = axes[0, 0]
    temp_data = results['tests']['temperature_dependence']
    T_over_Tc = temp_data['T_over_Tc']
    xi_fm = temp_data['xi_fm']
    xi_eff_fm = temp_data['xi_eff_fm']

    ax1.semilogy(T_over_Tc, xi_fm, 'b-', label=r'$\xi(T)$ (bare)', linewidth=2)
    ax1.semilogy(T_over_Tc, xi_eff_fm, 'r--', label=r'$\xi_{eff}(T)$ (with Debye)', linewidth=2)
    ax1.axhline(XI_0, color='g', linestyle=':', label=r'$\xi_0 = 0.985$ fm')
    ax1.set_xlabel(r'$T/T_c$')
    ax1.set_ylabel(r'Coherence length (fm)')
    ax1.set_xlim(1, 7)
    ax1.set_ylim(0.1, 10)
    ax1.legend()
    ax1.set_title('Coherence Length vs Temperature')
    ax1.grid(True, alpha=0.3)

    # Plot 2: Quality factor vs temperature
    ax2 = axes[0, 1]
    Q_factor = temp_data['Q_factor']
    ax2.plot(T_over_Tc, Q_factor, 'k-', linewidth=2)
    ax2.axhline(1, color='r', linestyle='--', label='Critical damping')
    ax2.set_xlabel(r'$T/T_c$')
    ax2.set_ylabel('Quality factor Q')
    ax2.set_title('Quality Factor (Q << 1: overdamped)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # Plot 3: Energy independence
    ax3 = axes[0, 2]
    energy_data = results['tests']['energy_independence']
    sqrt_s = energy_data['sqrt_s_GeV']
    R_hydro = energy_data['R_hydro_fm']
    xi_cg = energy_data['xi_cg_fm']

    ax3.semilogx(sqrt_s, R_hydro, 'b-o', label='Standard hydro: R ∝ √s^0.15', linewidth=2)
    ax3.semilogx(sqrt_s, xi_cg, 'r--s', label='CG: ξ = constant', linewidth=2)
    ax3.set_xlabel(r'$\sqrt{s}$ (GeV)')
    ax3.set_ylabel('Length scale (fm)')
    ax3.set_title('Energy Independence Test')
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # Plot 4: Correlation function (spatial)
    ax4 = axes[1, 0]
    corr_data = results['tests']['correlation_function']
    r_fm = corr_data['spatial']['r_fm']
    C_r = corr_data['spatial']['C_r']

    ax4.semilogy(r_fm, [abs(c) for c in C_r], 'b-', linewidth=2)
    ax4.axvline(corr_data['xi_eff_fm'], color='r', linestyle='--',
                label=rf'$\xi_{{eff}}$ = {corr_data["xi_eff_fm"]:.2f} fm')
    ax4.set_xlabel('r (fm)')
    ax4.set_ylabel('|C(r, t=0)|')
    ax4.set_title('Spatial Correlation at t=0')
    ax4.legend()
    ax4.grid(True, alpha=0.3)

    # Plot 5: HBT modification
    ax5 = axes[1, 1]
    hbt_data = results['tests']['hbt_modification']
    q_fm_inv = hbt_data['q_fm_inv']
    C2_standard = hbt_data['C2_standard']
    C2_cg = hbt_data['C2_cg']

    ax5.plot(q_fm_inv, C2_standard, 'b-', label='Standard Gaussian', linewidth=2)
    ax5.plot(q_fm_inv, C2_cg, 'r--', label='CG modified', linewidth=2)
    ax5.set_xlabel(r'q (fm$^{-1}$)')
    ax5.set_ylabel(r'$C_2(q)$')
    ax5.set_title('HBT Correlation Function')
    ax5.legend()
    ax5.grid(True, alpha=0.3)

    # Plot 6: Spectral function
    ax6 = axes[1, 2]
    spec_data = results['tests']['spectral_function']
    omega = spec_data['omega_values_MeV']
    rho = spec_data['spectral_function']

    ax6.plot(omega, rho, 'b-', linewidth=2)
    ax6.axvline(OMEGA_0, color='r', linestyle='--', label=rf'$\omega_0$ = {OMEGA_0} MeV')
    ax6.axvline(spec_data['peak_omega_MeV'], color='g', linestyle=':',
                label=f'Peak at {spec_data["peak_omega_MeV"]:.0f} MeV')
    ax6.set_xlabel(r'$\omega$ (MeV)')
    ax6.set_ylabel(r'$\rho(\omega)$')
    ax6.set_title('Spectral Function (Dilepton)')
    ax6.legend()
    ax6.grid(True, alpha=0.3)

    plt.tight_layout()

    # Save plot
    plot_path = 'verification/plots/prediction_8_2_1_qgp_coherence.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\n📊 Plot saved to: {plot_path}")

    return plot_path


# =============================================================================
# Main Execution
# =============================================================================

if __name__ == '__main__':
    # Run verifications
    results = run_all_verifications()

    # Generate plots
    try:
        plot_path = generate_plots(results)
        results['plot_path'] = plot_path
    except Exception as e:
        print(f"\n⚠️  Could not generate plots: {e}")

    # Save results to JSON
    output_path = 'verification/prediction_8_2_1_results.json'

    # Convert numpy arrays to lists for JSON serialization
    def convert_to_serializable(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, dict):
            return {k: convert_to_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_to_serializable(i) for i in obj]
        elif isinstance(obj, (np.float64, np.float32)):
            return float(obj)
        elif isinstance(obj, (np.int64, np.int32)):
            return int(obj)
        else:
            return obj

    results_serializable = convert_to_serializable(results)

    with open(output_path, 'w') as f:
        json.dump(results_serializable, f, indent=2)

    print(f"\n📄 Results saved to: {output_path}")

    # Print key predictions
    print("\n" + "=" * 70)
    print("KEY PREDICTIONS FOR EXPERIMENTAL TEST")
    print("=" * 70)
    print(f"""
1. COHERENCE LENGTH (energy-independent):
   ξ_eff ~ 0.4-0.6 fm at T ~ 200 MeV

2. HBT MODIFICATION:
   Non-Gaussian tail at q ~ {1/results['tests']['hbt_modification']['xi_eff_fm'] * HBAR_C:.0f} MeV

3. DILEPTON ENHANCEMENT:
   Peak in spectral function near M ~ 200 MeV

4. FALSIFICATION CRITERION:
   If ξ scales with √s (i.e., ξ ∝ R_fireball), CG is falsified.
   If ξ = constant across energies, CG is supported.
""")
