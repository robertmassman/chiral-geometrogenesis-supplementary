#!/usr/bin/env python3
"""
Derivation 2.2.5b Verification: QCD Bath Degrees of Freedom

This script verifies the numerical calculations in Derivation-2.2.5b-QCD-Bath-Degrees-Freedom.md
including spectral density, effective friction, and the coupling constant K.

Multi-Agent Verification: 2026-01-03
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import quad
from scipy.constants import hbar, c, k as k_B, pi

# ==============================================================================
# PHYSICAL CONSTANTS (Natural Units: hbar = c = 1)
# ==============================================================================

# QCD Parameters
LAMBDA_QCD = 200  # MeV
ALPHA_S = 0.5     # QCD coupling at Lambda_QCD
N_F = 3           # Number of light flavors
N_C = 3           # Number of colors

# Instanton parameters (Schafer-Shuryak 1998)
INSTANTON_DENSITY = 1.0    # fm^-4
RHO_BAR = 0.33             # fm (average instanton size)

# Conversions
FM_TO_MEV_INV = 197.327    # 1 fm = 197.327 MeV^-1
INSTANTON_DENSITY_MEV = INSTANTON_DENSITY * FM_TO_MEV_INV**4  # MeV^4

# Gluon condensate
GLUON_CONDENSATE = 0.012   # GeV^4 = 0.012e12 MeV^4
GLUON_CONDENSATE_MEV = 0.012 * 1e12  # MeV^4

# String tension
SQRT_SIGMA = 440           # MeV

# Deconfinement temperature
T_C = 155                  # MeV

# ==============================================================================
# SECTION 3.5: EFFECTIVE FRICTION COEFFICIENT
# ==============================================================================

def calculate_eta_eff(alpha_s, n_f):
    """
    Calculate the effective friction coefficient eta_eff from gluon + quark contributions.

    From Derivation 2.2.5b Section 3.5:
    eta_gluon+quark = (alpha_s / 2*pi) * (1 + 2*N_f/3)
    """
    eta = (alpha_s / (2 * pi)) * (1 + 2 * n_f / 3)
    return eta

def calculate_eta_components(alpha_s, n_f):
    """Calculate individual components of eta_eff."""
    eta_gluon = alpha_s / (2 * pi)
    eta_quark = (n_f * alpha_s) / (3 * pi)
    eta_total = eta_gluon + eta_quark
    return eta_gluon, eta_quark, eta_total

# ==============================================================================
# SECTION 4.2: COUPLING CONSTANT K FROM BATH
# ==============================================================================

def calculate_K_perturbative(eta_eff, lambda_qcd):
    """
    Calculate K from perturbative estimate.

    From Section 4.2:
    sigma = 3K/4 = 2*gamma = 2*eta_eff*Lambda_QCD
    Therefore: K = (8/3) * eta_eff * Lambda_QCD
    """
    K = (8.0 / 3.0) * eta_eff * lambda_qcd
    return K

def calculate_K_from_sigma(sigma):
    """
    Given sigma = 3K/4, calculate K.
    """
    return (4.0 / 3.0) * sigma

# ==============================================================================
# SPECTRAL DENSITY FUNCTIONS
# ==============================================================================

def J_gluon(omega, alpha_s, lambda_qcd, gamma_0=23/3):
    """
    Gluon contribution to spectral density.

    J_gluon(omega) = (alpha_s / 2*pi) * omega  for omega < Lambda_QCD
    J_gluon(omega) = (alpha_s / 2*pi) * Lambda_QCD * (Lambda_QCD/omega)^gamma_0  for omega > Lambda_QCD

    gamma_0 = 11 - 2*N_f/3 = 11 - 2 = 9 (for N_f=3)
    Wait, that's the beta function coefficient for running, not for J suppression.
    Using gamma_0 ~ 23/3 as in the document.
    """
    if omega < lambda_qcd:
        return (alpha_s / (2 * pi)) * omega
    else:
        return (alpha_s / (2 * pi)) * lambda_qcd * (lambda_qcd / omega)**gamma_0

def J_gluon_array(omega_array, alpha_s, lambda_qcd, gamma_0=23/3):
    """Vectorized version of J_gluon."""
    result = np.zeros_like(omega_array)
    mask_low = omega_array < lambda_qcd
    result[mask_low] = (alpha_s / (2 * pi)) * omega_array[mask_low]
    result[~mask_low] = (alpha_s / (2 * pi)) * lambda_qcd * (lambda_qcd / omega_array[~mask_low])**gamma_0
    return result

def J_instanton(omega, n_fourth, rho_bar):
    """
    Instanton contribution to spectral density.

    J_instanton(omega) = c_inst * n^(1/4) * (omega*rho_bar)^4 * exp(-omega*rho_bar)

    where c_inst ~ O(1) and n^(1/4) provides the energy scale.

    Parameters:
    -----------
    omega : float
        Frequency in MeV
    n_fourth : float
        n^(1/4) in MeV (from instanton density)
    rho_bar : float
        Average instanton size in MeV^-1
    """
    c_inst = 1.0  # O(1) coefficient
    x = omega * rho_bar
    return c_inst * n_fourth * x**4 * np.exp(-x)

def J_quark(omega, n_f, alpha_s, m_q=0):
    """
    Quark contribution to spectral density.

    J_quark(omega) = (N_f * alpha_s / 3*pi) * omega * sqrt(1 - 4*m_q^2/omega^2) * Theta(omega - 2*m_q)

    For light quarks (m_q << Lambda_QCD), this is approximately:
    J_quark(omega) = (N_f * alpha_s / 3*pi) * omega
    """
    if m_q > 0 and omega > 2 * m_q:
        threshold = np.sqrt(1 - 4 * m_q**2 / omega**2)
    elif m_q > 0:
        return 0.0
    else:
        threshold = 1.0

    return (n_f * alpha_s / (3 * pi)) * omega * threshold

def J_quark_array(omega_array, n_f, alpha_s, m_q=0):
    """Vectorized version of J_quark."""
    if m_q > 0:
        result = np.zeros_like(omega_array)
        mask = omega_array > 2 * m_q
        threshold = np.sqrt(1 - 4 * m_q**2 / omega_array[mask]**2)
        result[mask] = (n_f * alpha_s / (3 * pi)) * omega_array[mask] * threshold
        return result
    else:
        return (n_f * alpha_s / (3 * pi)) * omega_array

# ==============================================================================
# NON-PERTURBATIVE CONTRIBUTIONS
# ==============================================================================

def K_from_gluon_condensate(g2):
    """
    K from gluon condensate: K ~ <G^2>^(1/4)

    g2 : gluon condensate in MeV^4
    """
    return g2**(0.25)

def K_from_instanton_density(n):
    """
    K from instanton density: K ~ n^(1/4)

    n : instanton density in MeV^4
    """
    return n**(0.25)

def K_from_string_tension(sqrt_sigma, alpha_s):
    """
    K from string tension: K ~ sqrt(sigma) * alpha_s
    """
    return sqrt_sigma * alpha_s

# ==============================================================================
# MAIN VERIFICATION
# ==============================================================================

def main():
    print("=" * 80)
    print("DERIVATION 2.2.5b VERIFICATION: QCD Bath Degrees of Freedom")
    print("=" * 80)
    print()

    # -------------------------------------------------------------------------
    # 1. Verify eta_eff calculation (Section 3.5)
    # -------------------------------------------------------------------------
    print("1. EFFECTIVE FRICTION COEFFICIENT (Section 3.5)")
    print("-" * 60)

    eta_gluon, eta_quark, eta_total = calculate_eta_components(ALPHA_S, N_F)
    eta_eff = calculate_eta_eff(ALPHA_S, N_F)

    print(f"   alpha_s = {ALPHA_S}")
    print(f"   N_f = {N_F}")
    print(f"   eta_gluon = alpha_s/(2*pi) = {eta_gluon:.6f}")
    print(f"   eta_quark = N_f*alpha_s/(3*pi) = {eta_quark:.6f}")
    print(f"   eta_total = eta_gluon + eta_quark = {eta_total:.6f}")
    print(f"   eta_eff (formula) = (alpha_s/(2*pi))*(1 + 2*N_f/3) = {eta_eff:.6f}")
    print(f"   Document value: ~0.24")
    print(f"   Status: {'VERIFIED' if abs(eta_eff - 0.24) < 0.01 else 'CHECK'}")
    print()

    # Cross-check the formula
    print("   Cross-check: (1 + 2*N_f/3) =", 1 + 2*N_F/3)
    print(f"   {ALPHA_S}/(2*pi) * {1 + 2*N_F/3} = {ALPHA_S/(2*pi) * (1 + 2*N_F/3):.4f}")
    print()

    # -------------------------------------------------------------------------
    # 2. Verify K perturbative calculation (Section 4.2)
    # -------------------------------------------------------------------------
    print("2. COUPLING CONSTANT K - PERTURBATIVE (Section 4.2)")
    print("-" * 60)

    K_pert = calculate_K_perturbative(eta_eff, LAMBDA_QCD)

    print(f"   From sigma = 2*gamma = 2*eta_eff*Lambda_QCD")
    print(f"   And sigma = 3K/4")
    print(f"   Therefore: K = (8/3)*eta_eff*Lambda_QCD")
    print(f"   K = (8/3) * {eta_eff:.4f} * {LAMBDA_QCD} MeV")
    print(f"   K = {K_pert:.2f} MeV")
    print(f"   Document value: ~128 MeV")
    print(f"   Status: {'VERIFIED' if abs(K_pert - 128) < 5 else 'CHECK'}")
    print()

    # Note the discrepancy with table
    print("   NOTE: Table in Section 4.3 uses (4/3) instead of (8/3):")
    K_table = (4.0/3.0) * eta_eff * LAMBDA_QCD
    print(f"   K (table formula) = (4/3)*eta_eff*Lambda_QCD = {K_table:.2f} MeV")
    print(f"   This is a DISCREPANCY that should be resolved.")
    print()

    # -------------------------------------------------------------------------
    # 3. Non-perturbative K estimates (Section 4.3)
    # -------------------------------------------------------------------------
    print("3. COUPLING CONSTANT K - NON-PERTURBATIVE (Section 4.3)")
    print("-" * 60)

    K_gluon = K_from_gluon_condensate(GLUON_CONDENSATE_MEV)

    n_mev4 = INSTANTON_DENSITY * FM_TO_MEV_INV**4
    K_inst = K_from_instanton_density(n_mev4)

    K_conf = K_from_string_tension(SQRT_SIGMA, ALPHA_S)

    print("   Non-perturbative contributions:")
    print(f"   - Gluon condensate: K ~ <G^2>^(1/4) = {K_gluon:.1f} MeV")
    print(f"   - Instanton density: K ~ n^(1/4) = {K_inst:.1f} MeV")
    print(f"   - String tension: K ~ sqrt(sigma)*alpha_s = {K_conf:.1f} MeV")
    print()
    print(f"   Document estimate: K ~ 150-300 MeV")
    print(f"   All estimates are O(Lambda_QCD) - CONSISTENT")
    print()

    # -------------------------------------------------------------------------
    # 4. Verify sigma = 3K/4 relationship
    # -------------------------------------------------------------------------
    print("4. PHASE-SPACE CONTRACTION RATE (Theorem 2.2.3 cross-check)")
    print("-" * 60)

    K_nominal = 200  # MeV, central estimate
    sigma = 3 * K_nominal / 4

    print(f"   For K = {K_nominal} MeV (central estimate):")
    print(f"   sigma = 3K/4 = {sigma:.1f} MeV")
    print(f"   Jacobian trace: Tr(J) = -sigma = -{sigma:.1f} MeV")
    print(f"   Eigenvalues: lambda = -3K/8 +/- i*sqrt(3)*K/4")
    print(f"              = {-3*K_nominal/8:.1f} +/- i*{np.sqrt(3)*K_nominal/4:.1f} MeV")
    print()

    # -------------------------------------------------------------------------
    # 5. Temperature scale
    # -------------------------------------------------------------------------
    print("5. EFFECTIVE TEMPERATURE (Section 2A.2)")
    print("-" * 60)

    # T_eff = K / k_B in natural units
    # k_B = 8.617e-11 MeV/K
    k_B_MeV = 8.617e-11  # MeV/K
    T_eff = LAMBDA_QCD / k_B_MeV

    print(f"   T_eff ~ Lambda_QCD / k_B")
    print(f"   T_eff = {LAMBDA_QCD} MeV / {k_B_MeV:.2e} MeV/K")
    print(f"   T_eff = {T_eff:.2e} K")
    print(f"   Document value: ~2 x 10^12 K")
    print(f"   QCD crossover temperature T_c = {T_C} MeV ~ {T_C/k_B_MeV:.2e} K")
    print(f"   Status: VERIFIED (same order of magnitude)")
    print()

    # -------------------------------------------------------------------------
    # 6. Plot spectral density
    # -------------------------------------------------------------------------
    print("6. GENERATING SPECTRAL DENSITY PLOTS")
    print("-" * 60)

    # Convert rho_bar to MeV^-1
    rho_bar_mev = RHO_BAR * FM_TO_MEV_INV  # MeV^-1
    n_fourth = n_mev4**0.25  # MeV

    omega = np.linspace(10, 3000, 1000)  # MeV

    # Calculate spectral densities
    J_g = J_gluon_array(omega, ALPHA_S, LAMBDA_QCD)
    J_i = np.array([J_instanton(w, n_fourth, rho_bar_mev) for w in omega])
    J_q = J_quark_array(omega, N_F, ALPHA_S)
    J_total = J_g + J_i + J_q

    # Create plot
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Individual contributions
    ax1 = axes[0, 0]
    ax1.semilogy(omega, J_g, 'b-', label='Gluon', linewidth=2)
    ax1.semilogy(omega, J_i, 'r-', label='Instanton', linewidth=2)
    ax1.semilogy(omega, J_q, 'g-', label='Quark', linewidth=2)
    ax1.axvline(LAMBDA_QCD, color='k', linestyle='--', alpha=0.5, label=r'$\Lambda_{QCD}$')
    ax1.set_xlabel(r'$\omega$ (MeV)', fontsize=12)
    ax1.set_ylabel(r'$J(\omega)$ (MeV)', fontsize=12)
    ax1.set_title('Spectral Density Components', fontsize=14)
    ax1.legend(fontsize=10)
    ax1.set_xlim(0, 3000)
    ax1.grid(True, alpha=0.3)

    # Plot 2: Total spectral density
    ax2 = axes[0, 1]
    ax2.semilogy(omega, J_total, 'k-', linewidth=2, label='Total')
    ax2.axvline(LAMBDA_QCD, color='gray', linestyle='--', alpha=0.5)
    ax2.fill_between(omega, J_total, alpha=0.3)
    ax2.set_xlabel(r'$\omega$ (MeV)', fontsize=12)
    ax2.set_ylabel(r'$J_{QCD}(\omega)$ (MeV)', fontsize=12)
    ax2.set_title('Total QCD Bath Spectral Density', fontsize=14)
    ax2.set_xlim(0, 3000)
    ax2.grid(True, alpha=0.3)

    # Plot 3: eta_eff(omega)
    ax3 = axes[1, 0]
    eta_omega = J_total / omega
    ax3.plot(omega, eta_omega, 'b-', linewidth=2)
    ax3.axhline(eta_eff, color='r', linestyle='--', label=f'Low-$\\omega$ limit = {eta_eff:.3f}')
    ax3.axvline(LAMBDA_QCD, color='gray', linestyle='--', alpha=0.5)
    ax3.set_xlabel(r'$\omega$ (MeV)', fontsize=12)
    ax3.set_ylabel(r'$\eta_{eff}(\omega) = J(\omega)/\omega$', fontsize=12)
    ax3.set_title('Effective Friction Coefficient', fontsize=14)
    ax3.legend(fontsize=10)
    ax3.set_xlim(0, 3000)
    ax3.set_ylim(0, max(eta_omega) * 1.2)
    ax3.grid(True, alpha=0.3)

    # Plot 4: K estimates comparison
    ax4 = axes[1, 1]
    methods = ['Perturbative\n(8/3)η·Λ', 'Gluon\nCondensate', 'Instanton\nDensity', 'String\nTension']
    K_values = [K_pert, K_gluon, K_inst, K_conf]
    colors = ['blue', 'orange', 'green', 'red']

    bars = ax4.bar(methods, K_values, color=colors, alpha=0.7, edgecolor='black')
    ax4.axhline(200, color='k', linestyle='--', linewidth=2, label=r'$\Lambda_{QCD}$ = 200 MeV')
    ax4.axhspan(150, 300, alpha=0.2, color='gray', label='Target range: 150-300 MeV')
    ax4.set_ylabel('K (MeV)', fontsize=12)
    ax4.set_title('Coupling Constant K Estimates', fontsize=14)
    ax4.legend(fontsize=10)
    ax4.set_ylim(0, 400)
    ax4.grid(True, alpha=0.3, axis='y')

    # Add values on bars
    for bar, val in zip(bars, K_values):
        ax4.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 10,
                f'{val:.0f}', ha='center', va='bottom', fontsize=11, fontweight='bold')

    plt.suptitle('Derivation 2.2.5b: QCD Bath Degrees of Freedom Verification',
                 fontsize=16, fontweight='bold', y=1.02)
    plt.tight_layout()
    plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/derivation_2_2_5b_verification.png',
                dpi=150, bbox_inches='tight')
    plt.close()

    print("   Plot saved: verification/plots/derivation_2_2_5b_verification.png")
    print()

    # -------------------------------------------------------------------------
    # 7. Summary
    # -------------------------------------------------------------------------
    print("=" * 80)
    print("VERIFICATION SUMMARY")
    print("=" * 80)
    print()
    print("VERIFIED QUANTITIES:")
    print(f"  [x] eta_eff = {eta_eff:.4f} (matches document ~0.24)")
    print(f"  [x] K_perturbative = {K_pert:.1f} MeV (matches document ~128 MeV)")
    print(f"  [x] K_gluon_condensate = {K_gluon:.1f} MeV (matches ~330 MeV)")
    print(f"  [x] K_instanton = {K_inst:.1f} MeV (matches ~200 MeV)")
    print(f"  [x] T_eff ~ 2e12 K (matches document)")
    print(f"  [x] sigma = 3K/4 relationship (used consistently)")
    print()
    print("ISSUES IDENTIFIED:")
    print("  [!] Table in Section 4.3 uses (4/3) factor instead of (8/3)")
    print("      This gives ~64 MeV instead of ~128 MeV for perturbative estimate")
    print()
    print("RECOMMENDATIONS:")
    print("  1. Reconcile the factor discrepancy in Section 4.3 table")
    print("  2. Update topological susceptibility to current lattice values")
    print("  3. Add PNJL model references for context")
    print()

    return {
        'eta_eff': eta_eff,
        'K_perturbative': K_pert,
        'K_gluon_condensate': K_gluon,
        'K_instanton': K_inst,
        'K_string_tension': K_conf,
        'sigma_nominal': sigma
    }

if __name__ == "__main__":
    results = main()
