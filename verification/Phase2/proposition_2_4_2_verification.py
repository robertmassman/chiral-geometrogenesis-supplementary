#!/usr/bin/env python3
"""
Verification Script for Proposition 2.4.2: Pre-Geometric Beta-Function from Unified Gauge Groups

This script verifies the numerical calculations in Proposition 2.4.2:
1. Beta-function coefficients for unified gauge groups
2. SM running from M_Z to M_GUT
3. Required pre-geometric b0
4. E6 -> E8 cascade unification verification
5. Optimal M_E8 threshold calculation

Author: Multi-Agent Verification System
Date: 2026-01-16
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Create plots directory if it doesn't exist
PLOTS_DIR = Path(__file__).parent.parent / "plots"
PLOTS_DIR.mkdir(exist_ok=True)

# =============================================================================
# Physical Constants
# =============================================================================

# Mass scales (GeV)
M_Z = 91.1876  # Z boson mass (PDG 2024)
M_GUT = 1.0e16  # GUT scale
M_P = 1.22e19   # Planck mass

# Strong coupling at M_Z (PDG 2024)
ALPHA_S_MZ = 0.1180
ALPHA_S_MZ_ERR = 0.0009

# CG Framework prediction
INV_ALPHA_S_GEOM = 64  # (N_c^2 - 1)^2 = 8^2 = 64
THETA_O = np.arccos(-1/3)  # Obtuse dihedral angle of stella octangula
THETA_T = np.arccos(1/3)   # Acute dihedral angle
SCHEME_FACTOR = THETA_O / THETA_T  # ~1.55215
INV_ALPHA_S_TARGET = INV_ALPHA_S_GEOM * SCHEME_FACTOR  # ~99.34

# =============================================================================
# Group Theory Data
# =============================================================================

# Dual Coxeter numbers (C_A for adjoint Casimir)
CASIMIR = {
    'SU3': 3,
    'SU5': 5,
    'SO10': 8,
    'E6': 12,
    'E8': 30
}

# Beta function data for minimal GUTs with 3 generations
# Format: (C_A, T_F*n_F, T_H*n_H)
BETA_DATA = {
    'SU3': (3, 6*0.5, 0),       # n_f=6 quarks, T_F=1/2 each
    'SU5': (5, 6, 5.5),         # 3 gen x (5-bar + 10), Higgs: 5 + 24
    'SO10': (8, 6, 8),          # 3 gen x 16, Higgs: 16 + 16-bar + 45
    'E6': (12, 9, 6),           # 3 gen x 27, Higgs: 27 + 27-bar
    'E8_pure': (30, 0, 0)       # Pure gauge, no matter
}

def compute_b0(c_a, t_f_n_f, t_h_n_h):
    """Compute one-loop beta function coefficient b0."""
    return (11/3) * c_a - (4/3) * t_f_n_f - (1/3) * t_h_n_h

def compute_all_b0():
    """Compute b0 for all groups."""
    results = {}
    for group, (c_a, t_f_n_f, t_h_n_h) in BETA_DATA.items():
        b0_gauge = (11/3) * c_a
        b0_ferm = -(4/3) * t_f_n_f
        b0_higgs = -(1/3) * t_h_n_h
        b0_total = compute_b0(c_a, t_f_n_f, t_h_n_h)
        results[group] = {
            'C_A': c_a,
            'b0_gauge': b0_gauge,
            'b0_ferm': b0_ferm,
            'b0_higgs': b0_higgs,
            'b0_total': b0_total
        }
    return results

# =============================================================================
# RG Running Functions
# =============================================================================

def one_loop_running(inv_alpha_1, b0, mu1, mu2):
    """
    One-loop RG running of inverse coupling.

    1/alpha(mu2) = 1/alpha(mu1) + (b0/2pi) * ln(mu2/mu1)
    """
    return inv_alpha_1 + (b0 / (2 * np.pi)) * np.log(mu2 / mu1)

def compute_sm_running():
    """Compute SM running from M_Z to M_GUT."""
    # QCD beta function coefficient with n_f = 6
    b0_qcd = 7.0  # = (11*3 - 2*6)/3 = (33-12)/3 = 7

    inv_alpha_mz = 1 / ALPHA_S_MZ
    inv_alpha_gut = one_loop_running(inv_alpha_mz, b0_qcd, M_Z, M_GUT)

    delta_inv_alpha = inv_alpha_gut - inv_alpha_mz

    return {
        'inv_alpha_mz': inv_alpha_mz,
        'inv_alpha_gut': inv_alpha_gut,
        'delta_inv_alpha': delta_inv_alpha,
        'b0_qcd': b0_qcd
    }

def compute_required_b0():
    """Compute required b0 to reach target from M_GUT to M_P."""
    sm_results = compute_sm_running()
    inv_alpha_gut = sm_results['inv_alpha_gut']

    delta_required = INV_ALPHA_S_TARGET - inv_alpha_gut
    delta_ln_mu = np.log(M_P / M_GUT)

    b0_required = (2 * np.pi * delta_required) / delta_ln_mu

    return {
        'inv_alpha_gut': inv_alpha_gut,
        'inv_alpha_target': INV_ALPHA_S_TARGET,
        'delta_required': delta_required,
        'delta_ln_mu': delta_ln_mu,
        'b0_required': b0_required
    }

# =============================================================================
# E6 -> E8 Cascade Analysis
# =============================================================================

def cascade_running(m_e8, b0_e6=30, b0_e8=110):
    """
    Compute E6 -> E8 cascade running.

    Args:
        m_e8: Threshold where E6 -> E8 transition occurs
        b0_e6: Beta coefficient for E6 with matter
        b0_e8: Beta coefficient for pure E8

    Returns:
        Dictionary with running contributions
    """
    # E6 running: M_GUT -> M_E8
    delta_e6 = (b0_e6 / (2 * np.pi)) * np.log(m_e8 / M_GUT)

    # E8 running: M_E8 -> M_P
    delta_e8 = (b0_e8 / (2 * np.pi)) * np.log(M_P / m_e8)

    # Total
    delta_total = delta_e6 + delta_e8

    return {
        'm_e8': m_e8,
        'delta_e6': delta_e6,
        'delta_e8': delta_e8,
        'delta_total': delta_total
    }

def find_optimal_m_e8(delta_target, b0_e6=30, b0_e8=110):
    """
    Analytically find the optimal M_E8 that achieves the target running.

    Solving: delta_total = delta_target
    where delta_total = (b0_e6/2pi)*ln(M_E8/M_GUT) + (b0_e8/2pi)*ln(M_P/M_E8)

    Let x = ln(M_E8/M_GUT), then ln(M_P/M_E8) = ln(M_P/M_GUT) - x

    (b0_e6/2pi)*x + (b0_e8/2pi)*(L - x) = delta_target
    where L = ln(M_P/M_GUT)

    x*(b0_e6 - b0_e8)/2pi = delta_target - b0_e8*L/2pi
    x = (2pi*delta_target - b0_e8*L) / (b0_e6 - b0_e8)
    """
    L = np.log(M_P / M_GUT)
    x = (2 * np.pi * delta_target - b0_e8 * L) / (b0_e6 - b0_e8)
    m_e8_optimal = M_GUT * np.exp(x)

    return m_e8_optimal

def scan_m_e8_thresholds():
    """Scan different M_E8 thresholds and compute running."""
    required = compute_required_b0()
    delta_target = required['delta_required']

    # Log-spaced scan from M_GUT to M_P
    m_e8_values = np.logspace(np.log10(M_GUT) + 0.5, np.log10(M_P) - 0.1, 100)

    results = []
    for m_e8 in m_e8_values:
        cascade = cascade_running(m_e8)
        match_fraction = cascade['delta_total'] / delta_target
        results.append({
            'm_e8': m_e8,
            'delta_e6': cascade['delta_e6'],
            'delta_e8': cascade['delta_e8'],
            'delta_total': cascade['delta_total'],
            'match_fraction': match_fraction
        })

    return results

# =============================================================================
# Verification Checks
# =============================================================================

def verify_proposition():
    """Run all verification checks and print results."""
    print("=" * 80)
    print("VERIFICATION OF PROPOSITION 2.4.2")
    print("Pre-Geometric Beta-Function from Unified Gauge Groups")
    print("=" * 80)

    # 1. Beta function coefficients
    print("\n1. BETA FUNCTION COEFFICIENTS")
    print("-" * 60)
    b0_results = compute_all_b0()
    print(f"{'Group':<10} {'C_A':<6} {'b0(gauge)':<12} {'b0(ferm)':<12} {'b0(Higgs)':<12} {'b0(total)':<10}")
    print("-" * 60)
    for group, data in b0_results.items():
        print(f"{group:<10} {data['C_A']:<6} {data['b0_gauge']:<12.2f} {data['b0_ferm']:<12.2f} {data['b0_higgs']:<12.2f} {data['b0_total']:<10.2f}")

    # Document values
    print("\nDocument values (for comparison):")
    doc_values = {'SU5': 8.50, 'SO10': 18.67, 'E6': 30.00, 'E8_pure': 110}
    for group, doc_b0 in doc_values.items():
        calc_b0 = b0_results[group]['b0_total']
        match = "MATCH" if abs(calc_b0 - doc_b0) < 0.1 else "MISMATCH"
        print(f"  {group}: Document = {doc_b0:.2f}, Calculated = {calc_b0:.2f} [{match}]")

    # 2. SM Running
    print("\n2. STANDARD MODEL RUNNING (M_Z -> M_GUT)")
    print("-" * 60)
    sm = compute_sm_running()
    print(f"  1/alpha_s(M_Z) = {sm['inv_alpha_mz']:.2f}")
    print(f"  b0_QCD = {sm['b0_qcd']:.1f}")
    print(f"  Delta(1/alpha) = (b0/2pi) * ln(M_GUT/M_Z)")
    print(f"                 = ({sm['b0_qcd']:.1f}/(2pi)) * ln({M_GUT:.2e}/{M_Z:.2f})")
    print(f"                 = {sm['delta_inv_alpha']:.2f}")
    print(f"  1/alpha_s(M_GUT) = {sm['inv_alpha_gut']:.2f}")
    print(f"  Document value: 44.5 [{'MATCH' if abs(sm['inv_alpha_gut'] - 44.5) < 0.5 else 'MISMATCH'}]")

    # 3. CG Framework target
    print("\n3. CG FRAMEWORK TARGET")
    print("-" * 60)
    print(f"  1/alpha_s^geom(M_P) = (N_c^2 - 1)^2 = 64")
    print(f"  theta_O = arccos(-1/3) = {np.degrees(THETA_O):.4f} deg")
    print(f"  theta_T = arccos(1/3) = {np.degrees(THETA_T):.4f} deg")
    print(f"  Scheme factor = theta_O/theta_T = {SCHEME_FACTOR:.5f}")
    print(f"  1/alpha_s^MS-bar(M_P) = 64 * {SCHEME_FACTOR:.5f} = {INV_ALPHA_S_TARGET:.2f}")

    # 4. Required b0
    print("\n4. REQUIRED PRE-GEOMETRIC BETA FUNCTION")
    print("-" * 60)
    req = compute_required_b0()
    print(f"  Delta(1/alpha) required = {req['inv_alpha_target']:.2f} - {req['inv_alpha_gut']:.2f} = {req['delta_required']:.2f}")
    print(f"  Delta(ln mu) = ln(M_P/M_GUT) = ln({M_P:.2e}/{M_GUT:.2e}) = {req['delta_ln_mu']:.3f}")
    print(f"  b0_required = 2pi * {req['delta_required']:.2f} / {req['delta_ln_mu']:.3f} = {req['b0_required']:.2f}")
    print(f"  Document value: 48.5 [{'MATCH' if abs(req['b0_required'] - 48.5) < 0.5 else 'MISMATCH'}]")

    # 5. Fraction provided by each group
    print("\n5. FRACTION OF REQUIRED b0 BY UNIFIED GROUPS")
    print("-" * 60)
    b0_req = req['b0_required']
    for group in ['SU5', 'SO10', 'E6']:
        b0_group = b0_results[group]['b0_total']
        frac = b0_group / b0_req * 100
        print(f"  {group}: b0 = {b0_group:.2f}, Fraction = {frac:.1f}%")
    print(f"\n  CONCLUSION: Even E6 provides only {b0_results['E6']['b0_total']/b0_req*100:.0f}% of required running")

    # 6. E6 -> E8 Cascade
    print("\n6. E6 -> E8 CASCADE UNIFICATION")
    print("-" * 60)

    # Document value
    m_e8_doc = 2.3e18
    cascade_doc = cascade_running(m_e8_doc)
    print(f"  Document M_E8 = {m_e8_doc:.2e} GeV")
    print(f"    E6 running (M_GUT -> M_E8): Delta(1/alpha) = {cascade_doc['delta_e6']:.2f}")
    print(f"    E8 running (M_E8 -> M_P):   Delta(1/alpha) = {cascade_doc['delta_e8']:.2f}")
    print(f"    Total:                      Delta(1/alpha) = {cascade_doc['delta_total']:.2f}")
    print(f"    Required:                   Delta(1/alpha) = {req['delta_required']:.2f}")
    print(f"    Match: {cascade_doc['delta_total']/req['delta_required']*100:.1f}%")

    # Optimal M_E8
    m_e8_opt = find_optimal_m_e8(req['delta_required'])
    cascade_opt = cascade_running(m_e8_opt)
    print(f"\n  Optimal M_E8 (analytical) = {m_e8_opt:.3e} GeV")
    print(f"    E6 contribution: {cascade_opt['delta_e6']:.2f}")
    print(f"    E8 contribution: {cascade_opt['delta_e8']:.2f}")
    print(f"    Total: {cascade_opt['delta_total']:.2f} (Target: {req['delta_required']:.2f})")
    print(f"    Match: {cascade_opt['delta_total']/req['delta_required']*100:.2f}%")

    # 7. Summary
    print("\n" + "=" * 80)
    print("VERIFICATION SUMMARY")
    print("=" * 80)
    checks = [
        ("b0(SU5) = 8.50", abs(b0_results['SU5']['b0_total'] - 8.50) < 0.1),
        ("b0(SO10) = 18.67", abs(b0_results['SO10']['b0_total'] - 18.67) < 0.1),
        ("b0(E6) = 30.00", abs(b0_results['E6']['b0_total'] - 30.00) < 0.1),
        ("b0(E8 pure) = 110", abs(b0_results['E8_pure']['b0_total'] - 110) < 0.1),
        ("1/alpha_s(M_GUT) ~ 44.5", abs(sm['inv_alpha_gut'] - 44.5) < 1.0),
        ("b0_required ~ 48.5", abs(req['b0_required'] - 48.5) < 1.0),
        ("E6->E8 cascade provides ~100% required running", abs(cascade_doc['delta_total']/req['delta_required'] - 1.0) < 0.02),
    ]

    for desc, passed in checks:
        status = "PASS" if passed else "FAIL"
        print(f"  [{status}] {desc}")

    all_passed = all(passed for _, passed in checks)
    print(f"\n  OVERALL: {'ALL CHECKS PASSED' if all_passed else 'SOME CHECKS FAILED'}")

    return b0_results, sm, req, cascade_doc

# =============================================================================
# Plotting Functions
# =============================================================================

def plot_cascade_running():
    """Plot the E6 -> E8 cascade running."""
    req = compute_required_b0()
    delta_target = req['delta_required']

    # Scan thresholds
    results = scan_m_e8_thresholds()
    m_e8_values = [r['m_e8'] for r in results]
    delta_totals = [r['delta_total'] for r in results]

    # Optimal threshold
    m_e8_opt = find_optimal_m_e8(delta_target)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Plot 1: Delta(1/alpha) vs M_E8
    ax1.plot(m_e8_values, delta_totals, 'b-', linewidth=2, label='E6 → E8 cascade')
    ax1.axhline(y=delta_target, color='r', linestyle='--', linewidth=1.5, label=f'Target: {delta_target:.2f}')
    ax1.axvline(x=m_e8_opt, color='g', linestyle=':', linewidth=1.5, label=f'Optimal M_E8: {m_e8_opt:.2e} GeV')
    ax1.axvline(x=2.3e18, color='purple', linestyle='-.', linewidth=1.5, label=f'Document M_E8: 2.3×10¹⁸ GeV')
    ax1.set_xscale('log')
    ax1.set_xlabel('M_E8 (GeV)', fontsize=12)
    ax1.set_ylabel('Δ(1/α)', fontsize=12)
    ax1.set_title('E6 → E8 Cascade: Running vs Threshold', fontsize=14)
    ax1.legend(loc='best')
    ax1.grid(True, alpha=0.3)

    # Plot 2: Full running from M_Z to M_P
    mu_values = np.logspace(np.log10(M_Z), np.log10(M_P), 500)
    inv_alpha_sm = []
    inv_alpha_cascade = []

    for mu in mu_values:
        if mu < M_GUT:
            # SM running
            inv_a = one_loop_running(1/ALPHA_S_MZ, 7.0, M_Z, mu)
        else:
            # First run SM to M_GUT
            inv_a_gut = one_loop_running(1/ALPHA_S_MZ, 7.0, M_Z, M_GUT)
            inv_a = inv_a_gut
        inv_alpha_sm.append(inv_a)

        # Cascade
        if mu < M_GUT:
            inv_a = one_loop_running(1/ALPHA_S_MZ, 7.0, M_Z, mu)
        elif mu < m_e8_opt:
            inv_a_gut = one_loop_running(1/ALPHA_S_MZ, 7.0, M_Z, M_GUT)
            inv_a = one_loop_running(inv_a_gut, 30, M_GUT, mu)
        else:
            inv_a_gut = one_loop_running(1/ALPHA_S_MZ, 7.0, M_Z, M_GUT)
            inv_a_e8 = one_loop_running(inv_a_gut, 30, M_GUT, m_e8_opt)
            inv_a = one_loop_running(inv_a_e8, 110, m_e8_opt, mu)
        inv_alpha_cascade.append(inv_a)

    ax2.plot(mu_values, inv_alpha_sm, 'b--', linewidth=1.5, label='SM running only')
    ax2.plot(mu_values, inv_alpha_cascade, 'g-', linewidth=2, label='SM + E6 → E8 cascade')
    ax2.axhline(y=INV_ALPHA_S_TARGET, color='r', linestyle='--', linewidth=1.5, label=f'CG target: {INV_ALPHA_S_TARGET:.2f}')
    ax2.axvline(x=M_GUT, color='gray', linestyle=':', alpha=0.5, label='M_GUT')
    ax2.axvline(x=m_e8_opt, color='orange', linestyle=':', alpha=0.5, label='M_E8')
    ax2.axvline(x=M_P, color='purple', linestyle=':', alpha=0.5, label='M_P')
    ax2.set_xscale('log')
    ax2.set_xlabel('μ (GeV)', fontsize=12)
    ax2.set_ylabel('1/α_s', fontsize=12)
    ax2.set_title('Running of Strong Coupling: SM vs Cascade', fontsize=14)
    ax2.legend(loc='upper left')
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(M_Z, 2*M_P)

    plt.tight_layout()
    plt.savefig(PLOTS_DIR / 'proposition_2_4_2_cascade_verification.png', dpi=150)
    print(f"\nPlot saved to: {PLOTS_DIR / 'proposition_2_4_2_cascade_verification.png'}")
    plt.close()

def plot_group_comparison():
    """Plot comparison of different unified groups."""
    req = compute_required_b0()
    b0_required = req['b0_required']

    groups = ['SU(5)', 'SO(10)', 'E₆', 'E₈ (pure)', 'Required']
    b0_values = [8.5, 18.67, 30.0, 110.0, b0_required]
    colors = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd']

    fig, ax = plt.subplots(figsize=(10, 6))

    bars = ax.bar(groups, b0_values, color=colors, edgecolor='black', linewidth=1.5)

    # Add fraction labels on bars
    for i, (bar, b0) in enumerate(zip(bars, b0_values)):
        if groups[i] != 'Required':
            frac = b0 / b0_required * 100
            ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 2,
                   f'{frac:.0f}%', ha='center', va='bottom', fontsize=11, fontweight='bold')

    ax.axhline(y=b0_required, color='red', linestyle='--', linewidth=2, label=f'Required b₀ = {b0_required:.1f}')

    ax.set_ylabel('β-function coefficient b₀', fontsize=12)
    ax.set_title('Comparison of Unified Group β-Functions\n(Proposition 2.4.2)', fontsize=14)
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3, axis='y')

    # Annotate that E8 exceeds required
    ax.annotate('E₈ alone exceeds required,\nbut needs cascade at M_E8 < M_P',
               xy=(3, 110), xytext=(2.5, 85),
               arrowprops=dict(arrowstyle='->', color='gray'),
               fontsize=10, ha='center')

    plt.tight_layout()
    plt.savefig(PLOTS_DIR / 'proposition_2_4_2_group_comparison.png', dpi=150)
    print(f"Plot saved to: {PLOTS_DIR / 'proposition_2_4_2_group_comparison.png'}")
    plt.close()

# =============================================================================
# Main
# =============================================================================

if __name__ == "__main__":
    # Run verification
    b0_results, sm, req, cascade = verify_proposition()

    # Generate plots
    print("\nGenerating verification plots...")
    plot_cascade_running()
    plot_group_comparison()

    print("\nVerification complete.")
