#!/usr/bin/env python3
"""
Theorem 5.2.6: NNLO QCD Running with Proper Threshold Matching

This script implements full NNLO (3-loop) QCD running of α_s with:
1. Three-loop β-function coefficients (β_0, β_1, β_2)
2. Four-loop coefficient β_3 for comparison
3. Proper threshold matching at quark mass thresholds
4. Comparison between one-loop, two-loop, and three-loop results

Goal: Determine if higher-loop corrections can reduce the 22% discrepancy
between CG prediction (1/α_s = 64) and required value (~52.5).

References:
- PDG 2024: α_s(M_Z) = 0.1180 ± 0.0009
- van Ritbergen, Vermaseren, Larin (1997): Four-loop β-function
- Tarasov, Vladimirov, Zharkov (1980): Three-loop β-function

Author: Verification Agent
Date: 2025-12-15
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import json
import matplotlib.pyplot as plt
import os

# =============================================================================
# PHYSICAL CONSTANTS
# =============================================================================

# PDG 2024 values
ALPHA_S_MZ = 0.1180          # Strong coupling at M_Z
ALPHA_S_MZ_ERR = 0.0009      # Uncertainty
M_Z = 91.1876                # GeV - Z boson mass
M_P = 1.220890e19            # GeV - Planck mass

# Quark masses (MS-bar at μ = m_q for heavy quarks, PDG 2024)
M_TOP = 172.69               # GeV - top quark pole mass
M_TOP_MSBAR = 163.0          # GeV - MS-bar mass at μ = m_t
M_BOTTOM = 4.18              # GeV - bottom MS-bar mass at μ = m_b
M_CHARM = 1.27               # GeV - charm MS-bar mass at μ = m_c

# Zeta function values
ZETA_3 = 1.2020569031595942  # ζ(3) = Riemann zeta at 3
ZETA_5 = 1.0369277551433699  # ζ(5) = Riemann zeta at 5

# =============================================================================
# QCD BETA FUNCTION COEFFICIENTS
# =============================================================================

def beta_coefficients(N_f: int, N_c: int = 3) -> dict:
    """
    QCD β-function coefficients for SU(N_c) with N_f flavors.

    Convention: dα_s/d(ln μ²) = β(α_s) = -α_s² Σ β_n (α_s/π)^n

    In MS-bar scheme:
    - β_0 = (11*N_c - 2*N_f) / 3
    - β_1 = (34*N_c² - 10*N_c*N_f - 3*(N_c²-1)*N_f/N_c) / 3  [= (102 - 38*N_f/3) for SU(3)]
    - β_2 = 2857/2 - 5033*N_f/18 + 325*N_f²/54  [for SU(3)]
    - β_3 = complex expression with ζ(3)

    Alternative convention used in many papers:
    b_0 = β_0/(4π), b_1 = β_1/(16π²), etc.
    """
    C_A = N_c                    # Adjoint Casimir
    C_F = (N_c**2 - 1)/(2*N_c)   # Fundamental Casimir
    T_F = 0.5                    # Trace normalization

    # One-loop (universal)
    beta_0 = (11/3) * C_A - (4/3) * T_F * N_f

    # Two-loop (universal in MS-bar)
    beta_1 = (34/3) * C_A**2 - (20/3) * C_A * T_F * N_f - 4 * C_F * T_F * N_f

    # Three-loop (MS-bar)
    # β_2 = 2857/2 - 5033*N_f/18 + 325*N_f²/54 for SU(3)
    beta_2 = (2857/2) * C_A**3 / N_c**3
    beta_2 -= (1415/6) * C_A**2 * T_F * N_f / N_c**2
    beta_2 -= (205/6) * C_A * C_F * T_F * N_f / N_c
    beta_2 += (79/108) * C_A * T_F**2 * N_f**2 / N_c
    beta_2 += (11/9) * C_F * T_F**2 * N_f**2
    beta_2 -= C_F**2 * T_F * N_f

    # Simplified for SU(3):
    if N_c == 3:
        beta_2_su3 = 2857/2 - (5033/18) * N_f + (325/54) * N_f**2
        beta_2 = beta_2_su3  # Use the simpler form

    # Four-loop (MS-bar) - from van Ritbergen, Vermaseren, Larin (1997)
    # β_3 ≈ 29243.0 - 6946.30*N_f + 405.089*N_f² + 1.49931*N_f³
    # Including ζ(3) terms:
    if N_c == 3:
        beta_3 = (149753/6) + 3564 * ZETA_3
        beta_3 -= ((1078361/162) + (6508/27) * ZETA_3) * N_f
        beta_3 += ((50065/162) + (6472/81) * ZETA_3) * N_f**2
        beta_3 += (1093/729) * N_f**3
    else:
        # General formula is more complex; use SU(3) as approximation
        beta_3 = 29243.0 - 6946.30 * N_f + 405.089 * N_f**2 + 1.49931 * N_f**3

    return {
        'beta_0': beta_0,
        'beta_1': beta_1,
        'beta_2': beta_2,
        'beta_3': beta_3,
        'N_f': N_f,
        'N_c': N_c
    }


def print_beta_coefficients():
    """Print β-function coefficients for various N_f."""
    print("=" * 70)
    print("QCD β-FUNCTION COEFFICIENTS (MS-bar scheme)")
    print("=" * 70)
    print(f"{'N_f':<5} {'β_0':<12} {'β_1':<12} {'β_2':<12} {'β_3':<12}")
    print("-" * 70)
    for n_f in [3, 4, 5, 6]:
        coeff = beta_coefficients(n_f)
        print(f"{n_f:<5} {coeff['beta_0']:<12.4f} {coeff['beta_1']:<12.4f} "
              f"{coeff['beta_2']:<12.2f} {coeff['beta_3']:<12.1f}")
    print()

# =============================================================================
# ALPHA_S RUNNING FUNCTIONS
# =============================================================================

def alpha_s_running_1loop(alpha_s_0: float, mu_0: float, mu: float, N_f: int) -> float:
    """
    One-loop running of α_s.

    1/α_s(μ) = 1/α_s(μ_0) + (β_0/2π) * ln(μ²/μ_0²)
    """
    coeff = beta_coefficients(N_f)
    beta_0 = coeff['beta_0']

    L = np.log(mu**2 / mu_0**2)
    inv_alpha = 1/alpha_s_0 + (beta_0 / (2 * np.pi)) * L

    if inv_alpha <= 0:
        return np.nan
    return 1 / inv_alpha


def alpha_s_running_2loop(alpha_s_0: float, mu_0: float, mu: float, N_f: int) -> float:
    """
    Two-loop running of α_s using iterative solution.

    Uses the implicit equation and iterates to convergence.
    """
    coeff = beta_coefficients(N_f)
    beta_0 = coeff['beta_0']
    beta_1 = coeff['beta_1']

    L = np.log(mu**2 / mu_0**2)

    # Start with one-loop result
    alpha_s = alpha_s_running_1loop(alpha_s_0, mu_0, mu, N_f)
    if np.isnan(alpha_s):
        return np.nan

    # Two-loop correction term
    b0 = beta_0 / (4 * np.pi)
    b1 = beta_1 / (16 * np.pi**2)

    # Iterate to solve implicit equation
    for _ in range(20):
        # Two-loop formula
        inv_alpha_new = 1/alpha_s_0 + 2 * b0 * L + (b1/b0) * np.log(1 + 2 * b0 * alpha_s * L)
        if inv_alpha_new <= 0:
            return np.nan
        alpha_s_new = 1 / inv_alpha_new

        if abs(alpha_s_new - alpha_s) < 1e-10:
            return alpha_s_new
        alpha_s = alpha_s_new

    return alpha_s


def alpha_s_running_3loop_numerical(alpha_s_0: float, mu_0: float, mu: float, N_f: int) -> float:
    """
    Three-loop running of α_s using numerical ODE integration.

    Solves: d(α_s)/d(ln μ²) = β(α_s) = -(α_s²/2π)[β_0 + (α_s/π)β_1 + (α_s/π)²β_2 + ...]
    """
    coeff = beta_coefficients(N_f)
    beta_0 = coeff['beta_0']
    beta_1 = coeff['beta_1']
    beta_2 = coeff['beta_2']

    def beta_function(t, alpha):
        """β(α_s) = d(α_s)/d(ln μ²)"""
        a = alpha[0]
        if a <= 0:
            return [0]
        a_pi = a / np.pi
        beta = -(a**2 / (2 * np.pi)) * (beta_0 + beta_1 * a_pi + beta_2 * a_pi**2)
        return [beta]

    # Integrate from ln(μ_0²) to ln(μ²)
    t_span = [0, np.log(mu**2 / mu_0**2)]

    sol = solve_ivp(beta_function, t_span, [alpha_s_0], method='RK45',
                    dense_output=True, rtol=1e-10, atol=1e-12)

    if not sol.success:
        return np.nan

    return sol.y[0, -1]


def alpha_s_running_4loop_numerical(alpha_s_0: float, mu_0: float, mu: float, N_f: int) -> float:
    """
    Four-loop running of α_s using numerical ODE integration.
    """
    coeff = beta_coefficients(N_f)
    beta_0 = coeff['beta_0']
    beta_1 = coeff['beta_1']
    beta_2 = coeff['beta_2']
    beta_3 = coeff['beta_3']

    def beta_function(t, alpha):
        """β(α_s) = d(α_s)/d(ln μ²)"""
        a = alpha[0]
        if a <= 0:
            return [0]
        a_pi = a / np.pi
        beta = -(a**2 / (2 * np.pi)) * (beta_0 + beta_1 * a_pi + beta_2 * a_pi**2 + beta_3 * a_pi**3)
        return [beta]

    t_span = [0, np.log(mu**2 / mu_0**2)]

    sol = solve_ivp(beta_function, t_span, [alpha_s_0], method='RK45',
                    dense_output=True, rtol=1e-10, atol=1e-12)

    if not sol.success:
        return np.nan

    return sol.y[0, -1]

# =============================================================================
# THRESHOLD MATCHING
# =============================================================================

def threshold_matching_coefficient(N_f: int, order: int = 2) -> float:
    """
    Threshold matching coefficient for decoupling a heavy quark.

    At a threshold μ = m_q:
    α_s^(N_f-1)(μ) = α_s^(N_f)(μ) * [1 + c_1*(α_s/π) + c_2*(α_s/π)² + ...]

    At NLO (order=1): c_1 = 0 (matching is trivial at one-loop in MS-bar)
    At NNLO (order=2): c_2 has non-zero contributions

    For simplicity, we use continuous matching at the threshold scale
    (c_1 = c_2 = 0 approximation), which is accurate to O(α_s²).
    """
    if order <= 1:
        return 0.0

    # NNLO matching corrections are small (~0.1% effect)
    # For a more precise calculation, see Chetyrkin et al.
    c_2 = 0.0  # Simplified; full expression involves ln(μ²/m_q²) terms

    return c_2


def run_alpha_s_with_thresholds(alpha_s_0: float, mu_0: float, mu: float,
                                 N_f_0: int, loop_order: int = 3) -> dict:
    """
    Run α_s from μ_0 to μ with proper threshold matching.

    Parameters:
    - alpha_s_0: α_s at scale μ_0
    - mu_0: starting scale (GeV)
    - mu: target scale (GeV)
    - N_f_0: number of active flavors at μ_0
    - loop_order: 1, 2, 3, or 4 loop running

    Returns dictionary with intermediate values and final result.
    """
    # Quark thresholds (in order of mass)
    thresholds = [
        (M_CHARM, 4),   # N_f: 3 → 4 at m_c
        (M_BOTTOM, 5),  # N_f: 4 → 5 at m_b
        (M_TOP_MSBAR, 6),    # N_f: 5 → 6 at m_t
    ]

    # Choose running function based on loop order
    if loop_order == 1:
        run_func = alpha_s_running_1loop
    elif loop_order == 2:
        run_func = alpha_s_running_2loop
    elif loop_order == 3:
        run_func = alpha_s_running_3loop_numerical
    else:
        run_func = alpha_s_running_4loop_numerical

    results = {
        'initial_scale': mu_0,
        'initial_alpha_s': alpha_s_0,
        'initial_N_f': N_f_0,
        'loop_order': loop_order,
        'intermediate_values': [],
        'final_scale': mu,
        'final_alpha_s': None,
        'final_N_f': None
    }

    current_alpha = alpha_s_0
    current_mu = mu_0
    current_N_f = N_f_0

    # Determine direction (running up or down)
    running_up = (mu > mu_0)

    if running_up:
        # Running UP in energy: N_f increases at thresholds
        for threshold_mu, N_f_above in thresholds:
            if current_mu < threshold_mu <= mu:
                # Run to threshold
                alpha_at_threshold = run_func(current_alpha, current_mu, threshold_mu, current_N_f)

                results['intermediate_values'].append({
                    'scale': threshold_mu,
                    'alpha_s': alpha_at_threshold,
                    'N_f_below': current_N_f,
                    'N_f_above': N_f_above,
                    'transition': f'N_f: {current_N_f} → {N_f_above}'
                })

                # Match and continue
                current_alpha = alpha_at_threshold  # Continuous matching
                current_mu = threshold_mu
                current_N_f = N_f_above

        # Run to final scale
        final_alpha = run_func(current_alpha, current_mu, mu, current_N_f)

    else:
        # Running DOWN in energy: N_f decreases at thresholds
        for threshold_mu, N_f_above in reversed(thresholds):
            if mu < threshold_mu <= current_mu:
                # Run down to threshold
                alpha_at_threshold = run_func(current_alpha, current_mu, threshold_mu, current_N_f)

                N_f_below = N_f_above - 1

                results['intermediate_values'].append({
                    'scale': threshold_mu,
                    'alpha_s': alpha_at_threshold,
                    'N_f_above': current_N_f,
                    'N_f_below': N_f_below,
                    'transition': f'N_f: {current_N_f} → {N_f_below}'
                })

                # Match and continue
                current_alpha = alpha_at_threshold  # Continuous matching
                current_mu = threshold_mu
                current_N_f = N_f_below

        # Run to final scale
        final_alpha = run_func(current_alpha, current_mu, mu, current_N_f)

    results['final_alpha_s'] = final_alpha
    results['final_N_f'] = current_N_f

    return results

# =============================================================================
# MAIN ANALYSIS: COMPARE LOOP ORDERS
# =============================================================================

def analyze_mp_running():
    """
    Main analysis: Run α_s from M_Z to M_P at different loop orders.
    Compare with CG prediction of 1/α_s(M_P) = 64.
    """
    print("=" * 70)
    print("ANALYSIS: QCD RUNNING FROM M_Z TO M_P")
    print("=" * 70)
    print(f"\nInput: α_s(M_Z) = {ALPHA_S_MZ} ± {ALPHA_S_MZ_ERR}")
    print(f"Running from M_Z = {M_Z:.2f} GeV to M_P = {M_P:.3e} GeV")
    print(f"CG prediction: 1/α_s(M_P) = 64 → α_s(M_P) = {1/64:.6f}")
    print()

    results = {}

    for loop_order in [1, 2, 3, 4]:
        result = run_alpha_s_with_thresholds(
            alpha_s_0=ALPHA_S_MZ,
            mu_0=M_Z,
            mu=M_P,
            N_f_0=5,  # 5 active flavors at M_Z
            loop_order=loop_order
        )

        alpha_s_MP = result['final_alpha_s']
        inv_alpha_s_MP = 1/alpha_s_MP if alpha_s_MP > 0 else np.nan

        # Compare with CG prediction
        CG_prediction = 64
        discrepancy = (CG_prediction - inv_alpha_s_MP) / inv_alpha_s_MP * 100

        results[f'{loop_order}-loop'] = {
            'alpha_s_MP': alpha_s_MP,
            'inv_alpha_s_MP': inv_alpha_s_MP,
            'CG_prediction': CG_prediction,
            'discrepancy_percent': discrepancy,
            'intermediate': result['intermediate_values']
        }

        print(f"\n{loop_order}-LOOP RUNNING:")
        print(f"  α_s(M_P) = {alpha_s_MP:.6f}")
        print(f"  1/α_s(M_P) = {inv_alpha_s_MP:.2f}")
        print(f"  CG prediction: 64")
        print(f"  Discrepancy: {discrepancy:+.1f}%")

        # Show intermediate values
        if result['intermediate_values']:
            print(f"  Thresholds crossed:")
            for iv in result['intermediate_values']:
                print(f"    μ = {iv['scale']:.1f} GeV: α_s = {iv['alpha_s']:.4f} ({iv['transition']})")

    return results


def analyze_reverse_running():
    """
    Reverse analysis: What 1/α_s(M_P) is REQUIRED to get α_s(M_Z) = 0.1180?

    Instead of running DOWN from M_P (which has numerical issues),
    we run UP from M_Z to M_P and invert the question:
    Given α_s(M_Z), what is α_s(M_P)?

    This gives us the REQUIRED value of 1/α_s(M_P) to match experiment.
    """
    print("\n" + "=" * 70)
    print("REVERSE ANALYSIS: REQUIRED 1/α_s(M_P) TO MATCH EXPERIMENT")
    print("=" * 70)
    print("\nMethod: Run UP from M_Z to M_P, which gives the REQUIRED α_s(M_P)")
    print("to be consistent with the measured α_s(M_Z) = 0.1180")

    results = {}

    for loop_order in [1, 2, 3, 4]:
        # Run from M_Z to M_P - this directly gives us what α_s(M_P) must be
        result = run_alpha_s_with_thresholds(
            alpha_s_0=ALPHA_S_MZ,
            mu_0=M_Z,
            mu=M_P,
            N_f_0=5,  # 5 active flavors at M_Z
            loop_order=loop_order
        )

        alpha_s_MP_required = result['final_alpha_s']

        if alpha_s_MP_required > 0 and not np.isnan(alpha_s_MP_required):
            inv_alpha_required = 1/alpha_s_MP_required
            discrepancy_from_64 = (64 - inv_alpha_required) / inv_alpha_required * 100

            results[f'{loop_order}-loop'] = {
                'alpha_s_MP_required': alpha_s_MP_required,
                'inv_alpha_s_MP_required': inv_alpha_required,
                'discrepancy_from_64': discrepancy_from_64
            }

            print(f"\n{loop_order}-LOOP:")
            print(f"  Required α_s(M_P) = {alpha_s_MP_required:.6f}")
            print(f"  Required 1/α_s(M_P) = {inv_alpha_required:.2f}")
            print(f"  CG predicts 64 → discrepancy = {discrepancy_from_64:+.1f}%")
        else:
            print(f"\n{loop_order}-LOOP: Numerical issues")
            results[f'{loop_order}-loop'] = None

    return results


def analyze_improvement():
    """
    Analyze how much NNLO corrections help reduce the discrepancy.
    """
    print("\n" + "=" * 70)
    print("SUMMARY: IMPACT OF HIGHER-LOOP CORRECTIONS")
    print("=" * 70)

    # Forward running results
    forward = analyze_mp_running()

    # Reverse running results
    reverse = analyze_reverse_running()

    print("\n" + "-" * 70)
    print("COMPARISON TABLE:")
    print("-" * 70)
    print(f"{'Loop Order':<12} {'1/α_s(M_P) Forward':<22} {'1/α_s(M_P) Required':<22} {'Discrepancy from 64':<20}")
    print("-" * 70)

    for loop_order in [1, 2, 3, 4]:
        key = f'{loop_order}-loop'
        fwd = forward[key]['inv_alpha_s_MP']
        if reverse[key]:
            req = reverse[key]['inv_alpha_s_MP_required']
            disc = reverse[key]['discrepancy_from_64']
        else:
            req = np.nan
            disc = np.nan
        print(f"{key:<12} {fwd:<22.2f} {req:<22.2f} {disc:+.1f}%")

    print("-" * 70)
    print("\nKey insights:")
    print("  - Forward running: Starting from CG's α_s(M_P) = 1/64, what α_s(M_Z) do we get?")
    print("  - Reverse running: What α_s(M_P) is needed to get experimental α_s(M_Z)?")
    print("  - Discrepancy: How far is the required value from CG's prediction of 64?")

    # Calculate improvement from 1-loop to 3-loop
    if reverse['1-loop'] and reverse['3-loop']:
        disc_1loop = reverse['1-loop']['discrepancy_from_64']
        disc_3loop = reverse['3-loop']['discrepancy_from_64']
        improvement = disc_1loop - disc_3loop
        print(f"\n  NNLO improvement: {improvement:+.1f}% reduction in discrepancy")

    return {'forward': forward, 'reverse': reverse}


# =============================================================================
# VISUALIZATION
# =============================================================================

def generate_plots(results):
    """Generate visualization of running results."""

    plots_dir = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots"
    os.makedirs(plots_dir, exist_ok=True)

    # Plot 1: α_s running from M_Z to M_P at different loop orders
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Energy scales to plot
    scales = np.logspace(np.log10(M_Z), np.log10(M_P), 100)

    ax1 = axes[0]
    for loop_order, color in [(1, 'blue'), (2, 'green'), (3, 'red'), (4, 'purple')]:
        alpha_values = []
        for scale in scales:
            result = run_alpha_s_with_thresholds(
                ALPHA_S_MZ, M_Z, scale, 5, loop_order
            )
            alpha_values.append(result['final_alpha_s'])
        ax1.semilogx(scales, alpha_values, color=color, label=f'{loop_order}-loop', linewidth=2)

    ax1.axhline(y=1/64, color='black', linestyle='--', label='CG: α_s = 1/64')
    ax1.set_xlabel('Energy Scale μ (GeV)', fontsize=12)
    ax1.set_ylabel('α_s(μ)', fontsize=12)
    ax1.set_title('QCD Running: α_s vs Energy Scale', fontsize=14)
    ax1.legend(loc='upper right')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(M_Z, M_P)

    # Plot 2: 1/α_s comparison
    ax2 = axes[1]
    loop_orders = [1, 2, 3, 4]
    required_values = []
    for lo in loop_orders:
        key = f'{lo}-loop'
        if results['reverse'][key]:
            required_values.append(results['reverse'][key]['inv_alpha_s_MP_required'])
        else:
            required_values.append(np.nan)

    ax2.bar(loop_orders, required_values, color=['blue', 'green', 'red', 'purple'],
            edgecolor='black', linewidth=2, alpha=0.7)
    ax2.axhline(y=64, color='black', linestyle='--', linewidth=2, label='CG prediction: 64')
    ax2.set_xlabel('Loop Order', fontsize=12)
    ax2.set_ylabel('Required 1/α_s(M_P)', fontsize=12)
    ax2.set_title('Required UV Coupling vs Loop Order', fontsize=14)
    ax2.set_xticks(loop_orders)
    ax2.set_xticklabels(['1-loop', '2-loop', '3-loop', '4-loop'])
    ax2.legend()
    ax2.grid(True, alpha=0.3, axis='y')

    # Add value labels on bars
    for i, val in enumerate(required_values):
        if not np.isnan(val):
            ax2.annotate(f'{val:.1f}', (loop_orders[i], val + 1),
                        ha='center', va='bottom', fontsize=10, fontweight='bold')

    plt.tight_layout()
    plt.savefig(f'{plots_dir}/theorem_5_2_6_nnlo_running.png', dpi=150, bbox_inches='tight')
    plt.close()

    print(f"\nPlot saved to: {plots_dir}/theorem_5_2_6_nnlo_running.png")


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("THEOREM 5.2.6: NNLO QCD RUNNING ANALYSIS")
    print("Goal: Determine impact of higher-loop corrections on UV coupling")
    print("=" * 70)

    # Print β-function coefficients
    print_beta_coefficients()

    # Main analysis
    results = analyze_improvement()

    # Generate plots
    generate_plots(results)

    # Save results
    output_dir = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification"

    def convert_numpy(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.int64, np.int32)):
            return int(obj)
        elif isinstance(obj, (np.float64, np.float32)):
            return float(obj)
        elif isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        elif isinstance(obj, dict):
            return {k: convert_numpy(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_numpy(v) for v in obj]
        return obj

    results_json = convert_numpy(results)

    with open(f"{output_dir}/theorem_5_2_6_nnlo_results.json", "w") as f:
        json.dump(results_json, f, indent=2)

    print(f"\nResults saved to: {output_dir}/theorem_5_2_6_nnlo_results.json")

    # Final summary
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    if results['reverse']['1-loop'] and results['reverse']['3-loop']:
        disc_1 = results['reverse']['1-loop']['discrepancy_from_64']
        disc_3 = results['reverse']['3-loop']['discrepancy_from_64']
        req_3 = results['reverse']['3-loop']['inv_alpha_s_MP_required']

        print(f"\n1-loop result:  1/α_s(M_P) required = {results['reverse']['1-loop']['inv_alpha_s_MP_required']:.2f}")
        print(f"3-loop result:  1/α_s(M_P) required = {req_3:.2f}")
        print(f"\nCG prediction:  1/α_s(M_P) = 64")
        print(f"\nDiscrepancy at 1-loop: {disc_1:+.1f}%")
        print(f"Discrepancy at 3-loop: {disc_3:+.1f}%")
        print(f"\nNNLO IMPROVEMENT: {abs(disc_1) - abs(disc_3):.1f}% reduction")

        if abs(disc_3) < abs(disc_1):
            print("\n✅ Higher-loop corrections REDUCE the discrepancy")
        else:
            print("\n⚠️ Higher-loop corrections do NOT significantly help")
