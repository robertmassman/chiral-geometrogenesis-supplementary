#!/usr/bin/env python3
"""
Two-Loop QCD Running: Robust Implementation

This script implements the exact two-loop QCD running with proper threshold matching,
following the methodology from two-loop-QCD-analysis.md.

Key Formula (Two-Loop Implicit Form):
    L = (1/(2b₀)) × [1/α_s(μ) - 1/α_s(μ₀)] + (b₁/(2b₀²)) × ln[α_s(μ)/α_s(μ₀)]

where L = ln(μ/μ₀)

Author: Multi-Agent Verification System
Date: 2025-12-14
"""

import numpy as np
from scipy.optimize import fsolve, brentq
import json
import warnings

# Suppress runtime warnings from fsolve
warnings.filterwarnings('ignore', category=RuntimeWarning)

# =============================================================================
# Physical Constants
# =============================================================================

M_P = 1.22e19      # Planck mass in GeV
M_Z = 91.1876      # Z boson mass in GeV (PDG 2024)
m_t = 172.69       # Top quark pole mass in GeV
m_b = 4.18         # Bottom quark MS-bar mass in GeV
m_c = 1.27         # Charm quark MS-bar mass in GeV

# Experimental value
ALPHA_S_MZ_EXP = 0.1179
ALPHA_S_MZ_ERR = 0.0010

# =============================================================================
# Beta Function Coefficients
# =============================================================================

def b0(N_f, N_c=3):
    """
    One-loop β-function coefficient.

    b₀ = (11N_c - 2N_f) / (12π)

    For SU(3):
        N_f=3: b₀ = 27/(12π) = 9/(4π) ≈ 0.7162
        N_f=4: b₀ = 25/(12π) ≈ 0.6631
        N_f=5: b₀ = 23/(12π) ≈ 0.6103
        N_f=6: b₀ = 21/(12π) = 7/(4π) ≈ 0.5570
    """
    return (11 * N_c - 2 * N_f) / (12 * np.pi)


def b1(N_f, N_c=3):
    """
    Two-loop β-function coefficient.

    b₁ = [34N_c²/3 - 10N_c·N_f/3 - (N_c² - 1)·N_f/N_c] / (16π²)

    For SU(3):
        N_f=3: b₁ = (102 - 38)/(16π²) = 64/(16π²) ≈ 0.4053
        N_f=4: b₁ ≈ 0.3258
        N_f=5: b₁ ≈ 0.2462
        N_f=6: b₁ ≈ 0.1651
    """
    term1 = 34 * N_c**2 / 3
    term2 = 10 * N_c * N_f / 3
    term3 = (N_c**2 - 1) * N_f / N_c
    return (term1 - term2 - term3) / (16 * np.pi**2)


def print_beta_coefficients():
    """Print β-function coefficients for reference."""
    print("\n" + "=" * 60)
    print("β-FUNCTION COEFFICIENTS")
    print("=" * 60)
    print(f"\n{'N_f':>4} {'b₀':>12} {'b₁':>12}")
    print("-" * 30)
    for nf in [3, 4, 5, 6]:
        print(f"{nf:>4} {b0(nf):>12.6f} {b1(nf):>12.6f}")


# =============================================================================
# Two-Loop Running Implementation
# =============================================================================

def RGE_2loop_equation(alpha_final, alpha_init, L, N_f):
    """
    Two-loop RGE implicit equation.

    The equation to solve is:
        L = (1/(2b₀)) × [1/α_s(μ) - 1/α_s(μ₀)] + (b₁/(2b₀²)) × ln[α_s(μ)/α_s(μ₀)]

    Returns: LHS - RHS (should be zero at solution)

    Args:
        alpha_final: α_s at final scale (unknown)
        alpha_init: α_s at initial scale (known)
        L: ln(μ_final / μ_init)
        N_f: number of active flavors
    """
    b0_val = b0(N_f)
    b1_val = b1(N_f)

    # Protect against invalid values
    if alpha_final <= 0 or alpha_init <= 0:
        return 1e10

    term1 = (1/alpha_final - 1/alpha_init) / (2 * b0_val)
    term2 = (b1_val / (2 * b0_val**2)) * np.log(alpha_final / alpha_init)

    return term1 + term2 - L


def run_2loop(alpha_init, mu_init, mu_final, N_f, verbose=False):
    """
    Run α_s from mu_init to mu_final using two-loop RGE.

    Uses scipy.optimize.fsolve for robust root finding.

    Args:
        alpha_init: α_s at initial scale
        mu_init: initial energy scale (GeV)
        mu_final: final energy scale (GeV)
        N_f: number of active flavors
        verbose: print intermediate results

    Returns:
        alpha_final: α_s at final scale
    """
    L = np.log(mu_final / mu_init)

    # Initial guess based on one-loop running
    b0_val = b0(N_f)
    denom = 1 + 2 * b0_val * alpha_init * L
    if denom > 0:
        alpha_guess = alpha_init / denom
    else:
        # Fallback guess
        alpha_guess = alpha_init * (1 - 2 * b0_val * alpha_init * L)

    # Ensure guess is positive
    alpha_guess = max(alpha_guess, 1e-6)

    # Solve for alpha_final
    try:
        result = fsolve(
            lambda a: RGE_2loop_equation(a[0], alpha_init, L, N_f),
            [alpha_guess],
            full_output=True
        )
        alpha_final = result[0][0]
        info = result[1]

        # Verify solution
        residual = abs(RGE_2loop_equation(alpha_final, alpha_init, L, N_f))

        if residual > 1e-6 or alpha_final <= 0:
            # Try Brent's method as fallback
            try:
                # Determine bracket based on running direction
                if mu_final < mu_init:  # Running DOWN → α increases
                    alpha_final = brentq(
                        lambda a: RGE_2loop_equation(a, alpha_init, L, N_f),
                        alpha_init * 0.5,
                        min(alpha_init * 100, 1.0)
                    )
                else:  # Running UP → α decreases
                    alpha_final = brentq(
                        lambda a: RGE_2loop_equation(a, alpha_init, L, N_f),
                        alpha_init * 0.01,
                        alpha_init * 1.5
                    )
            except ValueError:
                if verbose:
                    print(f"  Warning: Brent's method failed, using fsolve result")

        if verbose:
            direction = "DOWN" if mu_final < mu_init else "UP"
            print(f"  Running {direction}: {mu_init:.2e} → {mu_final:.2e} GeV (N_f={N_f})")
            print(f"    α_s: {alpha_init:.6f} → {alpha_final:.6f}")

        return alpha_final

    except Exception as e:
        print(f"  Error in two-loop running: {e}")
        # Return one-loop result as fallback
        return alpha_init / (1 + 2 * b0_val * alpha_init * L)


def run_with_thresholds_2loop(alpha_start, mu_start, mu_end, verbose=True):
    """
    Run α_s with proper flavor thresholds using two-loop RGE.

    CG Method: The sequence from two-loop-QCD-analysis.md is:
        M_P → m_t (N_f=6) → m_b (N_f=5) → m_c (N_f=4) → M_Z (N_f=3)

    Note: The last step (m_c → M_Z) runs UP in energy!

    Returns:
        (alpha_final, intermediate_values)
    """
    if verbose:
        print("\n" + "=" * 60)
        print("TWO-LOOP RUNNING WITH THRESHOLD MATCHING")
        print("=" * 60)
        print(f"\nStarting: α_s(M_P) = {alpha_start:.6f} = 1/{1/alpha_start:.0f}")

    results = {'stages': []}
    current_alpha = alpha_start

    # Stage 1: M_P → m_t (N_f = 6)
    if verbose:
        print("\n--- Stage 1: M_P → m_t (N_f = 6) ---")

    L1 = np.log(m_t / M_P)
    alpha_mt = run_2loop(current_alpha, M_P, m_t, N_f=6, verbose=verbose)
    results['stages'].append({
        'stage': 1,
        'from': 'M_P',
        'to': 'm_t',
        'N_f': 6,
        'L': L1,
        'alpha_init': current_alpha,
        'alpha_final': alpha_mt
    })
    current_alpha = alpha_mt

    # Stage 2: m_t → m_b (N_f = 5)
    if verbose:
        print("\n--- Stage 2: m_t → m_b (N_f = 5) ---")

    L2 = np.log(m_b / m_t)
    alpha_mb = run_2loop(current_alpha, m_t, m_b, N_f=5, verbose=verbose)
    results['stages'].append({
        'stage': 2,
        'from': 'm_t',
        'to': 'm_b',
        'N_f': 5,
        'L': L2,
        'alpha_init': current_alpha,
        'alpha_final': alpha_mb
    })
    current_alpha = alpha_mb

    # Stage 3: m_b → m_c (N_f = 4)
    if verbose:
        print("\n--- Stage 3: m_b → m_c (N_f = 4) ---")

    L3 = np.log(m_c / m_b)
    alpha_mc = run_2loop(current_alpha, m_b, m_c, N_f=4, verbose=verbose)
    results['stages'].append({
        'stage': 3,
        'from': 'm_b',
        'to': 'm_c',
        'N_f': 4,
        'L': L3,
        'alpha_init': current_alpha,
        'alpha_final': alpha_mc
    })
    current_alpha = alpha_mc

    # Stage 4: m_c → M_Z (N_f = 3) - Note: this runs UP!
    if verbose:
        print("\n--- Stage 4: m_c → M_Z (N_f = 3) [Running UP] ---")

    L4 = np.log(M_Z / m_c)
    alpha_mz = run_2loop(current_alpha, m_c, M_Z, N_f=3, verbose=verbose)
    results['stages'].append({
        'stage': 4,
        'from': 'm_c',
        'to': 'M_Z',
        'N_f': 3,
        'L': L4,
        'alpha_init': current_alpha,
        'alpha_final': alpha_mz
    })

    results['alpha_final'] = alpha_mz
    results['alpha_mt'] = alpha_mt
    results['alpha_mb'] = alpha_mb
    results['alpha_mc'] = alpha_mc

    return alpha_mz, results


def run_standard_thresholds_2loop(alpha_start, mu_start, mu_end, verbose=True):
    """
    Run α_s with STANDARD threshold ordering (no backtracking).

    Standard Method:
        M_P → m_t (N_f=6) → M_Z (N_f=5)

    Note: M_Z is between m_t and m_b, so N_f=5 at M_Z.
    """
    if verbose:
        print("\n" + "=" * 60)
        print("STANDARD TWO-LOOP RUNNING (N_f=5 at M_Z)")
        print("=" * 60)
        print(f"\nStarting: α_s(M_P) = {alpha_start:.6f} = 1/{1/alpha_start:.0f}")

    current_alpha = alpha_start

    # Stage 1: M_P → m_t (N_f = 6)
    if verbose:
        print("\n--- Stage 1: M_P → m_t (N_f = 6) ---")
    alpha_mt = run_2loop(current_alpha, M_P, m_t, N_f=6, verbose=verbose)
    current_alpha = alpha_mt

    # Stage 2: m_t → M_Z (N_f = 5)
    if verbose:
        print("\n--- Stage 2: m_t → M_Z (N_f = 5) ---")
    alpha_mz = run_2loop(current_alpha, m_t, M_Z, N_f=5, verbose=verbose)

    return alpha_mz, {'alpha_mt': alpha_mt, 'alpha_mz': alpha_mz}


# =============================================================================
# Reverse Running
# =============================================================================

def reverse_run_2loop(alpha_mz, verbose=True):
    """
    Run BACKWARDS from M_Z to M_P to find required α_s(M_P).

    Uses the CG threshold sequence in reverse:
        M_Z → m_c (N_f=3) → m_b (N_f=4) → m_t (N_f=5) → M_P (N_f=6)
    """
    if verbose:
        print("\n" + "=" * 60)
        print("REVERSE RUNNING: M_Z → M_P")
        print("=" * 60)
        print(f"\nStarting: α_s(M_Z) = {alpha_mz:.6f}")

    current_alpha = alpha_mz

    # Stage 1: M_Z → m_c (N_f = 3) - Running DOWN
    if verbose:
        print("\n--- Stage 1: M_Z → m_c (N_f = 3) [Running DOWN] ---")
    alpha_mc = run_2loop(current_alpha, M_Z, m_c, N_f=3, verbose=verbose)
    current_alpha = alpha_mc

    # Stage 2: m_c → m_b (N_f = 4) - Running UP
    if verbose:
        print("\n--- Stage 2: m_c → m_b (N_f = 4) [Running UP] ---")
    alpha_mb = run_2loop(current_alpha, m_c, m_b, N_f=4, verbose=verbose)
    current_alpha = alpha_mb

    # Stage 3: m_b → m_t (N_f = 5) - Running UP
    if verbose:
        print("\n--- Stage 3: m_b → m_t (N_f = 5) [Running UP] ---")
    alpha_mt = run_2loop(current_alpha, m_b, m_t, N_f=5, verbose=verbose)
    current_alpha = alpha_mt

    # Stage 4: m_t → M_P (N_f = 6) - Running UP
    if verbose:
        print("\n--- Stage 4: m_t → M_P (N_f = 6) [Running UP] ---")
    alpha_mp = run_2loop(current_alpha, m_t, M_P, N_f=6, verbose=verbose)

    return alpha_mp


# =============================================================================
# Main Analysis
# =============================================================================

def main():
    print("=" * 70)
    print("TWO-LOOP QCD RUNNING: ROBUST IMPLEMENTATION")
    print("=" * 70)

    print_beta_coefficients()

    alpha_s_MP = 1/64  # CG prediction

    # =========================================================================
    # Test 1: CG Method (with N_f=3 at M_Z)
    # =========================================================================

    alpha_mz_cg, results_cg = run_with_thresholds_2loop(alpha_s_MP, M_P, M_Z, verbose=True)
    error_cg = abs(alpha_mz_cg - ALPHA_S_MZ_EXP) / ALPHA_S_MZ_EXP * 100

    print("\n" + "-" * 60)
    print("CG METHOD RESULT")
    print("-" * 60)
    print(f"α_s(M_P) = {alpha_s_MP:.6f} = 1/64")
    print(f"α_s(m_t) = {results_cg['alpha_mt']:.6f}")
    print(f"α_s(m_b) = {results_cg['alpha_mb']:.6f}")
    print(f"α_s(m_c) = {results_cg['alpha_mc']:.6f}")
    print(f"α_s(M_Z) = {alpha_mz_cg:.6f}")
    print(f"")
    print(f"Experimental: α_s(M_Z) = {ALPHA_S_MZ_EXP} ± {ALPHA_S_MZ_ERR}")
    print(f"Error: {error_cg:.2f}%")

    # Compare with claimed values from two-loop-QCD-analysis.md
    print("\n" + "-" * 60)
    print("COMPARISON WITH CLAIMED VALUES")
    print("-" * 60)
    claimed = {
        'alpha_mt': 0.01076,
        'alpha_mb': 0.0163,
        'alpha_mc': 0.0216,
        'alpha_mz': 0.1187
    }
    print(f"{'Scale':<8} {'Calculated':<12} {'Claimed':<12} {'Diff %':<10}")
    print("-" * 45)
    print(f"{'m_t':<8} {results_cg['alpha_mt']:<12.6f} {claimed['alpha_mt']:<12.6f} {100*abs(results_cg['alpha_mt']-claimed['alpha_mt'])/claimed['alpha_mt']:.2f}%")
    print(f"{'m_b':<8} {results_cg['alpha_mb']:<12.6f} {claimed['alpha_mb']:<12.6f} {100*abs(results_cg['alpha_mb']-claimed['alpha_mb'])/claimed['alpha_mb']:.2f}%")
    print(f"{'m_c':<8} {results_cg['alpha_mc']:<12.6f} {claimed['alpha_mc']:<12.6f} {100*abs(results_cg['alpha_mc']-claimed['alpha_mc'])/claimed['alpha_mc']:.2f}%")
    print(f"{'M_Z':<8} {alpha_mz_cg:<12.6f} {claimed['alpha_mz']:<12.6f} {100*abs(alpha_mz_cg-claimed['alpha_mz'])/claimed['alpha_mz']:.2f}%")

    # =========================================================================
    # Test 2: Standard Method (N_f=5 at M_Z)
    # =========================================================================

    alpha_mz_std, results_std = run_standard_thresholds_2loop(alpha_s_MP, M_P, M_Z, verbose=True)
    error_std = abs(alpha_mz_std - ALPHA_S_MZ_EXP) / ALPHA_S_MZ_EXP * 100

    print("\n" + "-" * 60)
    print("STANDARD METHOD RESULT")
    print("-" * 60)
    print(f"α_s(M_Z) = {alpha_mz_std:.6f}")
    print(f"Error: {error_std:.2f}%")

    # =========================================================================
    # Test 3: Reverse Running
    # =========================================================================

    alpha_mp_needed = reverse_run_2loop(ALPHA_S_MZ_EXP, verbose=True)

    print("\n" + "-" * 60)
    print("REVERSE RUNNING RESULT")
    print("-" * 60)
    print(f"To match α_s(M_Z) = {ALPHA_S_MZ_EXP}:")
    print(f"  Required: α_s(M_P) = {alpha_mp_needed:.6f}")
    print(f"  Required: 1/α_s(M_P) = {1/alpha_mp_needed:.2f}")
    print(f"")
    print(f"CG predicts: 1/α_s(M_P) = 64")
    print(f"Discrepancy: {abs(64 - 1/alpha_mp_needed):.2f} ({abs(64 - 1/alpha_mp_needed)/64*100:.1f}%)")

    # =========================================================================
    # Summary
    # =========================================================================

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"""
Starting Point: α_s(M_P) = 1/64 = 0.015625

Method 1: CG Threshold Sequence (M_P → m_t → m_b → m_c → M_Z)
  - Uses N_f = 3 at M_Z (non-standard)
  - α_s(M_Z) = {alpha_mz_cg:.6f}
  - Error vs experiment: {error_cg:.2f}%

Method 2: Standard Sequence (M_P → m_t → M_Z)
  - Uses N_f = 5 at M_Z (standard)
  - α_s(M_Z) = {alpha_mz_std:.6f}
  - Error vs experiment: {error_std:.2f}%

Reverse Running (from experimental α_s(M_Z)):
  - Required: 1/α_s(M_P) = {1/alpha_mp_needed:.2f}
  - CG predicts: 1/α_s(M_P) = 64
  - Discrepancy: {abs(64 - 1/alpha_mp_needed)/64*100:.1f}%

Experimental Reference:
  - α_s(M_Z) = {ALPHA_S_MZ_EXP} ± {ALPHA_S_MZ_ERR} (PDG 2024)
""")

    # =========================================================================
    # Save Results
    # =========================================================================

    output = {
        'input': {
            'alpha_s_MP': alpha_s_MP,
            'one_over_alpha_s_MP': 64,
            'M_P_GeV': M_P,
            'M_Z_GeV': M_Z,
            'm_t_GeV': m_t,
            'm_b_GeV': m_b,
            'm_c_GeV': m_c
        },
        'cg_method': {
            'description': 'M_P → m_t (N_f=6) → m_b (N_f=5) → m_c (N_f=4) → M_Z (N_f=3)',
            'intermediate_values': {
                'alpha_mt': float(results_cg['alpha_mt']),
                'alpha_mb': float(results_cg['alpha_mb']),
                'alpha_mc': float(results_cg['alpha_mc'])
            },
            'alpha_s_MZ': float(alpha_mz_cg),
            'error_percent': float(error_cg)
        },
        'standard_method': {
            'description': 'M_P → m_t (N_f=6) → M_Z (N_f=5)',
            'alpha_s_MZ': float(alpha_mz_std),
            'error_percent': float(error_std)
        },
        'reverse_running': {
            'alpha_s_MZ_input': ALPHA_S_MZ_EXP,
            'alpha_s_MP_required': float(alpha_mp_needed),
            'one_over_alpha_s_MP_required': float(1/alpha_mp_needed),
            'discrepancy_from_64': float(abs(64 - 1/alpha_mp_needed)),
            'discrepancy_percent': float(abs(64 - 1/alpha_mp_needed)/64*100)
        },
        'experimental': {
            'alpha_s_MZ': ALPHA_S_MZ_EXP,
            'uncertainty': ALPHA_S_MZ_ERR,
            'source': 'PDG 2024'
        },
        'claimed_values_from_doc': {
            'alpha_mt': 0.01076,
            'alpha_mb': 0.0163,
            'alpha_mc': 0.0216,
            'alpha_mz': 0.1187,
            'error_percent': 0.7
        }
    }

    with open('verification/qcd_running_two_loop_robust_results.json', 'w') as f:
        json.dump(output, f, indent=2)

    print("Results saved to: verification/qcd_running_two_loop_robust_results.json")

    return output


if __name__ == "__main__":
    results = main()
