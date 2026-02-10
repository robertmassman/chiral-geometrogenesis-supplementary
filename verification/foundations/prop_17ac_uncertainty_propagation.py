#!/usr/bin/env python3
"""
Uncertainty propagation of α_s(M_Z) through 1-loop QCD running to Planck scale.

Computes 1/α_s(M_P) with proper threshold matching at m_c, m_b, m_t.

QCD 1-loop running:
    1/α_s(μ₂) = 1/α_s(μ₁) + β₀/(2π) × ln(μ₂/μ₁)

where β₀ = (11·N_c - 2·N_f) / 3 for SU(N_c).

Author: Verification script for Proposition 0.0.17ac
Date: 2026-02-08
"""

import numpy as np

# ============================================================
# Physical constants and thresholds
# ============================================================
M_Z = 91.1876       # GeV, Z boson mass
M_P = 1.22e19       # GeV, Planck mass
m_c = 1.27          # GeV, charm quark mass (PDG)
m_b = 4.18          # GeV, bottom quark mass (PDG)
m_t = 172.76        # GeV, top quark mass (PDG)
N_c = 3             # Number of colors for SU(3)

# α_s(M_Z) values
alpha_s_central = 0.1180
alpha_s_upper   = 0.1189
alpha_s_lower   = 0.1171


def beta0(N_f):
    """1-loop β₀ coefficient: β₀ = (11·N_c - 2·N_f) / 3"""
    return (11 * N_c - 2 * N_f) / 3.0


def run_alpha_s_up(alpha_s_start, mu_start, mu_end, N_f):
    """
    Run α_s from mu_start to mu_end (upward) at fixed N_f.

    1-loop formula:
        1/α_s(μ₂) = 1/α_s(μ₁) + β₀/(2π) × ln(μ₂/μ₁)

    Returns α_s(mu_end).
    """
    b0 = beta0(N_f)
    inv_alpha_start = 1.0 / alpha_s_start
    inv_alpha_end = inv_alpha_start + b0 / (2.0 * np.pi) * np.log(mu_end / mu_start)
    return 1.0 / inv_alpha_end


def run_alpha_s_down(alpha_s_start, mu_start, mu_end, N_f):
    """
    Run α_s from mu_start DOWN to mu_end at fixed N_f.

    Same formula, just mu_end < mu_start so the log is negative.

    Returns α_s(mu_end).
    """
    b0 = beta0(N_f)
    inv_alpha_start = 1.0 / alpha_s_start
    inv_alpha_end = inv_alpha_start + b0 / (2.0 * np.pi) * np.log(mu_end / mu_start)
    return 1.0 / inv_alpha_end


def run_up_to_planck(alpha_s_MZ):
    """
    Run α_s from M_Z up to M_P with proper threshold matching.

    Thresholds:
        M_Z → m_t   : N_f = 5  (b, s, d, u, c active; t decoupled)
        m_t → M_P    : N_f = 6  (all quarks active)

    Note: M_Z = 91.19 GeV is above m_b = 4.18 GeV and m_c = 1.27 GeV,
    so we only cross the top threshold going up.

    Returns (alpha_s_MP, inv_alpha_s_MP, details_dict).
    """
    details = {}

    # Step 1: M_Z → m_t with N_f = 5
    nf = 5
    b0 = beta0(nf)
    inv_alpha_MZ = 1.0 / alpha_s_MZ
    inv_alpha_mt = inv_alpha_MZ + b0 / (2.0 * np.pi) * np.log(m_t / M_Z)
    alpha_mt = 1.0 / inv_alpha_mt

    details['step1'] = {
        'range': f'M_Z ({M_Z} GeV) → m_t ({m_t} GeV)',
        'N_f': nf,
        'beta0': b0,
        'ln_ratio': np.log(m_t / M_Z),
        'delta_inv_alpha': b0 / (2.0 * np.pi) * np.log(m_t / M_Z),
        'inv_alpha_start': inv_alpha_MZ,
        'inv_alpha_end': inv_alpha_mt,
        'alpha_end': alpha_mt,
    }

    # Step 2: m_t → M_P with N_f = 6
    nf = 6
    b0 = beta0(nf)
    inv_alpha_MP = inv_alpha_mt + b0 / (2.0 * np.pi) * np.log(M_P / m_t)
    alpha_MP = 1.0 / inv_alpha_MP

    details['step2'] = {
        'range': f'm_t ({m_t} GeV) → M_P ({M_P:.2e} GeV)',
        'N_f': nf,
        'beta0': b0,
        'ln_ratio': np.log(M_P / m_t),
        'delta_inv_alpha': b0 / (2.0 * np.pi) * np.log(M_P / m_t),
        'inv_alpha_start': inv_alpha_mt,
        'inv_alpha_end': inv_alpha_MP,
        'alpha_end': alpha_MP,
    }

    return alpha_MP, inv_alpha_MP, details


def run_down_from_planck(inv_alpha_MP):
    """
    Run α_s from M_P down to M_Z with proper threshold matching.

    Thresholds:
        M_P → m_t    : N_f = 6
        m_t → M_Z    : N_f = 5

    Returns (alpha_s_MZ, details_dict).
    """
    details = {}

    # Step 1: M_P → m_t with N_f = 6
    nf = 6
    b0 = beta0(nf)
    inv_alpha_mt = inv_alpha_MP + b0 / (2.0 * np.pi) * np.log(m_t / M_P)
    alpha_mt = 1.0 / inv_alpha_mt

    details['step1'] = {
        'range': f'M_P ({M_P:.2e} GeV) → m_t ({m_t} GeV)',
        'N_f': nf,
        'beta0': b0,
        'ln_ratio': np.log(m_t / M_P),
        'delta_inv_alpha': b0 / (2.0 * np.pi) * np.log(m_t / M_P),
        'inv_alpha_start': inv_alpha_MP,
        'inv_alpha_end': inv_alpha_mt,
        'alpha_end': alpha_mt,
    }

    # Step 2: m_t → M_Z with N_f = 5
    nf = 5
    b0 = beta0(nf)
    inv_alpha_MZ = inv_alpha_mt + b0 / (2.0 * np.pi) * np.log(M_Z / m_t)
    alpha_MZ = 1.0 / inv_alpha_MZ

    details['step2'] = {
        'range': f'm_t ({m_t} GeV) → M_Z ({M_Z} GeV)',
        'N_f': nf,
        'beta0': b0,
        'ln_ratio': np.log(M_Z / m_t),
        'delta_inv_alpha': b0 / (2.0 * np.pi) * np.log(M_Z / m_t),
        'inv_alpha_start': inv_alpha_mt,
        'inv_alpha_end': inv_alpha_MZ,
        'alpha_end': alpha_MZ,
    }

    return alpha_MZ, details


def run_down_full(inv_alpha_MP):
    """
    Run α_s from M_P all the way down to low scales with full threshold matching.

    M_P → m_t (N_f=6) → m_b (N_f=5) → m_c (N_f=4) → 1 GeV (N_f=3)

    Returns (alpha_s_values_dict, details_dict).
    """
    results = {}

    # M_P → m_t with N_f = 6
    nf = 6
    b0 = beta0(nf)
    inv_alpha_mt = inv_alpha_MP + b0 / (2.0 * np.pi) * np.log(m_t / M_P)
    results['m_t'] = 1.0 / inv_alpha_mt

    # m_t → M_Z with N_f = 5
    nf = 5
    b0 = beta0(nf)
    inv_alpha_MZ = inv_alpha_mt + b0 / (2.0 * np.pi) * np.log(M_Z / m_t)
    results['M_Z'] = 1.0 / inv_alpha_MZ

    # m_t → m_b with N_f = 5
    inv_alpha_mb = inv_alpha_mt + b0 / (2.0 * np.pi) * np.log(m_b / m_t)
    results['m_b'] = 1.0 / inv_alpha_mb

    # m_b → m_c with N_f = 4
    nf = 4
    b0 = beta0(nf)
    inv_alpha_mc = inv_alpha_mb + b0 / (2.0 * np.pi) * np.log(m_c / m_b)
    results['m_c'] = 1.0 / inv_alpha_mc

    return results


# ============================================================
# Main computation
# ============================================================
def main():
    print("=" * 72)
    print("UNCERTAINTY PROPAGATION: α_s(M_Z) → 1/α_s(M_P)")
    print("1-loop QCD running with threshold matching")
    print("=" * 72)

    # -----------------------------------------------------------
    # Print β₀ values for each N_f
    # -----------------------------------------------------------
    print("\n--- β₀ coefficients ---")
    for nf in [3, 4, 5, 6]:
        b0 = beta0(nf)
        print(f"  N_f = {nf}: β₀ = (11×{N_c} - 2×{nf})/3 = {b0:.4f}")

    # -----------------------------------------------------------
    # Run up for central, upper, lower values
    # -----------------------------------------------------------
    print("\n" + "=" * 72)
    print("FORWARD RUNNING: M_Z → M_P")
    print("=" * 72)

    results = {}
    for label, alpha_val in [('central', alpha_s_central),
                              ('upper', alpha_s_upper),
                              ('lower', alpha_s_lower)]:
        alpha_MP, inv_alpha_MP, details = run_up_to_planck(alpha_val)
        results[label] = {
            'alpha_s_MZ': alpha_val,
            'inv_alpha_s_MZ': 1.0 / alpha_val,
            'alpha_s_MP': alpha_MP,
            'inv_alpha_s_MP': inv_alpha_MP,
            'details': details,
        }

    # Print detailed results for central value
    print(f"\n--- Central value: α_s(M_Z) = {alpha_s_central} ---")
    d = results['central']['details']
    for step_key in ['step1', 'step2']:
        s = d[step_key]
        print(f"\n  {s['range']}:")
        print(f"    N_f = {s['N_f']}, β₀ = {s['beta0']:.4f}")
        print(f"    ln(μ₂/μ₁) = {s['ln_ratio']:.6f}")
        print(f"    Δ(1/α_s) = β₀/(2π) × ln(μ₂/μ₁) = {s['delta_inv_alpha']:.6f}")
        print(f"    1/α_s: {s['inv_alpha_start']:.6f} → {s['inv_alpha_end']:.6f}")
        print(f"    α_s = {s['alpha_end']:.6f}")

    # -----------------------------------------------------------
    # Summary table
    # -----------------------------------------------------------
    print("\n" + "=" * 72)
    print("SUMMARY OF FORWARD RUNNING")
    print("=" * 72)

    print(f"\n{'Label':<10} {'α_s(M_Z)':<14} {'1/α_s(M_Z)':<14} {'1/α_s(M_P)':<14} {'α_s(M_P)':<14}")
    print("-" * 66)
    for label in ['lower', 'central', 'upper']:
        r = results[label]
        print(f"{label:<10} {r['alpha_s_MZ']:<14.4f} {r['inv_alpha_s_MZ']:<14.6f} "
              f"{r['inv_alpha_s_MP']:<14.6f} {r['alpha_s_MP']:<14.8f}")

    # -----------------------------------------------------------
    # Uncertainty calculation
    # -----------------------------------------------------------
    inv_central = results['central']['inv_alpha_s_MP']
    inv_upper_input = results['upper']['inv_alpha_s_MP']  # larger α_s → smaller 1/α_s
    inv_lower_input = results['lower']['inv_alpha_s_MP']  # smaller α_s → larger 1/α_s

    # Note: larger α_s(M_Z) gives SMALLER 1/α_s(M_P) (coupling runs slower from larger start)
    delta_up = inv_lower_input - inv_central    # This should be positive
    delta_down = inv_central - inv_upper_input  # This should be positive
    delta_symmetric = (delta_up + delta_down) / 2.0

    # Alternative: direct propagation from δα_s = 0.0009
    # δ(1/α_s) = δα_s / α_s² (at M_Z), propagated through running
    delta_alpha = 0.0009
    delta_inv_direct = delta_alpha / alpha_s_central**2

    print(f"\n--- Uncertainty in 1/α_s(M_P) ---")
    print(f"  Central: 1/α_s(M_P) = {inv_central:.4f}")
    print(f"  From α_s = {alpha_s_lower}: 1/α_s(M_P) = {inv_lower_input:.4f} (δ+ = +{delta_up:.4f})")
    print(f"  From α_s = {alpha_s_upper}: 1/α_s(M_P) = {inv_upper_input:.4f} (δ- = -{delta_down:.4f})")
    print(f"  Symmetric uncertainty: δ(1/α_s(M_P)) = ±{delta_symmetric:.4f}")
    print(f"  Relative uncertainty: {delta_symmetric/inv_central*100:.2f}%")
    print()
    print(f"  Cross-check via error propagation:")
    print(f"    δ(1/α_s(M_Z)) = δα_s / α_s² = {delta_alpha} / {alpha_s_central}² = {delta_inv_direct:.4f}")
    print(f"    (This is the input uncertainty; running preserves 1/α_s shifts additively)")
    print(f"    Since 1-loop: 1/α_s(M_P) = 1/α_s(M_Z) + Σ[β₀/(2π)·ln(μ₂/μ₁)]")
    print(f"    The running contribution is independent of α_s(M_Z)")
    print(f"    So: δ(1/α_s(M_P)) = δ(1/α_s(M_Z)) = {delta_inv_direct:.4f}")

    # -----------------------------------------------------------
    # Total running contribution breakdown
    # -----------------------------------------------------------
    d = results['central']['details']
    total_running = d['step1']['delta_inv_alpha'] + d['step2']['delta_inv_alpha']
    print(f"\n--- Running contribution breakdown ---")
    print(f"  M_Z → m_t (N_f=5): Δ(1/α_s) = +{d['step1']['delta_inv_alpha']:.4f}")
    print(f"  m_t → M_P (N_f=6): Δ(1/α_s) = +{d['step2']['delta_inv_alpha']:.4f}")
    print(f"  Total running:      Δ(1/α_s) = +{total_running:.4f}")
    print(f"  1/α_s(M_Z) = {results['central']['inv_alpha_s_MZ']:.4f}")
    print(f"  1/α_s(M_P) = {results['central']['inv_alpha_s_MZ']:.4f} + {total_running:.4f} = {inv_central:.4f}")

    # -----------------------------------------------------------
    # REVERSE CHECK: Start from 1/α_s(M_P) = 52, run down to M_Z
    # -----------------------------------------------------------
    print("\n" + "=" * 72)
    print("REVERSE CHECK: 1/α_s(M_P) = 52 → α_s(M_Z)")
    print("=" * 72)

    inv_alpha_MP_test = 52.0
    alpha_MZ_recovered, rev_details = run_down_from_planck(inv_alpha_MP_test)

    for step_key in ['step1', 'step2']:
        s = rev_details[step_key]
        print(f"\n  {s['range']}:")
        print(f"    N_f = {s['N_f']}, β₀ = {s['beta0']:.4f}")
        print(f"    ln(μ₂/μ₁) = {s['ln_ratio']:.6f}")
        print(f"    Δ(1/α_s) = β₀/(2π) × ln(μ₂/μ₁) = {s['delta_inv_alpha']:.6f}")
        print(f"    1/α_s: {s['inv_alpha_start']:.6f} → {s['inv_alpha_end']:.6f}")
        print(f"    α_s = {s['alpha_end']:.6f}")

    print(f"\n  RESULT: Starting from 1/α_s(M_P) = {inv_alpha_MP_test}")
    print(f"  → α_s(M_Z) = {alpha_MZ_recovered:.6f}")
    print(f"  → 1/α_s(M_Z) = {1.0/alpha_MZ_recovered:.4f}")
    print(f"  Compare with PDG: α_s(M_Z) = 0.1180 ± 0.0009")
    print(f"  Deviation: {(alpha_MZ_recovered - 0.1180)/0.0009:.2f}σ")

    # Also try reverse from our computed central value (should round-trip exactly)
    print(f"\n--- Round-trip check ---")
    alpha_MZ_roundtrip, _ = run_down_from_planck(inv_central)
    print(f"  Forward:  α_s(M_Z) = {alpha_s_central} → 1/α_s(M_P) = {inv_central:.6f}")
    print(f"  Reverse:  1/α_s(M_P) = {inv_central:.6f} → α_s(M_Z) = {alpha_MZ_roundtrip:.10f}")
    print(f"  Original: α_s(M_Z) = {alpha_s_central}")
    print(f"  Roundtrip error: {abs(alpha_MZ_roundtrip - alpha_s_central):.2e}")

    # -----------------------------------------------------------
    # Additional reverse checks at different 1/α_s(M_P) values
    # -----------------------------------------------------------
    print("\n" + "=" * 72)
    print("REVERSE RUNNING TABLE: 1/α_s(M_P) → α_s(M_Z)")
    print("=" * 72)

    test_values = [48, 49, 50, 51, 52, 53, 54, 55, 56]
    print(f"\n{'1/α_s(M_P)':<14} {'α_s(M_Z)':<14} {'1/α_s(M_Z)':<14} {'σ from PDG':<14}")
    print("-" * 56)
    for inv_val in test_values:
        a_MZ, _ = run_down_from_planck(float(inv_val))
        sigma = (a_MZ - 0.1180) / 0.0009
        print(f"{inv_val:<14} {a_MZ:<14.6f} {1.0/a_MZ:<14.4f} {sigma:+.2f}σ")

    # -----------------------------------------------------------
    # Formula for the proposition
    # -----------------------------------------------------------
    print("\n" + "=" * 72)
    print("FORMULA TEXT FOR PROPOSITION")
    print("=" * 72)

    print(f"""
At 1-loop with threshold matching at m_c, m_b, m_t:

  1/α_s(M_P) = 1/α_s(M_Z) + β₀⁽⁵⁾/(2π) · ln(m_t/M_Z) + β₀⁽⁶⁾/(2π) · ln(M_P/m_t)

where:
  β₀⁽⁵⁾ = (33 - 2×5)/3 = 23/3 ≈ 7.6667  (N_f = 5, M_Z < μ < m_t)
  β₀⁽⁶⁾ = (33 - 2×6)/3 = 21/3 = 7.0000  (N_f = 6, m_t < μ < M_P)

Numerically:
  1/α_s(M_Z) = 1/0.1180 = {1/0.1180:.4f}
  + β₀⁽⁵⁾/(2π) · ln(172.76/91.19) = {beta0(5)/(2*np.pi) * np.log(m_t/M_Z):.4f}
  + β₀⁽⁶⁾/(2π) · ln(1.22×10¹⁹/172.76) = {beta0(6)/(2*np.pi) * np.log(M_P/m_t):.4f}
  = {inv_central:.4f}

  ≈ {inv_central:.1f} ± {delta_symmetric:.1f}

Uncertainty propagation:
  δ(1/α_s(M_P)) = δα_s(M_Z) / α_s(M_Z)²
                 = 0.0009 / (0.1180)²
                 = {delta_inv_direct:.2f}

  (The running terms Σ β₀/(2π)·ln(μ₂/μ₁) are independent of α_s(M_Z),
   so the uncertainty propagates as a pure shift in 1/α_s.)

Result:
  1/α_s(M_P) = {inv_central:.1f} ± {delta_symmetric:.1f}  (1-loop, threshold-matched)
""")

    # -----------------------------------------------------------
    # Comparison with specific values used in Theorem 5.2.6
    # -----------------------------------------------------------
    print("=" * 72)
    print("COMPARISON WITH THEOREM 5.2.6 VALUE")
    print("=" * 72)

    # Check what α_s(M_P) ≈ 1/52 gives
    for target in [50, 51, 52, 53, 54]:
        a_MZ, _ = run_down_from_planck(float(target))
        print(f"  If 1/α_s(M_P) = {target}: α_s(M_Z) = {a_MZ:.4f} "
              f"({'✓ consistent' if abs(a_MZ - 0.1180) < 0.0009 else '✗ inconsistent'} "
              f"with PDG at 1σ)")

    print(f"\n  Our computed value: 1/α_s(M_P) = {inv_central:.2f}")
    print(f"  Nearest integer: {round(inv_central)}")
    print(f"  Using 1/α_s(M_P) ≈ {round(inv_central)} is {'justified' if abs(round(inv_central) - inv_central) < delta_symmetric else 'NOT justified'} within uncertainties")


if __name__ == '__main__':
    main()
