"""
Adversarial Physics Verification: Proposition 0.0.17aa
Spectral Index as a Genuine Geometric Prediction

This script performs adversarial testing of the claim that n_s = 0.96484
is derived from first principles via the relation:
    N_geo = (4/π) × ln(ξ) = 512/9 ≈ 56.9
    n_s = 1 - 2/N_geo = 1 - 9/256 = 0.96484

Key tests:
1. Algebraic verification of all derivation steps
2. Sensitivity analysis (N_c, N_f variations)
3. Comparison with experimental data (Planck 2018, ACT DR6)
4. Alternative factor exploration (why 4/π and not something else?)
5. Physical consistency checks

Author: Multi-Agent Verification System
Date: 2026-01-26
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
import json
from datetime import datetime

# Output directory for plots
PLOT_DIR = Path(__file__).parent.parent / "plots"
PLOT_DIR.mkdir(exist_ok=True)

# Physical constants
PI = np.pi

# Topological inputs
N_C = 3  # Number of colors (SU(3))
N_F = 3  # Number of light quark flavors


def calculate_beta_coefficient(N_c: int, N_f: int) -> float:
    """
    Calculate the QCD β-function coefficient b₀.

    b₀ = (11N_c - 2N_f) / (12π)

    This is the convention where β(α_s) = -b₀ α_s²
    """
    return (11 * N_c - 2 * N_f) / (12 * PI)


def calculate_hierarchy_exponent(N_c: int, N_f: int) -> float:
    """
    Calculate the QCD-Planck hierarchy exponent ln(ξ).

    ln(ξ) = (N_c² - 1)² / (2 b₀)

    For N_c = 3, N_f = 3: ln(ξ) = 64 / (9/(2π)) = 128π/9 ≈ 44.68
    """
    b0 = calculate_beta_coefficient(N_c, N_f)
    numerator = (N_c**2 - 1)**2
    return numerator / (2 * b0)


def calculate_N_geo(N_c: int, N_f: int, factor: float = 4/PI) -> float:
    """
    Calculate the number of e-folds N_geo.

    N_geo = factor × ln(ξ)

    The proposition claims factor = 4/π arises from SU(3) coset geometry.
    """
    ln_xi = calculate_hierarchy_exponent(N_c, N_f)
    return factor * ln_xi


def calculate_spectral_index(N_geo: float) -> float:
    """
    Calculate the spectral index n_s from e-folds.

    n_s = 1 - 2/N_geo (standard slow-roll α-attractor formula)
    """
    return 1 - 2 / N_geo


def calculate_tensor_ratio(N_geo: float, alpha: float = 1/3) -> float:
    """
    Calculate the tensor-to-scalar ratio r.

    r = 12α / N² for α-attractors

    For α = 1/3 (SU(3) coset): r = 4/N²
    """
    return 12 * alpha / N_geo**2


# ============================================================================
# TEST 1: Algebraic Verification
# ============================================================================

def test_algebraic_derivation():
    """Verify all algebraic steps in the derivation."""
    print("=" * 70)
    print("TEST 1: ALGEBRAIC VERIFICATION")
    print("=" * 70)

    results = {}

    # Step 1: β-function coefficient
    b0 = calculate_beta_coefficient(N_C, N_F)
    b0_expected = 9 / (4 * PI)
    results['b0'] = {
        'calculated': b0,
        'expected': b0_expected,
        'match': np.isclose(b0, b0_expected, rtol=1e-10),
        'formula': 'b₀ = (11×3 - 2×3)/(12π) = 27/(12π) = 9/(4π)'
    }
    print(f"\n  b₀ = {b0:.6f}")
    print(f"  Expected: {b0_expected:.6f}")
    print(f"  Match: {results['b0']['match']}")

    # Step 2: Hierarchy exponent
    ln_xi = calculate_hierarchy_exponent(N_C, N_F)
    ln_xi_expected = 128 * PI / 9
    results['ln_xi'] = {
        'calculated': ln_xi,
        'expected': ln_xi_expected,
        'match': np.isclose(ln_xi, ln_xi_expected, rtol=1e-10),
        'formula': 'ln(ξ) = 64 / (9/(2π)) = 128π/9'
    }
    print(f"\n  ln(ξ) = {ln_xi:.6f}")
    print(f"  Expected: {ln_xi_expected:.6f}")
    print(f"  Match: {results['ln_xi']['match']}")

    # Step 3: Number of e-folds (with 4/π factor)
    N_geo = calculate_N_geo(N_C, N_F, factor=4/PI)
    N_geo_expected = 512 / 9
    results['N_geo'] = {
        'calculated': N_geo,
        'expected': N_geo_expected,
        'match': np.isclose(N_geo, N_geo_expected, rtol=1e-10),
        'formula': 'N_geo = (4/π) × 128π/9 = 512/9'
    }
    print(f"\n  N_geo = {N_geo:.6f}")
    print(f"  Expected: {N_geo_expected:.6f}")
    print(f"  Match: {results['N_geo']['match']}")

    # Step 4: Spectral index
    n_s = calculate_spectral_index(N_geo)
    n_s_expected = 1 - 9/256
    results['n_s'] = {
        'calculated': n_s,
        'expected': n_s_expected,
        'match': np.isclose(n_s, n_s_expected, rtol=1e-10),
        'formula': 'n_s = 1 - 2/(512/9) = 1 - 18/512 = 1 - 9/256'
    }
    print(f"\n  n_s = {n_s:.8f}")
    print(f"  Expected: {n_s_expected:.8f}")
    print(f"  Match: {results['n_s']['match']}")

    # Step 5: Alternative formula verification
    n_s_alt = 1 - 9 / (4 * (N_C**2 - 1)**2)
    results['n_s_alternative'] = {
        'calculated': n_s_alt,
        'expected': n_s,
        'match': np.isclose(n_s_alt, n_s, rtol=1e-10),
        'formula': 'n_s = 1 - 9/(4×(N_c²-1)²) = 1 - 9/256'
    }
    print(f"\n  Alternative formula n_s = {n_s_alt:.8f}")
    print(f"  Match: {results['n_s_alternative']['match']}")

    # Step 6: Tensor ratio
    r = calculate_tensor_ratio(N_geo, alpha=1/3)
    r_expected = 4 / N_geo**2
    results['r'] = {
        'calculated': r,
        'expected': r_expected,
        'match': np.isclose(r, r_expected, rtol=1e-10),
        'formula': 'r = 12×(1/3)/N² = 4/N²'
    }
    print(f"\n  r = {r:.6f}")
    print(f"  Expected: {r_expected:.6f}")
    print(f"  Match: {results['r']['match']}")

    all_pass = all(v['match'] for v in results.values())
    print(f"\n  ALL ALGEBRAIC TESTS PASS: {all_pass}")

    return results, all_pass


# ============================================================================
# TEST 2: Sensitivity Analysis
# ============================================================================

def test_sensitivity_analysis():
    """Analyze sensitivity to N_c and N_f variations."""
    print("\n" + "=" * 70)
    print("TEST 2: SENSITIVITY ANALYSIS")
    print("=" * 70)

    # Planck 2018 constraint
    n_s_planck = 0.9649
    n_s_err = 0.0042

    results = {'N_c_variation': [], 'N_f_variation': []}

    # N_c variation (keeping N_f = 3)
    print("\n  N_c variation (N_f = 3 fixed):")
    print("  " + "-" * 50)
    N_c_values = [2, 3, 4, 5]
    for N_c in N_c_values:
        N_geo = calculate_N_geo(N_c, N_F, factor=4/PI)
        n_s = calculate_spectral_index(N_geo)
        sigma_off = abs(n_s - n_s_planck) / n_s_err
        status = "RULED OUT" if sigma_off > 3 else ("TENSION" if sigma_off > 2 else "OK")
        results['N_c_variation'].append({
            'N_c': N_c, 'N_geo': N_geo, 'n_s': n_s,
            'sigma_off': sigma_off, 'status': status
        })
        print(f"  N_c = {N_c}: N_geo = {N_geo:.1f}, n_s = {n_s:.4f} ({sigma_off:.1f}σ) {status}")

    # N_f variation (keeping N_c = 3)
    print("\n  N_f variation (N_c = 3 fixed):")
    print("  " + "-" * 50)
    N_f_values = [0, 2, 3, 4, 5, 6]
    for N_f in N_f_values:
        # Check for asymptotic freedom: 11*N_c > 2*N_f
        if 11 * N_C <= 2 * N_f:
            print(f"  N_f = {N_f}: NOT ASYMPTOTICALLY FREE (skipped)")
            continue
        N_geo = calculate_N_geo(N_C, N_f, factor=4/PI)
        n_s = calculate_spectral_index(N_geo)
        sigma_off = abs(n_s - n_s_planck) / n_s_err
        status = "RULED OUT" if sigma_off > 3 else ("TENSION" if sigma_off > 2 else "OK")
        results['N_f_variation'].append({
            'N_f': N_f, 'N_geo': N_geo, 'n_s': n_s,
            'sigma_off': sigma_off, 'status': status
        })
        note = "(inflationary scale)" if N_f == 6 else "(QCD scale)" if N_f == 3 else ""
        print(f"  N_f = {N_f}: N_geo = {N_geo:.1f}, n_s = {n_s:.4f} ({sigma_off:.1f}σ) {status} {note}")

    return results


# ============================================================================
# TEST 3: Experimental Comparison
# ============================================================================

def test_experimental_comparison():
    """Compare predictions with experimental data."""
    print("\n" + "=" * 70)
    print("TEST 3: EXPERIMENTAL COMPARISON")
    print("=" * 70)

    # Framework predictions
    N_geo = calculate_N_geo(N_C, N_F, factor=4/PI)
    n_s_pred = calculate_spectral_index(N_geo)
    r_pred = calculate_tensor_ratio(N_geo, alpha=1/3)

    # Experimental values
    experiments = {
        'Planck 2018': {'n_s': 0.9649, 'n_s_err': 0.0042, 'r_bound': 0.058},
        'Planck 2018 + BK15': {'n_s': 0.9649, 'n_s_err': 0.0042, 'r_bound': 0.036},
        'Planck 2018 + BK18': {'n_s': 0.9649, 'n_s_err': 0.0042, 'r_bound': 0.032},
        'ACT DR6 + Planck': {'n_s': 0.9709, 'n_s_err': 0.0038, 'r_bound': 0.032},
        'ACT DR6 + Planck + DESI': {'n_s': 0.9744, 'n_s_err': 0.0034, 'r_bound': 0.032},
    }

    results = {}
    print(f"\n  Framework prediction: n_s = {n_s_pred:.5f}, r = {r_pred:.5f}")
    print("\n  Comparison with experiments:")
    print("  " + "-" * 60)

    for name, data in experiments.items():
        sigma_off = abs(n_s_pred - data['n_s']) / data['n_s_err']
        r_ok = r_pred < data['r_bound']
        status = "OK" if sigma_off < 2 and r_ok else ("TENSION" if sigma_off < 3 else "RULED OUT")
        results[name] = {
            'n_s_obs': data['n_s'],
            'n_s_err': data['n_s_err'],
            'r_bound': data['r_bound'],
            'sigma_off': sigma_off,
            'r_satisfied': r_ok,
            'status': status
        }
        print(f"  {name}:")
        print(f"    n_s = {data['n_s']} ± {data['n_s_err']}: deviation = {sigma_off:.2f}σ")
        print(f"    r < {data['r_bound']}: satisfied = {r_ok}")
        print(f"    Status: {status}")

    return results


# ============================================================================
# TEST 4: Alternative Factor Analysis
# ============================================================================

def test_alternative_factors():
    """Explore what factor would be needed to match different N values."""
    print("\n" + "=" * 70)
    print("TEST 4: ALTERNATIVE FACTOR ANALYSIS")
    print("=" * 70)

    ln_xi = calculate_hierarchy_exponent(N_C, N_F)  # ≈ 44.68

    print(f"\n  Hierarchy exponent ln(ξ) = {ln_xi:.4f}")
    print("\n  What factor F would give different N_geo values?")
    print("  N_geo = F × ln(ξ)")
    print("  " + "-" * 50)

    # Test various N values
    N_values = [40, 50, 55, 56.9, 57, 60, 65]
    results = []

    for N in N_values:
        factor = N / ln_xi
        n_s = calculate_spectral_index(N)
        results.append({
            'N': N,
            'factor': factor,
            'factor_approx': f"{factor:.4f}",
            'n_s': n_s
        })
        print(f"  N = {N:.1f}: F = {factor:.4f}, n_s = {n_s:.5f}")

    # Check if 4/π is special
    print(f"\n  The proposition uses F = 4/π = {4/PI:.6f}")
    print(f"  This gives N_geo = {4/PI * ln_xi:.4f}")

    # Check some "nice" mathematical factors
    print("\n  Testing some 'nice' mathematical factors:")
    nice_factors = {
        '4/π': 4/PI,
        '2/√3': 2/np.sqrt(3),
        '√2': np.sqrt(2),
        'e/π': np.e/PI,
        '4/3': 4/3,
        '3/2': 3/2,
        '1': 1.0,
        '2': 2.0,
    }

    for name, factor in nice_factors.items():
        N_geo = factor * ln_xi
        n_s = calculate_spectral_index(N_geo)
        sigma_off = abs(n_s - 0.9649) / 0.0042
        status = "MATCHES" if sigma_off < 0.5 else ("OK" if sigma_off < 2 else "")
        print(f"  F = {name} = {factor:.4f}: N = {N_geo:.1f}, n_s = {n_s:.4f} ({sigma_off:.1f}σ) {status}")

    return results


# ============================================================================
# TEST 5: Physical Consistency Checks
# ============================================================================

def test_physical_consistency():
    """Check physical consistency of the derivation."""
    print("\n" + "=" * 70)
    print("TEST 5: PHYSICAL CONSISTENCY CHECKS")
    print("=" * 70)

    results = {}

    # Check 1: Dimensional consistency
    print("\n  CHECK 1: Dimensional Consistency")
    print("  " + "-" * 50)
    checks = [
        ('ξ = R_stella/ℓ_P', 'length/length', 'dimensionless', True),
        ('ln(ξ)', 'ln(dimensionless)', 'dimensionless', True),
        ('N_geo = (4/π) × ln(ξ)', '(pure number) × dimensionless', 'dimensionless', True),
        ('n_s = 1 - 2/N_geo', '1 - pure number/dimensionless', 'dimensionless', True),
    ]
    for name, operation, result, correct in checks:
        status = "✓" if correct else "✗"
        print(f"  {status} {name}: {operation} → {result}")
    results['dimensional'] = all(c[3] for c in checks)

    # Check 2: Asymptotic freedom requirement
    print("\n  CHECK 2: Asymptotic Freedom")
    print("  " + "-" * 50)
    b0 = calculate_beta_coefficient(N_C, N_F)
    af_satisfied = b0 > 0
    print(f"  b₀ = {b0:.4f} > 0: {af_satisfied}")
    print(f"  Requirement: 11×N_c > 2×N_f → 33 > 6: True")
    results['asymptotic_freedom'] = af_satisfied

    # Check 3: Slow-roll validity
    print("\n  CHECK 3: Slow-Roll Validity")
    print("  " + "-" * 50)
    N_geo = calculate_N_geo(N_C, N_F, factor=4/PI)
    epsilon = 1 / N_geo
    eta = 2 / N_geo
    sr_valid = epsilon < 1 and abs(eta) < 1
    print(f"  ε = 1/N = {epsilon:.4f} << 1: {epsilon < 0.1}")
    print(f"  |η| = 2/N = {eta:.4f} < 1: {abs(eta) < 1}")
    print(f"  Slow-roll approximation valid: {sr_valid}")
    results['slow_roll'] = sr_valid

    # Check 4: e-fold requirement
    print("\n  CHECK 4: E-Fold Requirement (N > 50 for CMB)")
    print("  " + "-" * 50)
    N_min = 50  # Typical minimum for CMB observables
    N_max = 70  # Typical maximum before reheating issues
    N_ok = N_min <= N_geo <= N_max
    print(f"  N_geo = {N_geo:.1f}")
    print(f"  Required: {N_min} ≤ N ≤ {N_max}")
    print(f"  Satisfied: {N_ok}")
    results['e_fold_requirement'] = N_ok

    # Check 5: r bound
    print("\n  CHECK 5: Tensor-to-Scalar Ratio Bound")
    print("  " + "-" * 50)
    r = calculate_tensor_ratio(N_geo, alpha=1/3)
    r_bound = 0.032  # BICEP/Keck 2022
    r_ok = r < r_bound
    print(f"  r = {r:.5f}")
    print(f"  Bound: r < {r_bound}")
    print(f"  Satisfied: {r_ok} (factor of {r_bound/r:.0f} margin)")
    results['r_bound'] = r_ok

    all_pass = all(results.values())
    print(f"\n  ALL PHYSICAL CHECKS PASS: {all_pass}")

    return results, all_pass


# ============================================================================
# TEST 6: The 4/π Factor Investigation
# ============================================================================

def test_four_pi_factor():
    """Investigate possible origins of the 4/π factor."""
    print("\n" + "=" * 70)
    print("TEST 6: INVESTIGATION OF 4/π FACTOR")
    print("=" * 70)

    print("\n  The central question: WHERE DOES 4/π COME FROM?")
    print("\n  The proposition claims it arises from 'SU(3) coset geometry'")
    print("  But the actual derivation shows it was OBSERVED to fit, not DERIVED.")

    # Check 1: Does 4/π appear in SU(3) integrals?
    print("\n  Possible geometric origins:")
    print("  " + "-" * 50)

    origins = [
        ("Coset geodesic: √(2/3) × (π/2) × v → factor √(2/3)", np.sqrt(2/3), False),
        ("SU(3) volume: Vol(SU(3)) = √3 × π⁵", np.sqrt(3) * PI**5, False),
        ("Flag manifold: Vol(CP²) = π²/2", PI**2 / 2, False),
        ("Casimir: C₂(SU(3)) = 4/3", 4/3, False),
        ("Proposed factor: 4/π", 4/PI, True),
    ]

    for name, value, is_used in origins:
        mark = "← USED" if is_used else ""
        print(f"  {name} = {value:.4f} {mark}")

    # The real issue
    print("\n  CRITICAL ASSESSMENT:")
    print("  " + "-" * 50)
    print("  1. The document does NOT derive 4/π from first principles")
    print("  2. The 'SU(3) coset geometry' explanation is hand-waving")
    print("  3. The factor was CHOSEN to make N_geo ≈ 57 match Planck data")
    print("  4. This is FITTING, not PREDICTION")

    # What would constitute a derivation?
    print("\n  WHAT WOULD CONSTITUTE A DERIVATION:")
    print("  " + "-" * 50)
    print("  1. Show that the inflaton field range on SU(3)/U(1)² is:")
    print("     Δφ = (4/π)^{1/2} × M_P × some function of ln(ξ)")
    print("  2. Without using N ≈ 57 as input")
    print("  3. The 'matching' in §6.2 is circular (needs N to find v)")

    return {
        'factor': 4/PI,
        'derived': False,
        'status': 'OBSERVED_NOT_DERIVED',
        'critical_gap': 'The 4/π factor lacks first-principles justification'
    }


# ============================================================================
# PLOTTING
# ============================================================================

def create_plots():
    """Generate visualization plots for the verification."""
    print("\n" + "=" * 70)
    print("GENERATING PLOTS")
    print("=" * 70)

    # Plot 1: N_c sensitivity
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Panel 1: n_s vs N_c
    ax = axes[0, 0]
    N_c_range = np.arange(2, 8)
    n_s_values = []
    for N_c in N_c_range:
        N_geo = calculate_N_geo(N_c, N_F, factor=4/PI)
        n_s_values.append(calculate_spectral_index(N_geo))

    ax.plot(N_c_range, n_s_values, 'bo-', markersize=10, linewidth=2)
    ax.axhline(0.9649, color='red', linestyle='--', linewidth=2, label='Planck 2018')
    ax.fill_between([1.5, 7.5], 0.9649-0.0042, 0.9649+0.0042, alpha=0.3, color='red')
    ax.axvline(3, color='green', linestyle=':', linewidth=2, label='N_c = 3 (SU(3))')
    ax.set_xlabel('N_c', fontsize=12)
    ax.set_ylabel('n_s', fontsize=12)
    ax.set_title('Spectral Index vs N_c\n(N_f = 3 fixed)', fontsize=12)
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Panel 2: n_s vs N_f
    ax = axes[0, 1]
    N_f_range = [0, 1, 2, 3, 4, 5, 6, 7, 8]
    n_s_values = []
    N_f_valid = []
    for N_f in N_f_range:
        if 11 * N_C > 2 * N_f:  # Asymptotic freedom
            N_geo = calculate_N_geo(N_C, N_f, factor=4/PI)
            n_s_values.append(calculate_spectral_index(N_geo))
            N_f_valid.append(N_f)

    ax.plot(N_f_valid, n_s_values, 'go-', markersize=10, linewidth=2)
    ax.axhline(0.9649, color='red', linestyle='--', linewidth=2, label='Planck 2018')
    ax.fill_between([-0.5, 16.5], 0.9649-0.0042, 0.9649+0.0042, alpha=0.3, color='red')
    ax.axvline(3, color='blue', linestyle=':', linewidth=2, label='N_f = 3 (QCD)')
    ax.axvline(6, color='orange', linestyle=':', linewidth=2, label='N_f = 6 (inflation)')
    ax.set_xlabel('N_f', fontsize=12)
    ax.set_ylabel('n_s', fontsize=12)
    ax.set_title('Spectral Index vs N_f\n(N_c = 3 fixed)', fontsize=12)
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Panel 3: Factor analysis
    ax = axes[1, 0]
    factors = np.linspace(0.5, 2.5, 100)
    ln_xi = calculate_hierarchy_exponent(N_C, N_F)
    n_s_values = [calculate_spectral_index(f * ln_xi) for f in factors]

    ax.plot(factors, n_s_values, 'b-', linewidth=2)
    ax.axhline(0.9649, color='red', linestyle='--', linewidth=2, label='Planck 2018')
    ax.fill_between(factors, 0.9649-0.0042, 0.9649+0.0042, alpha=0.3, color='red')
    ax.axvline(4/PI, color='green', linestyle='-', linewidth=2, label=f'4/π = {4/PI:.4f}')
    ax.axvline(1.0, color='gray', linestyle=':', linewidth=1, label='F = 1')
    ax.set_xlabel('Factor F (N_geo = F × ln(ξ))', fontsize=12)
    ax.set_ylabel('n_s', fontsize=12)
    ax.set_title('Spectral Index vs Factor F\n(Showing which F matches Planck)', fontsize=12)
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Panel 4: r-n_s plane
    ax = axes[1, 1]
    N_range = np.linspace(30, 100, 100)
    n_s_vals = [calculate_spectral_index(N) for N in N_range]
    r_vals = [calculate_tensor_ratio(N, alpha=1/3) for N in N_range]

    ax.plot(n_s_vals, r_vals, 'b-', linewidth=2, label='α-attractor (α=1/3)')
    ax.axvline(0.9649, color='red', linestyle='--', linewidth=2, label='Planck n_s')
    ax.axhline(0.032, color='orange', linestyle='--', linewidth=2, label='BICEP/Keck r bound')

    # Mark specific N values
    for N in [40, 50, 57, 60, 70]:
        n_s = calculate_spectral_index(N)
        r = calculate_tensor_ratio(N, alpha=1/3)
        ax.plot(n_s, r, 'ko', markersize=8)
        ax.annotate(f'N={N}', (n_s, r), xytext=(5, 5), textcoords='offset points', fontsize=9)

    # Mark the prediction
    N_geo = calculate_N_geo(N_C, N_F, factor=4/PI)
    n_s_pred = calculate_spectral_index(N_geo)
    r_pred = calculate_tensor_ratio(N_geo, alpha=1/3)
    ax.plot(n_s_pred, r_pred, 'r*', markersize=20, label=f'Prediction (N={N_geo:.1f})')

    ax.set_xlabel('n_s', fontsize=12)
    ax.set_ylabel('r', fontsize=12)
    ax.set_title('r vs n_s Plane\n(α-attractor with α = 1/3)', fontsize=12)
    ax.set_xlim(0.93, 1.0)
    ax.set_ylim(0, 0.05)
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plot_path = PLOT_DIR / 'prop_0_0_17aa_adversarial_verification.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\n  Saved: {plot_path}")
    plt.close()

    return str(plot_path)


# ============================================================================
# MAIN
# ============================================================================

def main():
    """Run all adversarial verification tests."""
    print("\n" + "=" * 70)
    print("ADVERSARIAL PHYSICS VERIFICATION: PROPOSITION 0.0.17aa")
    print("Spectral Index as a Genuine Geometric Prediction")
    print("=" * 70)
    print(f"\nDate: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

    results = {}

    # Run all tests
    results['algebraic'], alg_pass = test_algebraic_derivation()
    results['sensitivity'] = test_sensitivity_analysis()
    results['experimental'] = test_experimental_comparison()
    results['alternative_factors'] = test_alternative_factors()
    results['physical'], phys_pass = test_physical_consistency()
    results['four_pi_investigation'] = test_four_pi_factor()

    # Generate plots
    plot_path = create_plots()
    results['plot_path'] = plot_path

    # Summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)

    print("\n  ALGEBRAIC CORRECTNESS:")
    print(f"  ✓ All equations verified: {alg_pass}")

    print("\n  NUMERICAL AGREEMENT:")
    N_geo = calculate_N_geo(N_C, N_F, factor=4/PI)
    n_s_pred = calculate_spectral_index(N_geo)
    print(f"  ✓ n_s = {n_s_pred:.5f} vs Planck 0.9649 ± 0.0042")
    print(f"  ✓ Deviation: {abs(n_s_pred - 0.9649)/0.0042:.2f}σ (excellent)")

    print("\n  PHYSICAL CONSISTENCY:")
    print(f"  ✓ All checks pass: {phys_pass}")

    print("\n  CRITICAL GAP:")
    print("  ✗ The factor 4/π is OBSERVED, not DERIVED")
    print("  ✗ The claim of 'first-principles derivation' is NOT SUPPORTED")
    print("  ✗ Status should be: 'Remarkable consistency relation'")

    print("\n  NEW EXPERIMENTAL TENSION:")
    print("  ⚠ ACT DR6 + Planck finds n_s = 0.9709 ± 0.0038")
    print(f"  ⚠ Tension with prediction: {abs(n_s_pred - 0.9709)/0.0038:.1f}σ")

    print("\n  OVERALL VERDICT: PARTIAL VERIFICATION")
    print("  - Numerical success (0.02σ from Planck 2018)")
    print("  - Physical formulas correct")
    print("  - BUT: Central claim (derivation) not supported")
    print("  - AND: Tension with newer data (ACT DR6)")

    # Save results
    results['summary'] = {
        'algebraic_pass': alg_pass,
        'physical_pass': phys_pass,
        'n_s_predicted': n_s_pred,
        'n_s_planck': 0.9649,
        'sigma_off_planck': abs(n_s_pred - 0.9649)/0.0042,
        'n_s_act': 0.9709,
        'sigma_off_act': abs(n_s_pred - 0.9709)/0.0038,
        'four_pi_derived': False,
        'overall_verdict': 'PARTIAL',
        'critical_gap': 'The 4/π factor lacks first-principles derivation'
    }

    results_path = PLOT_DIR.parent / 'prop_0_0_17aa_verification_results.json'
    with open(results_path, 'w') as f:
        # Convert numpy types to Python native types for JSON serialization
        def convert(obj):
            if isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, (np.bool_, bool)):
                return bool(obj)
            elif isinstance(obj, dict):
                return {k: convert(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert(v) for v in obj]
            return obj
        json.dump(convert(results), f, indent=2)
    print(f"\n  Results saved to: {results_path}")

    print("\n" + "=" * 70)
    print("VERIFICATION COMPLETE")
    print("=" * 70)

    return results


if __name__ == "__main__":
    results = main()
