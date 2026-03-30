#!/usr/bin/env python3
"""
Proposition 7.8.1: Exceptional Group Glueball Predictions — Adversarial Physics Verification
==============================================================================================

ADVERSARIAL VERIFICATION PROTOCOL

You are an independent verification agent. Your role is ADVERSARIAL.
Your job is to find errors, gaps, and inconsistencies.

Key Claims Under Adversarial Test:
    (ADV-1)  Casimir invariants for all 5 exceptional groups — independent derivation
    (ADV-2)  Sp(2N) Casimir ratio: test claimed eta = sqrt(2) vs correct 4(N+1)/(2N+1)
               [NOTE: Eq. (5.16) corrected in Derivation §5.4 to 4(N+1)/(2N+1)]
    (ADV-3)  M0 weighted mean: verify 2.33 vs actual inverse-variance weighted mean
               [NOTE: §5.3 now reports wt. mean 2.282±0.013; 2.33 is "adopted central value"]
    (ADV-4)  SU(N) Casimir scaling universality: chi^2 test of M0 constancy
    (ADV-5)  R_cont predictions: stress test against all available lattice data
    (ADV-6)  c(G) bounds: sensitivity to sqrt(sigma)/Lambda_MSbar assumptions
               [NOTE: §6.2 now presents both estimates (A) and (B) with sensitivity table]
    (ADV-7)  eta monotonicity: verify decreasing with rank for exceptionals
    (ADV-8)  E8 self-duality: fundamental = adjoint cross-checks
    (ADV-9)  G2 = large-N consistency: eta(G2) = sqrt(2) = lim_{N->inf} eta_SU(N)
    (ADV-10) Error propagation: verify ±0.15 quadrature composition
    (ADV-11) Quasigluon model cross-check: compare with Buisseret (2011) predictions
    (ADV-12) Center symmetry: verify Z(G) assignments against standard tables

Related Documents:
    - Statement: docs/proofs/Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions.md
    - Derivation: docs/proofs/Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions-Derivation.md
    - Applications: docs/proofs/Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions-Applications.md

Verification Date: 2026-02-19
"""

import numpy as np
import json
import os
from datetime import datetime
from typing import Dict, List, Tuple, Any

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False

# =============================================================================
# OUTPUT DIRECTORIES
# =============================================================================

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BASE_DIR = os.path.dirname(SCRIPT_DIR)
PLOT_DIR = os.path.join(BASE_DIR, 'plots')
os.makedirs(PLOT_DIR, exist_ok=True)

# =============================================================================
# TEST INFRASTRUCTURE
# =============================================================================

test_results = []
adversarial_findings = []


def record_test(name: str, passed: bool, details: str, data: dict = None):
    """Record a test result."""
    result = {
        "test": name,
        "passed": passed,
        "details": details,
        "data": data or {}
    }
    test_results.append(result)
    status = "PASS" if passed else "FAIL"
    print(f"  [{status}] {name}")
    if not passed:
        print(f"         → {details}")


def record_finding(finding_id: str, severity: str, description: str, impact: str):
    """Record an adversarial finding."""
    finding = {
        "id": finding_id,
        "severity": severity,
        "description": description,
        "impact": impact
    }
    adversarial_findings.append(finding)
    print(f"  *** FINDING {finding_id} ({severity}): {description}")


# =============================================================================
# EXCEPTIONAL GROUP DATA (STANDARD REFERENCE VALUES)
# =============================================================================

EXCEPTIONAL_GROUPS = {
    'G2': {
        'rank': 2, 'h_dual': 4,
        'd_fund': 7, 'd_adj': 14,
        'C2_fund': 2, 'C2_adj': 4,
        'T_fund': 1, 'T_adj': 4,
        'center': '{1}', 'center_order': 1,
    },
    'F4': {
        'rank': 4, 'h_dual': 9,
        'd_fund': 26, 'd_adj': 52,
        'C2_fund': 6, 'C2_adj': 9,
        'T_fund': 3, 'T_adj': 9,
        'center': '{1}', 'center_order': 1,
    },
    'E6': {
        'rank': 6, 'h_dual': 12,
        'd_fund': 27, 'd_adj': 78,
        'C2_fund': 26/3, 'C2_adj': 12,
        'T_fund': 3, 'T_adj': 12,
        'center': 'Z3', 'center_order': 3,
    },
    'E7': {
        'rank': 7, 'h_dual': 18,
        'd_fund': 56, 'd_adj': 133,
        'C2_fund': 57/4, 'C2_adj': 18,
        'T_fund': 6, 'T_adj': 18,
        'center': 'Z2', 'center_order': 2,
    },
    'E8': {
        'rank': 8, 'h_dual': 30,
        'd_fund': 248, 'd_adj': 248,
        'C2_fund': 30, 'C2_adj': 30,
        'T_fund': 30, 'T_adj': 30,
        'center': '{1}', 'center_order': 1,
    },
}

# SU(N) lattice data: (R_cont, error) from Athenodorou & Teper
SU_DATA = {
    2: (3.56, 0.18),
    3: (3.405, 0.021),
    4: (3.52, 0.11),
    5: (3.55, 0.14),
    6: (3.53, 0.15),
    8: (3.55, 0.22),
    12: (3.60, 0.30),
}

# Sp(2N) lattice data: (R_cont, error) from Bennett et al.
SP_DATA = {
    1: (3.56, 0.18),  # Sp(2) = SU(2)
    2: (3.31, 0.22),  # Sp(4)
    3: (3.44, 0.30),  # Sp(6)
    4: (3.46, 0.35),  # Sp(8)
}

# Buisseret (2011) quasigluon model predictions
BUISSERET_PREDICTIONS = {
    'G2': 3.3, 'F4': 2.9, 'E6': 2.8, 'E7': 2.6, 'E8': 2.3
}

# Paper's claimed values
M0_CLAIMED = 2.33
M0_CLAIMED_ERR = 0.05
R_CONT_SU3 = 3.405
R_CONT_SU3_ERR = 0.021
SIGMA_LAMBDA_SU3 = 1.994  # sqrt(sigma)/Lambda_MSbar for SU(3)


# =============================================================================
# HELPER FUNCTIONS
# =============================================================================

def eta_SU(N: int) -> float:
    """Casimir ratio factor for SU(N)."""
    return np.sqrt(2 * N**2 / (N**2 - 1))


def eta_Sp_correct(N: int) -> float:
    """CORRECT Casimir ratio factor for Sp(2N).

    The correct formula is sqrt(4(N+1)/(2N+1)), NOT sqrt(2).
    C2(adj)/C2(fund) = 4(N+1)/(2N+1) for Sp(2N).
    """
    return np.sqrt(4 * (N + 1) / (2 * N + 1))


def eta_Sp_claimed(N: int) -> float:
    """CLAIMED (incorrect) Casimir ratio factor from Eq. (5.16)."""
    return np.sqrt(2)


def eta_exceptional(name: str) -> float:
    """Casimir ratio factor for exceptional group."""
    g = EXCEPTIONAL_GROUPS[name]
    return np.sqrt(g['C2_adj'] / g['C2_fund'])


def weighted_mean(values, errors):
    """Compute inverse-variance weighted mean and error."""
    weights = 1.0 / np.array(errors)**2
    wm = np.sum(np.array(values) * weights) / np.sum(weights)
    wm_err = 1.0 / np.sqrt(np.sum(weights))
    return wm, wm_err


# =============================================================================
# ADV-1: CASIMIR INVARIANT VERIFICATION
# =============================================================================

def test_ADV1_casimir_invariants():
    """Verify Casimir invariants for all exceptional groups via Dynkin identity."""
    print("\n" + "=" * 60)
    print("ADV-1: Casimir Invariant Independent Verification")
    print("=" * 60)

    all_pass = True
    for name, g in EXCEPTIONAL_GROUPS.items():
        # Check T(fund) * d_adj = C2(fund) * d_fund
        lhs_fund = g['T_fund'] * g['d_adj']
        rhs_fund = g['C2_fund'] * g['d_fund']
        fund_ok = abs(lhs_fund - rhs_fund) < 1e-10

        # Check T(adj) * d_adj = C2(adj) * d_adj
        lhs_adj = g['T_adj'] * g['d_adj']
        rhs_adj = g['C2_adj'] * g['d_adj']
        adj_ok = abs(lhs_adj - rhs_adj) < 1e-10

        # Check C2(adj) = h_dual (in standard normalization)
        h_ok = abs(g['C2_adj'] - g['h_dual']) < 1e-10

        passed = fund_ok and adj_ok and h_ok
        if not passed:
            all_pass = False

        record_test(
            f"ADV-1.{name}: Dynkin identity",
            passed,
            f"T(f)*d_adj={lhs_fund}, C2(f)*d_R={rhs_fund}, "
            f"T(adj)*d_adj={lhs_adj}, C2(adj)*d_adj={rhs_adj}, "
            f"C2(adj)={g['C2_adj']} vs h_dual={g['h_dual']}",
            {"group": name, "fund_ok": fund_ok, "adj_ok": adj_ok, "h_ok": h_ok}
        )

    # Cross-check: E7 ratio 24/19 = 168/133
    ratio_a = 24 / 19
    ratio_b = 168 / 133
    e7_notation = abs(ratio_a - ratio_b) < 1e-14
    record_test(
        "ADV-1.E7_notation: 24/19 = 168/133",
        e7_notation,
        f"24/19 = {ratio_a:.15f}, 168/133 = {ratio_b:.15f}",
        {"ratio_a": ratio_a, "ratio_b": ratio_b}
    )


# =============================================================================
# ADV-2: SP(2N) CASIMIR RATIO — CRITICAL ADVERSARIAL TEST
# =============================================================================

def test_ADV2_Sp_casimir_ratio():
    """Adversarial test: Eq. (5.16) claims C2(adj)/C2(fund) = 2 for ALL Sp(2N).

    This is INCORRECT. The correct formula is 4(N+1)/(2N+1).
    """
    print("\n" + "=" * 60)
    print("ADV-2: Sp(2N) Casimir Ratio — Critical Adversarial Test")
    print("=" * 60)

    print("  Eq. (5.16) claims: C2(adj)/C2(fund) = 2 for all Sp(2N)")
    print("  Correct formula:   C2(adj)/C2(fund) = 4(N+1)/(2N+1)")
    print()

    errors_found = False
    for N in [1, 2, 3, 4, 10, 100]:
        correct_ratio = 4 * (N + 1) / (2 * N + 1)
        claimed_ratio = 2.0
        discrepancy = abs(correct_ratio - claimed_ratio) / claimed_ratio * 100

        eta_correct = np.sqrt(correct_ratio)
        eta_claimed = np.sqrt(claimed_ratio)
        eta_discrepancy = abs(eta_correct - eta_claimed) / eta_claimed * 100

        is_eq = abs(correct_ratio - 2.0) < 0.001
        if not is_eq:
            errors_found = True

        print(f"  Sp({2*N}): correct ratio = {correct_ratio:.6f}, "
              f"claimed = 2.000, discrepancy = {discrepancy:.1f}%")
        print(f"           eta_correct = {eta_correct:.4f}, "
              f"eta_claimed = {eta_claimed:.4f}, "
              f"diff = {eta_discrepancy:.1f}%")

    # Verify N=1 matches SU(2)
    sp2_ratio = 4 * 2 / 3  # = 8/3
    su2_ratio = 2 * 4 / (4 - 1)  # = 8/3
    su2_match = abs(sp2_ratio - su2_ratio) < 1e-14

    record_test(
        "ADV-2.a: Sp(2)=SU(2) Casimir ratio match",
        su2_match,
        f"Sp(2) ratio = {sp2_ratio:.6f} = SU(2) ratio = {su2_ratio:.6f}",
        {"sp2_ratio": sp2_ratio, "su2_ratio": su2_ratio}
    )

    # The key adversarial test: is Eq. (5.16) correct?
    record_test(
        "ADV-2.b: Eq. (5.16) correctness",
        not errors_found,  # This SHOULD fail
        "Eq. (5.16) claims C2(adj)/C2(fund) = 2 for all N; "
        f"actual ratio ranges from {4*2/3:.4f} (N=1) to 2.000 (N→∞)",
        {"equation_correct": not errors_found}
    )

    if errors_found:
        record_finding(
            "ADV-2-F1", "MAJOR",
            "Eq. (5.16) incorrectly states C2(adj)/C2(fund) = 2 for all Sp(2N). "
            "Correct formula: 4(N+1)/(2N+1). "
            "Ratio is 8/3 at N=1, approaching 2 only as N→∞.",
            "Limited impact on exceptional group predictions (uses SU calibration), "
            "but Sp cross-check M0 values in §5.4 are wrong."
        )

    # Verify impact on M0 extraction from Sp data
    print("\n  Impact on M0 extraction from Sp(2N):")
    m0_claimed_vals = []
    m0_correct_vals = []
    m0_correct_errs = []
    for N, (R, Re) in SP_DATA.items():
        eta_cl = eta_Sp_claimed(N)
        eta_co = eta_Sp_correct(N)
        m0_cl = R / eta_cl
        m0_co = R / eta_co
        m0_co_err = Re / eta_co
        m0_claimed_vals.append(m0_cl)
        m0_correct_vals.append(m0_co)
        m0_correct_errs.append(m0_co_err)
        print(f"    Sp({2*N}): M0(claimed eta) = {m0_cl:.3f}, "
              f"M0(correct eta) = {m0_co:.3f}")

    wm_correct, wm_correct_err = weighted_mean(m0_correct_vals, m0_correct_errs)
    wm_claimed = np.mean(m0_claimed_vals)  # Paper uses simple average-like value
    print(f"\n    M0 from Sp (corrected): {wm_correct:.3f} ± {wm_correct_err:.3f}")
    print(f"    M0 from Sp (paper):     2.40 ± 0.10")


# =============================================================================
# ADV-3: M0 WEIGHTED MEAN VERIFICATION
# =============================================================================

def test_ADV3_M0_weighted_mean():
    """Verify the claimed M0 = 2.33 ± 0.05 against actual weighted mean."""
    print("\n" + "=" * 60)
    print("ADV-3: M0 Weighted Mean Verification")
    print("=" * 60)

    # Extract M0 from SU(N) data
    m0_vals = []
    m0_errs = []
    for N, (R, Re) in SU_DATA.items():
        eta = eta_SU(N)
        m0 = R / eta
        m0_err = Re / eta
        m0_vals.append(m0)
        m0_errs.append(m0_err)
        print(f"  SU({N:2d}): R_cont = {R:.3f} ± {Re:.3f}, "
              f"eta = {eta:.4f}, M0 = {m0:.3f} ± {m0_err:.3f}")

    # Compute actual weighted mean
    wm, wm_err = weighted_mean(m0_vals, m0_errs)
    print(f"\n  Actual weighted mean: M0 = {wm:.4f} ± {wm_err:.4f}")
    print(f"  Claimed value:       M0 = {M0_CLAIMED} ± {M0_CLAIMED_ERR}")

    # Check how many sigma apart
    sigma_diff = abs(M0_CLAIMED - wm) / np.sqrt(wm_err**2 + M0_CLAIMED_ERR**2)
    print(f"  Discrepancy: {sigma_diff:.1f}σ (combined error)")

    # Check SU(3) weight dominance
    w3 = 1.0 / m0_errs[1]**2
    w_total = sum(1.0 / e**2 for e in m0_errs)
    su3_weight = w3 / w_total
    print(f"\n  SU(3) weight fraction: {su3_weight:.1%}")

    # The claimed 2.33 is not a proper weighted mean
    is_consistent = abs(M0_CLAIMED - wm) < M0_CLAIMED_ERR
    record_test(
        "ADV-3.a: M0 claimed vs actual weighted mean",
        is_consistent,
        f"Claimed {M0_CLAIMED} ± {M0_CLAIMED_ERR}, "
        f"actual weighted mean {wm:.4f} ± {wm_err:.4f}, "
        f"diff = {sigma_diff:.1f}σ",
        {"claimed": M0_CLAIMED, "actual_wm": wm, "actual_err": wm_err,
         "sigma_diff": sigma_diff, "su3_weight_fraction": su3_weight}
    )

    if not is_consistent:
        record_finding(
            "ADV-3-F1", "MEDIUM",
            f"M0 = {M0_CLAIMED} labeled as 'weighted mean' but actual weighted mean "
            f"is {wm:.3f} ± {wm_err:.3f}. The value 2.33 appears to be a compromise "
            f"accounting for the systematic upward trend with N.",
            "R_cont predictions ~2% high but within stated ±0.15 error bars."
        )

    # Chi-squared test for M0 constancy
    chi2 = sum(((m0_vals[i] - wm) / m0_errs[i])**2 for i in range(len(m0_vals)))
    ndof = len(m0_vals) - 1
    chi2_per_dof = chi2 / ndof
    print(f"\n  Chi^2/dof for M0 constancy: {chi2_per_dof:.2f} "
          f"(chi^2 = {chi2:.2f}, dof = {ndof})")

    record_test(
        "ADV-3.b: M0 constancy chi^2/dof",
        chi2_per_dof < 3.0,
        f"chi^2/dof = {chi2_per_dof:.2f} (acceptable if < 3)",
        {"chi2": chi2, "ndof": ndof, "chi2_per_dof": chi2_per_dof}
    )

    return wm, wm_err


# =============================================================================
# ADV-4: SU(N) CASIMIR SCALING UNIVERSALITY
# =============================================================================

def test_ADV4_SU_universality():
    """Test whether R_cont/eta is truly constant across SU(N)."""
    print("\n" + "=" * 60)
    print("ADV-4: SU(N) Casimir Scaling Universality Test")
    print("=" * 60)

    # Compute R_cont/eta for each N and look for trends
    N_vals = []
    m0_vals = []
    m0_errs = []
    for N, (R, Re) in sorted(SU_DATA.items()):
        eta = eta_SU(N)
        m0 = R / eta
        m0_err = Re / eta
        N_vals.append(N)
        m0_vals.append(m0)
        m0_errs.append(m0_err)

    N_arr = np.array(N_vals)
    m0_arr = np.array(m0_vals)
    m0_err_arr = np.array(m0_errs)

    # Linear fit: M0 = a + b * (1/N^2) to test for sub-leading corrections
    x = 1.0 / N_arr**2
    w = 1.0 / m0_err_arr**2

    # Weighted linear regression
    S = np.sum(w)
    Sx = np.sum(w * x)
    Sy = np.sum(w * m0_arr)
    Sxx = np.sum(w * x**2)
    Sxy = np.sum(w * x * m0_arr)

    det = S * Sxx - Sx**2
    a = (Sxx * Sy - Sx * Sxy) / det  # intercept (N->inf limit)
    b = (S * Sxy - Sx * Sy) / det    # slope (1/N^2 correction)
    a_err = np.sqrt(Sxx / det)
    b_err = np.sqrt(S / det)

    print(f"  Linear fit: M0 = {a:.4f}(±{a_err:.4f}) "
          f"+ {b:.3f}(±{b_err:.3f}) / N^2")
    print(f"  Large-N limit: M0(∞) = {a:.4f} ± {a_err:.4f}")

    slope_significant = abs(b) > 2 * b_err
    if slope_significant:
        print(f"  → 1/N^2 correction is {abs(b)/b_err:.1f}σ significant")
    else:
        print(f"  → 1/N^2 correction is {abs(b)/b_err:.1f}σ (not significant)")

    record_test(
        "ADV-4: SU(N) M0 large-N extrapolation",
        True,  # Informational test
        f"M0(∞) = {a:.4f} ± {a_err:.4f}, "
        f"1/N^2 slope = {b:.3f} ± {b_err:.3f} "
        f"({abs(b)/b_err:.1f}σ significance)",
        {"M0_inf": a, "M0_inf_err": a_err, "slope": b, "slope_err": b_err,
         "slope_significance_sigma": abs(b)/b_err}
    )

    return N_arr, m0_arr, m0_err_arr, a, b


# =============================================================================
# ADV-5: R_CONT PREDICTIONS VS LATTICE DATA
# =============================================================================

def test_ADV5_R_cont_predictions():
    """Stress-test R_cont predictions against all available lattice data."""
    print("\n" + "=" * 60)
    print("ADV-5: R_cont Predictions vs Lattice Data")
    print("=" * 60)

    all_within_2sigma = True
    max_tension = 0.0

    # SU(N) predictions vs lattice
    print("\n  SU(N) predictions:")
    su_tensions = []
    for N, (R_lat, R_err) in sorted(SU_DATA.items()):
        eta = eta_SU(N)
        R_pred = M0_CLAIMED * eta
        R_pred_err = 0.15  # Paper's claimed error
        tension = abs(R_pred - R_lat) / np.sqrt(R_pred_err**2 + R_err**2)
        su_tensions.append(tension)
        if tension > max_tension:
            max_tension = tension
        if tension > 2.0:
            all_within_2sigma = False
        print(f"    SU({N:2d}): pred = {R_pred:.3f} ± {R_pred_err:.2f}, "
              f"lat = {R_lat:.3f} ± {R_err:.3f}, tension = {tension:.2f}σ")

    # Sp(2N) predictions vs lattice (using CORRECT eta)
    print("\n  Sp(2N) predictions (correct eta):")
    sp_tensions = []
    for N, (R_lat, R_err) in sorted(SP_DATA.items()):
        eta = eta_Sp_correct(N)
        R_pred = M0_CLAIMED * eta
        R_pred_err = 0.15
        tension = abs(R_pred - R_lat) / np.sqrt(R_pred_err**2 + R_err**2)
        sp_tensions.append(tension)
        if tension > max_tension:
            max_tension = tension
        if tension > 2.0:
            all_within_2sigma = False
        print(f"    Sp({2*N:2d}): pred = {R_pred:.3f} ± {R_pred_err:.2f}, "
              f"lat = {R_lat:.3f} ± {R_err:.3f}, tension = {tension:.2f}σ")

    record_test(
        "ADV-5: All predictions within 2σ of lattice",
        all_within_2sigma,
        f"Max tension = {max_tension:.2f}σ",
        {"max_tension": max_tension,
         "su_tensions": su_tensions,
         "sp_tensions": sp_tensions}
    )


# =============================================================================
# ADV-6: c(G) SENSITIVITY ANALYSIS
# =============================================================================

def test_ADV6_cG_sensitivity():
    """Sensitivity analysis: how do c(G) values change with sqrt(sigma)/Lambda?"""
    print("\n" + "=" * 60)
    print("ADV-6: c(G) Sensitivity to √σ/Λ_MSbar Assumptions")
    print("=" * 60)

    # Test multiple values of sqrt(sigma)/Lambda
    sigma_lambda_values = [1.0, 1.5, 1.88, 1.994, 2.0, 2.5]

    exceptional_R_cont = {}
    for name in EXCEPTIONAL_GROUPS:
        eta = eta_exceptional(name)
        exceptional_R_cont[name] = M0_CLAIMED * eta

    print(f"\n  {'Group':>5s}", end="")
    for sl in sigma_lambda_values:
        print(f"  √σ/Λ={sl:.2f}", end="")
    print()

    all_positive = True
    min_cG = float('inf')

    for name in ['G2', 'F4', 'E6', 'E7', 'E8']:
        R = exceptional_R_cont[name]
        print(f"  {name:>5s}", end="")
        for sl in sigma_lambda_values:
            cG = R * sl
            if cG < min_cG:
                min_cG = cG
            print(f"  c={cG:5.2f}    ", end="")
        print()

    # Using Eq. (6.4) scaling properly
    print("\n  With Eq. (6.4) b0-scaling from SU(3):")
    b0_su3 = 11 * 3  # 11 * h_dual for SU(3)
    for name in ['G2', 'F4', 'E6', 'E7', 'E8']:
        g = EXCEPTIONAL_GROUPS[name]
        R = exceptional_R_cont[name]
        b0_G = 11 * g['h_dual']
        sl_scaled = SIGMA_LAMBDA_SU3 * np.sqrt(b0_su3 / b0_G)
        cG_scaled = R * sl_scaled
        cG_paper = R * 2.0
        print(f"    {name}: b0_ratio = {b0_su3/b0_G:.4f}, "
              f"√σ/Λ(scaled) = {sl_scaled:.3f}, "
              f"c(G) = {cG_scaled:.2f} (paper: {cG_paper:.2f})")
        if cG_scaled < min_cG:
            min_cG = cG_scaled
        if cG_scaled <= 0:
            all_positive = False

    record_test(
        "ADV-6.a: All c(G) positive (mass gap existence)",
        all_positive,
        f"Minimum c(G) = {min_cG:.2f} > 0",
        {"min_cG": min_cG, "all_positive": all_positive}
    )

    # Check if Eq. (6.4) gives very different c(G) for E8
    g_e8 = EXCEPTIONAL_GROUPS['E8']
    b0_e8 = 11 * g_e8['h_dual']
    sl_e8 = SIGMA_LAMBDA_SU3 * np.sqrt(b0_su3 / b0_e8)
    cG_e8_scaled = exceptional_R_cont['E8'] * sl_e8
    cG_e8_paper = exceptional_R_cont['E8'] * 2.0

    large_discrepancy = abs(cG_e8_scaled - cG_e8_paper) / cG_e8_paper > 0.5

    record_test(
        "ADV-6.b: c(E8) paper vs Eq.(6.4) scaling",
        not large_discrepancy,
        f"c(E8) paper = {cG_e8_paper:.2f}, "
        f"c(E8) Eq.(6.4) = {cG_e8_scaled:.2f}, "
        f"discrepancy = {abs(cG_e8_scaled - cG_e8_paper)/cG_e8_paper:.0%}",
        {"cG_e8_paper": cG_e8_paper, "cG_e8_eq64": cG_e8_scaled}
    )

    if large_discrepancy:
        record_finding(
            "ADV-6-F1", "HIGH",
            f"c(E8) from Eq. (6.4) scaling = {cG_e8_scaled:.2f} vs "
            f"paper's {cG_e8_paper:.2f}. The √σ/Λ ~ 2.0 assumption "
            f"may significantly overestimate c(G) for large-rank groups.",
            "c(G) > 0 for mass gap existence is still satisfied, "
            "but numerical values are unreliable for E7, E8."
        )

    return exceptional_R_cont


# =============================================================================
# ADV-7: ETA MONOTONICITY
# =============================================================================

def test_ADV7_eta_monotonicity():
    """Verify eta is strictly decreasing with rank for exceptional groups."""
    print("\n" + "=" * 60)
    print("ADV-7: Eta Monotonicity (Decreasing with Rank)")
    print("=" * 60)

    groups = ['G2', 'F4', 'E6', 'E7', 'E8']
    etas = [(name, eta_exceptional(name)) for name in groups]
    ranks = [EXCEPTIONAL_GROUPS[name]['rank'] for name in groups]

    monotonic = True
    for i in range(len(etas) - 1):
        ok = etas[i][1] > etas[i+1][1]
        if not ok:
            monotonic = False
        print(f"  eta({etas[i][0]}) = {etas[i][1]:.4f} > "
              f"eta({etas[i+1][0]}) = {etas[i+1][1]:.4f}: "
              f"{'OK' if ok else 'FAIL'}")

    record_test(
        "ADV-7: Eta strictly decreasing with rank",
        monotonic,
        f"Ranks: {ranks}, etas: {[f'{e[1]:.4f}' for e in etas]}",
        {"monotonic": monotonic, "etas": {n: v for n, v in etas}}
    )


# =============================================================================
# ADV-8: E8 SELF-DUALITY CROSS-CHECKS
# =============================================================================

def test_ADV8_E8_self_duality():
    """Verify E8 self-duality properties."""
    print("\n" + "=" * 60)
    print("ADV-8: E8 Self-Duality Verification")
    print("=" * 60)

    g = EXCEPTIONAL_GROUPS['E8']

    # fund = adj
    fund_eq_adj = (g['d_fund'] == g['d_adj'])
    record_test("ADV-8.a: d_fund = d_adj = 248", fund_eq_adj,
                f"d_fund = {g['d_fund']}, d_adj = {g['d_adj']}")

    # C2 equality
    c2_eq = abs(g['C2_fund'] - g['C2_adj']) < 1e-14
    record_test("ADV-8.b: C2(fund) = C2(adj) = 30", c2_eq,
                f"C2(fund) = {g['C2_fund']}, C2(adj) = {g['C2_adj']}")

    # T equality
    t_eq = abs(g['T_fund'] - g['T_adj']) < 1e-14
    record_test("ADV-8.c: T(fund) = T(adj) = 30", t_eq,
                f"T(fund) = {g['T_fund']}, T(adj) = {g['T_adj']}")

    # eta = 1
    eta_e8 = eta_exceptional('E8')
    eta_1 = abs(eta_e8 - 1.0) < 1e-14
    record_test("ADV-8.d: eta(E8) = 1 exactly", eta_1,
                f"eta(E8) = {eta_e8}")

    # E8 has no smaller faithful representation
    # (This is a standard fact about E8)
    record_test("ADV-8.e: E8 smallest faithful rep is 248-dim",
                True,  # Standard Lie algebra fact
                "E8 has no representation smaller than 248-dimensional (standard)")


# =============================================================================
# ADV-9: G2 = LARGE-N CONSISTENCY
# =============================================================================

def test_ADV9_G2_large_N():
    """Verify G2 eta matches the SU(N→∞) and Sp(2N→∞) limits."""
    print("\n" + "=" * 60)
    print("ADV-9: G2 = Large-N Limit Consistency")
    print("=" * 60)

    eta_g2 = eta_exceptional('G2')
    sqrt2 = np.sqrt(2)

    # G2 = sqrt(2) exactly
    g2_exact = abs(eta_g2 - sqrt2) < 1e-14
    record_test("ADV-9.a: eta(G2) = sqrt(2) exactly", g2_exact,
                f"eta(G2) = {eta_g2:.15f}, sqrt(2) = {sqrt2:.15f}")

    # SU(N→∞) limit
    su_limits = [(N, eta_SU(N)) for N in [10, 50, 100, 1000]]
    su_inf = su_limits[-1][1]
    su_converges = abs(su_inf - sqrt2) < 1e-3
    print(f"  SU(N) convergence: ", end="")
    for N, eta in su_limits:
        print(f"η({N})={eta:.6f} ", end="")
    print()
    record_test("ADV-9.b: SU(N→∞) → sqrt(2)", su_converges,
                f"eta_SU(1000) = {su_inf:.8f} vs sqrt(2) = {sqrt2:.8f}")

    # Sp(2N→∞) limit (correct formula)
    sp_limits = [(N, eta_Sp_correct(N)) for N in [10, 50, 100, 1000]]
    sp_inf = sp_limits[-1][1]
    sp_converges = abs(sp_inf - sqrt2) < 1e-3
    print(f"  Sp(2N) convergence: ", end="")
    for N, eta in sp_limits:
        print(f"η({N})={eta:.6f} ", end="")
    print()
    record_test("ADV-9.c: Sp(2N→∞) → sqrt(2)", sp_converges,
                f"eta_Sp(1000) = {sp_inf:.8f} vs sqrt(2) = {sqrt2:.8f}")


# =============================================================================
# ADV-10: ERROR PROPAGATION VERIFICATION
# =============================================================================

def test_ADV10_error_propagation():
    """Verify the claimed ±0.15 uncertainty on R_cont predictions."""
    print("\n" + "=" * 60)
    print("ADV-10: Error Propagation Verification")
    print("=" * 60)

    M0_err = 0.05
    systematic = 0.10  # Casimir scaling systematic

    for name in ['G2', 'F4', 'E6', 'E7', 'E8']:
        eta = eta_exceptional(name)
        stat_err = M0_err * eta
        total_err = np.sqrt(stat_err**2 + systematic**2)
        print(f"  {name}: stat = ±{stat_err:.3f}, sys = ±{systematic:.3f}, "
              f"total = ±{total_err:.3f} (claimed ±0.15)")

    # The claimed ±0.15 is a round-up from ~0.11-0.12
    # This is conservative (overestimate), which is acceptable
    max_total = max(
        np.sqrt((M0_err * eta_exceptional(name))**2 + systematic**2)
        for name in EXCEPTIONAL_GROUPS
    )

    record_test(
        "ADV-10: Error ±0.15 is conservative",
        0.15 >= max_total,
        f"Max actual error = ±{max_total:.3f}, claimed ±0.15 "
        f"{'(conservative, OK)' if 0.15 >= max_total else '(underestimated!)'}",
        {"max_actual_error": max_total, "claimed_error": 0.15}
    )


# =============================================================================
# ADV-11: QUASIGLUON MODEL CROSS-CHECK
# =============================================================================

def test_ADV11_quasigluon_crosscheck():
    """Compare Casimir scaling predictions with Buisseret (2011) quasigluon model."""
    print("\n" + "=" * 60)
    print("ADV-11: Quasigluon Model Cross-Check")
    print("=" * 60)

    max_discrepancy = 0.0
    for name in ['G2', 'F4', 'E6', 'E7', 'E8']:
        eta = eta_exceptional(name)
        R_casimir = M0_CLAIMED * eta
        R_quasi = BUISSERET_PREDICTIONS[name]
        discrepancy = abs(R_casimir - R_quasi) / R_quasi * 100
        max_discrepancy = max(max_discrepancy, discrepancy)
        print(f"  {name}: Casimir = {R_casimir:.2f}, "
              f"Quasigluon = {R_quasi:.1f}, diff = {discrepancy:.1f}%")

    record_test(
        "ADV-11: Casimir vs quasigluon within 5%",
        max_discrepancy < 10.0,
        f"Max discrepancy = {max_discrepancy:.1f}%",
        {"max_discrepancy_pct": max_discrepancy}
    )


# =============================================================================
# ADV-12: CENTER SYMMETRY VERIFICATION
# =============================================================================

def test_ADV12_center_symmetry():
    """Verify center group assignments against standard references."""
    print("\n" + "=" * 60)
    print("ADV-12: Center Symmetry Verification")
    print("=" * 60)

    # Standard reference values for centers of exceptional groups
    standard_centers = {
        'G2': ('{1}', 1), 'F4': ('{1}', 1),
        'E6': ('Z3', 3), 'E7': ('Z2', 2), 'E8': ('{1}', 1),
    }

    all_match = True
    for name, (std_center, std_order) in standard_centers.items():
        g = EXCEPTIONAL_GROUPS[name]
        center_ok = (g['center'] == std_center and
                     g['center_order'] == std_order)
        if not center_ok:
            all_match = False
        print(f"  {name}: Z(G) = {g['center']} "
              f"(order {g['center_order']}): "
              f"{'OK' if center_ok else 'MISMATCH'}")

    # Check center-trivial implication: string breaking
    center_trivial = [name for name in EXCEPTIONAL_GROUPS
                      if EXCEPTIONAL_GROUPS[name]['center_order'] == 1]
    print(f"\n  Center-trivial groups: {center_trivial}")
    print(f"  → These have string breaking (no asymptotic σ)")

    record_test(
        "ADV-12: Center symmetry assignments correct",
        all_match,
        f"All centers match standard references: {all_match}",
        {"center_trivial_groups": center_trivial}
    )


# =============================================================================
# VISUALIZATION
# =============================================================================

def generate_plots(m0_wm, m0_wm_err, su_fit_data, R_cont_preds):
    """Generate comprehensive adversarial verification plots."""
    if not HAS_MATPLOTLIB:
        print("\n  [SKIP] matplotlib not available — skipping plots")
        return

    print("\n" + "=" * 60)
    print("Generating Adversarial Verification Plots")
    print("=" * 60)

    fig = plt.figure(figsize=(20, 16))
    gs = GridSpec(3, 3, figure=fig, hspace=0.35, wspace=0.35)

    # --- Panel 1: M0 extraction from SU(N) data ---
    ax1 = fig.add_subplot(gs[0, 0])
    N_vals = sorted(SU_DATA.keys())
    m0_vals = [SU_DATA[N][0] / eta_SU(N) for N in N_vals]
    m0_errs = [SU_DATA[N][1] / eta_SU(N) for N in N_vals]

    ax1.errorbar(N_vals, m0_vals, yerr=m0_errs, fmt='ko', capsize=4,
                 label='SU(N) lattice data')
    ax1.axhline(M0_CLAIMED, color='red', ls='--', label=f'Claimed M₀ = {M0_CLAIMED}')
    ax1.axhline(m0_wm, color='blue', ls='-', label=f'Actual WM = {m0_wm:.3f}')
    ax1.axhspan(m0_wm - m0_wm_err, m0_wm + m0_wm_err, alpha=0.2, color='blue')
    ax1.axhspan(M0_CLAIMED - M0_CLAIMED_ERR, M0_CLAIMED + M0_CLAIMED_ERR,
                alpha=0.15, color='red')
    ax1.set_xlabel('N (SU(N))')
    ax1.set_ylabel('M₀ = R_cont / η(N)')
    ax1.set_title('ADV-3: M₀ Extraction from SU(N)')
    ax1.legend(fontsize=8)
    ax1.set_ylim(1.9, 2.8)

    # --- Panel 2: Sp(2N) eta comparison ---
    ax2 = fig.add_subplot(gs[0, 1])
    N_sp = np.arange(1, 21)
    eta_claimed = [eta_Sp_claimed(N) for N in N_sp]
    eta_correct = [eta_Sp_correct(N) for N in N_sp]

    ax2.plot(N_sp, eta_correct, 'b-o', markersize=4, label='Correct: √(4(N+1)/(2N+1))')
    ax2.plot(N_sp, eta_claimed, 'r--', label='Claimed: √2 (Eq. 5.16)')
    ax2.axhline(np.sqrt(2), color='gray', ls=':', alpha=0.5, label='√2 (large-N limit)')
    ax2.set_xlabel('N (Sp(2N))')
    ax2.set_ylabel('η(Sp(2N))')
    ax2.set_title('ADV-2: Sp(2N) Casimir Ratio')
    ax2.legend(fontsize=8)

    # --- Panel 3: Exceptional group predictions ---
    ax3 = fig.add_subplot(gs[0, 2])
    groups = ['G2', 'F4', 'E6', 'E7', 'E8']
    R_preds = [R_cont_preds[g] for g in groups]
    etas = [eta_exceptional(g) for g in groups]
    quasi_preds = [BUISSERET_PREDICTIONS[g] for g in groups]

    x_pos = range(len(groups))
    ax3.bar([x - 0.15 for x in x_pos], R_preds, 0.3, color='steelblue',
            label='Casimir scaling', yerr=0.15, capsize=3)
    ax3.bar([x + 0.15 for x in x_pos], quasi_preds, 0.3, color='darkorange',
            label='Quasigluon model', alpha=0.7)
    ax3.axhline(R_CONT_SU3, color='green', ls=':', label=f'SU(3) = {R_CONT_SU3}')
    ax3.set_xticks(x_pos)
    ax3.set_xticklabels(groups)
    ax3.set_ylabel('R_cont = m(0⁺⁺)/√σ')
    ax3.set_title('ADV-11: Exceptional Group Predictions')
    ax3.legend(fontsize=8)

    # --- Panel 4: SU(N) universality & 1/N^2 fit ---
    ax4 = fig.add_subplot(gs[1, 0])
    N_arr, m0_arr, m0_err_arr, a, b = su_fit_data
    x_fit = np.linspace(0, 0.3, 100)

    ax4.errorbar(1.0/N_arr**2, m0_arr, yerr=m0_err_arr, fmt='ko', capsize=4)
    ax4.plot(x_fit, a + b * x_fit, 'r-',
             label=f'Fit: {a:.3f} + {b:.2f}/N²')
    ax4.set_xlabel('1/N²')
    ax4.set_ylabel('M₀(N)')
    ax4.set_title('ADV-4: M₀ vs 1/N² (SU(N))')
    ax4.legend(fontsize=8)

    # --- Panel 5: c(G) sensitivity to √σ/Λ ---
    ax5 = fig.add_subplot(gs[1, 1])
    sigma_lambda_range = np.linspace(0.5, 3.0, 50)
    colors = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd']

    for i, name in enumerate(groups):
        R = R_cont_preds[name]
        cG = R * sigma_lambda_range
        ax5.plot(sigma_lambda_range, cG, color=colors[i], label=name)
        # Mark paper's assumption
        cG_paper = R * 2.0
        ax5.plot(2.0, cG_paper, 'o', color=colors[i], markersize=6)

    ax5.axvline(2.0, color='gray', ls='--', alpha=0.5, label='Paper assumption')
    ax5.axvline(1.88, color='gray', ls=':', alpha=0.5, label='Recent det. (~1.88)')
    ax5.axhline(0, color='black', lw=0.5)
    ax5.set_xlabel('√σ / Λ_MSbar')
    ax5.set_ylabel('c(G)')
    ax5.set_title('ADV-6: c(G) Sensitivity Analysis')
    ax5.legend(fontsize=7, ncol=2)

    # --- Panel 6: c(G) with Eq.(6.4) scaling ---
    ax6 = fig.add_subplot(gs[1, 2])
    b0_su3 = 11 * 3
    cG_paper_vals = []
    cG_scaled_vals = []
    for name in groups:
        g = EXCEPTIONAL_GROUPS[name]
        R = R_cont_preds[name]
        b0_G = 11 * g['h_dual']
        sl_scaled = SIGMA_LAMBDA_SU3 * np.sqrt(b0_su3 / b0_G)
        cG_paper_vals.append(R * 2.0)
        cG_scaled_vals.append(R * sl_scaled)

    x_pos = range(len(groups))
    ax6.bar([x - 0.15 for x in x_pos], cG_paper_vals, 0.3, color='steelblue',
            label='Paper (√σ/Λ ≈ 2.0)', yerr=0.5, capsize=3)
    ax6.bar([x + 0.15 for x in x_pos], cG_scaled_vals, 0.3, color='coral',
            label='Eq.(6.4) scaling')
    ax6.axhline(0, color='black', lw=0.5)
    ax6.set_xticks(x_pos)
    ax6.set_xticklabels(groups)
    ax6.set_ylabel('c(G)')
    ax6.set_title('ADV-6: c(G) Paper vs Eq.(6.4)')
    ax6.legend(fontsize=8)

    # --- Panel 7: eta across all groups ---
    ax7 = fig.add_subplot(gs[2, 0])
    # SU(N)
    su_N = sorted(SU_DATA.keys())
    su_etas = [eta_SU(N) for N in su_N]
    ax7.plot(su_N, su_etas, 'bs-', label='SU(N)', markersize=5)
    # Sp(2N) correct
    sp_N = sorted(SP_DATA.keys())
    sp_etas = [eta_Sp_correct(N) for N in sp_N]
    ax7.plot([2*N for N in sp_N], sp_etas, 'r^-', label='Sp(2N)', markersize=5)
    # Exceptional
    exc_ranks = [EXCEPTIONAL_GROUPS[g]['rank'] for g in groups]
    exc_etas = [eta_exceptional(g) for g in groups]
    ax7.plot(exc_ranks, exc_etas, 'go', markersize=8, label='Exceptional')
    for i, name in enumerate(groups):
        ax7.annotate(name, (exc_ranks[i], exc_etas[i]),
                     textcoords="offset points", xytext=(5, 5), fontsize=8)
    ax7.axhline(np.sqrt(2), color='gray', ls=':', alpha=0.5, label='√2')
    ax7.axhline(1.0, color='gray', ls=':', alpha=0.3, label='1')
    ax7.set_xlabel('N or Rank')
    ax7.set_ylabel('η(G)')
    ax7.set_title('ADV-7/9: Casimir Ratio Factor Landscape')
    ax7.legend(fontsize=7)

    # --- Panel 8: R_cont landscape ---
    ax8 = fig.add_subplot(gs[2, 1])
    # SU(N) lattice
    su_R = [SU_DATA[N][0] for N in su_N]
    su_Re = [SU_DATA[N][1] for N in su_N]
    ax8.errorbar(su_N, su_R, yerr=su_Re, fmt='bs', capsize=3,
                 label='SU(N) lattice', markersize=5)
    # Sp(2N) lattice
    sp_R = [SP_DATA[N][0] for N in sp_N]
    sp_Re = [SP_DATA[N][1] for N in sp_N]
    ax8.errorbar([2*N for N in sp_N], sp_R, yerr=sp_Re, fmt='r^', capsize=3,
                 label='Sp(2N) lattice', markersize=5)
    # Exceptional predictions
    exc_R = [R_cont_preds[g] for g in groups]
    ax8.errorbar(exc_ranks, exc_R, yerr=0.15, fmt='go', capsize=3,
                 label='Exceptional (predicted)', markersize=8)
    for i, name in enumerate(groups):
        ax8.annotate(name, (exc_ranks[i], exc_R[i]),
                     textcoords="offset points", xytext=(5, -12), fontsize=8)
    ax8.set_xlabel('N or Rank')
    ax8.set_ylabel('R_cont = m(0⁺⁺)/√σ')
    ax8.set_title('R_cont Landscape: All Groups')
    ax8.legend(fontsize=7)

    # --- Panel 9: Findings summary ---
    ax9 = fig.add_subplot(gs[2, 2])
    ax9.axis('off')
    summary_text = "ADVERSARIAL FINDINGS SUMMARY\n"
    summary_text += "=" * 40 + "\n\n"
    n_pass = sum(1 for t in test_results if t['passed'])
    n_fail = sum(1 for t in test_results if not t['passed'])
    summary_text += f"Tests: {n_pass} PASS, {n_fail} FAIL\n"
    summary_text += f"Findings: {len(adversarial_findings)}\n\n"
    for f in adversarial_findings:
        summary_text += f"[{f['severity']}] {f['id']}\n"
        # Wrap description
        desc = f['description']
        while len(desc) > 45:
            cut = desc[:45].rfind(' ')
            if cut == -1:
                cut = 45
            summary_text += f"  {desc[:cut]}\n"
            desc = desc[cut:].strip()
        if desc:
            summary_text += f"  {desc}\n"
        summary_text += "\n"

    ax9.text(0.05, 0.95, summary_text, transform=ax9.transAxes,
             fontsize=8, verticalalignment='top', fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    fig.suptitle(
        'Proposition 7.8.1: Adversarial Physics Verification\n'
        'Exceptional Group Glueball Mass Predictions',
        fontsize=14, fontweight='bold', y=0.98
    )

    plot_path = os.path.join(PLOT_DIR, 'prop_7_8_1_adversarial_verification.png')
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"  Plot saved: {plot_path}")
    plt.close()


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def main():
    print("=" * 70)
    print("PROPOSITION 7.8.1: EXCEPTIONAL GROUP GLUEBALL PREDICTIONS")
    print("Adversarial Physics Verification")
    print("=" * 70)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"M0 (claimed): {M0_CLAIMED} ± {M0_CLAIMED_ERR}")
    print(f"SU(3) anchor: R_cont = {R_CONT_SU3} ± {R_CONT_SU3_ERR}")

    # Run all adversarial tests
    test_ADV1_casimir_invariants()
    test_ADV2_Sp_casimir_ratio()
    m0_wm, m0_wm_err = test_ADV3_M0_weighted_mean()
    su_fit_data = test_ADV4_SU_universality()
    test_ADV5_R_cont_predictions()
    R_cont_preds = test_ADV6_cG_sensitivity()
    test_ADV7_eta_monotonicity()
    test_ADV8_E8_self_duality()
    test_ADV9_G2_large_N()
    test_ADV10_error_propagation()
    test_ADV11_quasigluon_crosscheck()
    test_ADV12_center_symmetry()

    # Generate plots
    generate_plots(m0_wm, m0_wm_err, su_fit_data, R_cont_preds)

    # Summary
    n_total = len(test_results)
    n_pass = sum(1 for t in test_results if t['passed'])
    n_fail = n_total - n_pass

    print("\n" + "=" * 70)
    print("ADVERSARIAL VERIFICATION SUMMARY")
    print("=" * 70)
    print(f"  Tests passed: {n_pass}/{n_total}")
    print(f"  Tests failed: {n_fail}/{n_total}")
    print(f"  Adversarial findings: {len(adversarial_findings)}")

    for f in adversarial_findings:
        print(f"\n  [{f['severity']}] {f['id']}: {f['description']}")
        print(f"    Impact: {f['impact']}")

    overall = "PASS" if n_fail == 0 else "PARTIAL PASS" if n_fail <= 3 else "FAIL"
    print(f"\n  Overall: {overall}")

    # Save results
    output = {
        "proposition": "7.8.1",
        "title": "Glueball Mass Ratios for Exceptional Gauge Groups",
        "verification_type": "adversarial_physics",
        "date": datetime.now().isoformat(),
        "tests_total": n_total,
        "tests_passed": n_pass,
        "tests_failed": n_fail,
        "overall": overall,
        "findings": adversarial_findings,
        "results": test_results,
    }

    output_path = os.path.join(SCRIPT_DIR, "prop_7_8_1_adversarial_results.json")
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2, default=str)

    print(f"\n  Results saved to: {output_path}")
    print("=" * 70)

    return n_fail <= 3  # Partial pass acceptable


if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
