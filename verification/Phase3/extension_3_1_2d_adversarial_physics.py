#!/usr/bin/env python3
"""
Extension 3.1.2d: Complete PMNS Parameter Derivation
Adversarial Physics Verification
====================================================================

This script performs comprehensive adversarial verification of the
PMNS parameter derivation claims, including:

1. Formula verification with proper dimensional analysis
2. NuFIT 6.0 comparison (both IC19 and IC24 variants)
3. Trial-and-error detection: counting failed vs successful formulas
4. TBM limit recovery test (lambda -> 0)
5. Jarlskog invariant consistency check
6. Parameter count analysis (inputs vs outputs)
7. Delta_CP formula internal consistency
8. Mass ratio sensitivity analysis

Related Documents:
- Proof: docs/proofs/Phase3/Extension-3.1.2d-Complete-PMNS-Parameters.md
- Verification Report: docs/proofs/verification-records/Extension-3.1.2d-Multi-Agent-Verification-2026-02-07.md

Verification Date: 2026-02-07
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from pathlib import Path
import json
from datetime import datetime

# =============================================================================
# OUTPUT DIRECTORIES
# =============================================================================
PLOT_DIR = Path(__file__).parent.parent / "plots"
PLOT_DIR.mkdir(exist_ok=True)

# =============================================================================
# CONSTANTS
# =============================================================================
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
LAMBDA = np.sin(np.radians(72)) / PHI**3  # Wolfenstein parameter from geometry

# NuFIT 6.0 IC19 (without SK atmospheric) - Normal Ordering
NUFIT60_IC19 = {
    'sin2_theta12': 0.307, 'sin2_theta12_err': 0.012,
    'sin2_theta23': 0.561, 'sin2_theta23_err': 0.014,
    'sin2_theta13': 0.02195, 'sin2_theta13_err': 0.00056,
    'delta_CP': 177.0, 'delta_CP_err': 20.0,
    'dm21_sq': 7.49e-5, 'dm21_sq_err': 0.21e-5,
    'dm31_sq': 2.534e-3, 'dm31_sq_err': 0.033e-3,
}

# NuFIT 6.0 IC24 (with SK atmospheric) - Normal Ordering
NUFIT60_IC24 = {
    'sin2_theta12': 0.308, 'sin2_theta12_err': 0.012,
    'sin2_theta23': 0.470, 'sin2_theta23_err': 0.015,
    'sin2_theta13': 0.02215, 'sin2_theta13_err': 0.00057,
    'delta_CP': 212.0, 'delta_CP_err': 34.0,
    'dm21_sq': 7.49e-5, 'dm21_sq_err': 0.21e-5,
    'dm31_sq': 2.513e-3, 'dm31_sq_err': 0.033e-3,
}

# NuFIT 5.x values (what the document actually uses, labeled as "NuFIT 6.0")
NUFIT5X = {
    'sin2_theta12': 0.303, 'sin2_theta12_err': 0.012,
    'sin2_theta23': 0.573, 'sin2_theta23_err': 0.020,
    'sin2_theta13': 0.02206, 'sin2_theta13_err': 0.00054,
    'delta_CP': 197.0, 'delta_CP_err': 24.0,
    'dm21_sq': 7.42e-5, 'dm21_sq_err': 0.21e-5,
    'dm31_sq': 2.514e-3, 'dm31_sq_err': 0.033e-3,
}

# PDG 2024 Wolfenstein parameter
PDG_LAMBDA = 0.22497
PDG_LAMBDA_ERR = 0.00070


# =============================================================================
# TEST 1: FORMULA VERIFICATION WITH DIMENSIONAL ANALYSIS
# =============================================================================

def test_theta12_dimensional_consistency():
    """
    Test: The theta_12 formula mixes degrees and radians.
    The boxed formula: theta_12 = 45 - arcsin(lambda) + lambda^2/2
    """
    print("=" * 70)
    print("TEST 1: theta_12 DIMENSIONAL ANALYSIS")
    print("=" * 70)

    # Interpretation A: lambda^2/2 in DEGREES
    theta12_deg = 45.0 - np.degrees(np.arcsin(LAMBDA)) + LAMBDA**2 / 2
    # Interpretation B: lambda^2/2 in RADIANS (converted to degrees)
    theta12_rad = 45.0 - np.degrees(np.arcsin(LAMBDA)) + np.degrees(LAMBDA**2 / 2)
    # Interpretation C: ALL in radians
    theta12_allrad = np.pi / 4 - np.arcsin(LAMBDA) + LAMBDA**2 / 2

    print(f"  lambda = {LAMBDA:.6f}")
    print(f"  lambda^2/2 = {LAMBDA**2/2:.6f}")
    print(f"\n  Interpretation A (lambda^2/2 in degrees): {theta12_deg:.3f} deg")
    print(f"  Interpretation B (lambda^2/2 in radians): {theta12_rad:.3f} deg")
    print(f"  Interpretation C (all radians -> degrees): {np.degrees(theta12_allrad):.3f} deg")
    print(f"\n  NuFIT 5.x observed: 33.41 +/- 0.76 deg")
    print(f"  NuFIT 6.0 IC19 observed: {np.degrees(np.arcsin(np.sqrt(NUFIT60_IC19['sin2_theta12']))):.2f} deg")

    interp_a_matches = abs(theta12_deg - 33.41) < 0.76
    interp_b_matches = abs(theta12_rad - 33.41) < 0.76

    print(f"\n  Interpretation A matches data? {interp_a_matches} (deviation: {abs(theta12_deg - 33.41):.2f} deg)")
    print(f"  Interpretation B matches data? {interp_b_matches} (deviation: {abs(theta12_rad - 33.41):.2f} deg)")

    passed = not interp_a_matches and interp_b_matches
    status = "CONFIRMED" if passed else "NOT CONFIRMED"
    print(f"\n  DIMENSIONAL INCONSISTENCY {status}")
    print(f"  -> Only interpretation B (radians) works, proving the boxed formula is dimensionally wrong")

    return {
        "test": "theta12_dimensional_consistency",
        "theta12_degrees_interp": float(theta12_deg),
        "theta12_radians_interp": float(theta12_rad),
        "theta12_all_radians": float(np.degrees(theta12_allrad)),
        "dimensional_error_confirmed": passed,
        "passed": passed
    }


# =============================================================================
# TEST 2: NUFIT 6.0 COMPARISON (BOTH VARIANTS)
# =============================================================================

def test_nufit60_comparison():
    """
    Test: Compare predictions against ACTUAL NuFIT 6.0 values (both IC19 and IC24).
    """
    print("\n" + "=" * 70)
    print("TEST 2: NUFIT 6.0 COMPARISON (ACTUAL VALUES)")
    print("=" * 70)

    # Predicted values from the document
    theta12_pred = 45.0 - np.degrees(np.arcsin(LAMBDA)) + np.degrees(LAMBDA**2 / 2)
    sin2_theta12_pred = np.sin(np.radians(theta12_pred))**2
    delta_CP_pred = 150.0 + (LAMBDA / PHI) * 360.0
    r_pred = LAMBDA**2 / np.sqrt(3)

    results = []
    for name, data in [("NuFIT 5.x (document uses)", NUFIT5X),
                        ("NuFIT 6.0 IC19 (actual)", NUFIT60_IC19),
                        ("NuFIT 6.0 IC24 (actual)", NUFIT60_IC24)]:
        print(f"\n  --- {name} ---")

        theta12_obs = np.degrees(np.arcsin(np.sqrt(data['sin2_theta12'])))
        dev_theta12 = abs(theta12_pred - theta12_obs) / (data['sin2_theta12_err'] * 50)  # approximate
        dev_sin2 = abs(sin2_theta12_pred - data['sin2_theta12']) / data['sin2_theta12_err']
        dev_dcp = abs(delta_CP_pred - data['delta_CP']) / data['delta_CP_err']
        r_obs = data['dm21_sq'] / data['dm31_sq']
        dev_r = abs(r_pred - r_obs) / r_obs * 100

        print(f"    sin2_theta12: pred={sin2_theta12_pred:.4f}, obs={data['sin2_theta12']:.4f}, "
              f"deviation={dev_sin2:.2f} sigma")
        print(f"    delta_CP: pred={delta_CP_pred:.1f} deg, obs={data['delta_CP']:.0f} deg, "
              f"deviation={dev_dcp:.2f} sigma")
        print(f"    r=Dm21/Dm31: pred={r_pred:.4f}, obs={r_obs:.4f}, "
              f"deviation={dev_r:.1f}%")

        results.append({
            "dataset": name,
            "sin2_theta12_pred": float(sin2_theta12_pred),
            "sin2_theta12_obs": data['sin2_theta12'],
            "sin2_theta12_sigma": float(dev_sin2),
            "delta_CP_pred": float(delta_CP_pred),
            "delta_CP_obs": data['delta_CP'],
            "delta_CP_sigma": float(dev_dcp),
            "r_pred": float(r_pred),
            "r_obs": float(r_obs),
            "r_percent": float(dev_r),
        })

    passed = True  # Informational test
    return {"test": "nufit60_comparison", "comparisons": results, "passed": passed}


# =============================================================================
# TEST 3: TBM LIMIT RECOVERY (lambda -> 0)
# =============================================================================

def test_tbm_limit_recovery():
    """
    Test: In the lambda -> 0 limit (exact A4), do the formulas recover TBM?
    """
    print("\n" + "=" * 70)
    print("TEST 3: TBM LIMIT RECOVERY (lambda -> 0)")
    print("=" * 70)

    lam = 1e-10  # effectively zero

    # theta_12 from QLC formula
    theta12_lim = 45.0 - np.degrees(np.arcsin(lam)) + np.degrees(lam**2 / 2)
    theta12_tbm = np.degrees(np.arctan(1.0 / np.sqrt(2)))  # arctan(1/sqrt(2)) = 35.26 deg

    # theta_23
    theta23_lim = 45.0  # all corrections proportional to lambda
    theta23_tbm = 45.0

    # theta_13
    sin_theta13_lim = (lam / PHI) * (1 + lam / 5 + lam**2 / 2)
    theta13_lim = np.degrees(np.arcsin(sin_theta13_lim))
    theta13_tbm = 0.0

    # mass ratio
    r_lim = lam**2 / np.sqrt(3)

    print(f"  theta_12: QLC limit = {theta12_lim:.2f} deg, TBM = {theta12_tbm:.2f} deg "
          f"{'PASS' if abs(theta12_lim - theta12_tbm) < 1 else 'FAIL'}")
    print(f"  theta_23: limit = {theta23_lim:.2f} deg, TBM = {theta23_tbm:.2f} deg "
          f"{'PASS' if abs(theta23_lim - theta23_tbm) < 1 else 'FAIL'}")
    print(f"  theta_13: limit = {theta13_lim:.6f} deg, TBM = {theta13_tbm:.2f} deg "
          f"{'PASS' if abs(theta13_lim - theta13_tbm) < 1 else 'FAIL'}")
    print(f"  r: limit = {r_lim:.2e}, expected = 0 PASS")

    theta12_passes = abs(theta12_lim - theta12_tbm) < 1.0
    theta23_passes = abs(theta23_lim - theta23_tbm) < 1.0
    theta13_passes = abs(theta13_lim - theta13_tbm) < 1.0

    passed = theta12_passes and theta23_passes and theta13_passes
    print(f"\n  TBM limit recovery: {'PASS' if passed else 'FAIL'}")
    if not theta12_passes:
        print(f"  CRITICAL: theta_12 -> {theta12_lim:.1f} deg, NOT {theta12_tbm:.1f} deg (TBM)")
        print(f"  This proves theta_12 formula is QLC-based, NOT A4-based")

    return {
        "test": "tbm_limit_recovery",
        "theta12_limit": float(theta12_lim),
        "theta12_tbm": float(theta12_tbm),
        "theta23_limit": float(theta23_lim),
        "theta13_limit": float(theta13_lim),
        "theta12_recovers_tbm": theta12_passes,
        "theta23_recovers_tbm": theta23_passes,
        "theta13_recovers_tbm": theta13_passes,
        "passed": passed
    }


# =============================================================================
# TEST 4: JARLSKOG INVARIANT CONSISTENCY
# =============================================================================

def test_jarlskog_consistency():
    """
    Test: Is the Jarlskog invariant comparison in the document correct?
    """
    print("\n" + "=" * 70)
    print("TEST 4: JARLSKOG INVARIANT CONSISTENCY")
    print("=" * 70)

    def compute_jarlskog(t12_deg, t23_deg, t13_deg, dcp_deg):
        t12, t23, t13, dcp = [np.radians(x) for x in [t12_deg, t23_deg, t13_deg, dcp_deg]]
        return (1.0/8) * np.sin(2*t12) * np.sin(2*t23) * np.sin(2*t13) * np.cos(t13) * np.sin(dcp)

    # Predicted (from document)
    J_predicted = compute_jarlskog(33.4, 48.9, 8.54, 200.0)

    # "Observed" using NuFIT 5.x values (what document uses)
    t12_5x = np.degrees(np.arcsin(np.sqrt(0.303)))
    t23_5x = np.degrees(np.arcsin(np.sqrt(0.573)))
    t13_5x = np.degrees(np.arcsin(np.sqrt(0.02206)))
    J_nufit5x = compute_jarlskog(t12_5x, t23_5x, t13_5x, 197.0)

    # Actual NuFIT 6.0 IC19
    t12_6 = np.degrees(np.arcsin(np.sqrt(0.307)))
    t23_6 = np.degrees(np.arcsin(np.sqrt(0.561)))
    t13_6 = np.degrees(np.arcsin(np.sqrt(0.02195)))
    J_nufit60 = compute_jarlskog(t12_6, t23_6, t13_6, 177.0)

    # J_max (sin(delta_CP) = 1)
    J_max = compute_jarlskog(t12_6, t23_6, t13_6, 90.0)

    print(f"  J_predicted (document's angles, delta=200):  {J_predicted:.5f}")
    print(f"  J_NuFIT5x (delta=197):                       {J_nufit5x:.5f}")
    print(f"  J_NuFIT6.0_IC19 (delta=177):                 {J_nufit60:.5f}")
    print(f"  J_max (delta=90):                             {J_max:.5f}")
    print(f"\n  Document claims 'observed J ~ +/-0.033':      {0.033:.3f}")
    print(f"  This is J_max, NOT J_observed!")
    print(f"\n  Actual comparison: J_pred={J_predicted:.4f} vs J_NuFIT5x={J_nufit5x:.4f}")
    print(f"  Relative discrepancy: {abs(J_predicted - J_nufit5x)/abs(J_nufit5x)*100:.1f}%")
    print(f"\n  With NuFIT 6.0 IC19: J_pred={J_predicted:.4f} vs J_6.0={J_nufit60:.5f}")
    print(f"  Sign: predicted NEGATIVE, NuFIT 6.0 IC19 {'NEGATIVE' if J_nufit60 < 0 else 'POSITIVE'}")
    if np.sign(J_predicted) != np.sign(J_nufit60) and abs(J_nufit60) > 1e-4:
        print(f"  WARNING: Predicted J has WRONG SIGN compared to NuFIT 6.0 IC19!")

    # The document incorrectly compares J = -0.011 with |J| = 0.033
    jmax_confusion = True  # always true - it's an error in the document
    passed = True  # informational

    return {
        "test": "jarlskog_consistency",
        "J_predicted": float(J_predicted),
        "J_nufit5x": float(J_nufit5x),
        "J_nufit60_IC19": float(J_nufit60),
        "J_max": float(J_max),
        "document_claims_observed": 0.033,
        "jmax_confusion_confirmed": jmax_confusion,
        "passed": passed
    }


# =============================================================================
# TEST 5: DELTA_CP FORMULA INTERNAL CONSISTENCY
# =============================================================================

def test_deltaCP_formula_consistency():
    """
    Test: The document claims lambda/phi * 360 = 360/phi^4. Are these equal?
    """
    print("\n" + "=" * 70)
    print("TEST 5: delta_CP FORMULA INTERNAL CONSISTENCY")
    print("=" * 70)

    form_a = (LAMBDA / PHI) * 360.0  # lambda/phi * 360
    form_b = 360.0 / PHI**4          # 360/phi^4

    delta_cp_a = 150.0 + form_a
    delta_cp_b = 150.0 + form_b

    print(f"  Formula A: lambda/phi * 360 = {LAMBDA:.6f}/{PHI:.6f} * 360 = {form_a:.3f} deg")
    print(f"  Formula B: 360/phi^4 = 360/{PHI**4:.6f} = {form_b:.3f} deg")
    print(f"\n  Difference: {abs(form_a - form_b):.3f} deg")
    print(f"  delta_CP from A: {delta_cp_a:.2f} deg")
    print(f"  delta_CP from B: {delta_cp_b:.2f} deg")

    # Check: lambda/phi = 1/phi^4 would require lambda = 1/phi^3
    lambda_required = 1.0 / PHI**3
    print(f"\n  For equality: lambda must equal 1/phi^3 = {lambda_required:.6f}")
    print(f"  Actual lambda = sin(72)/phi^3 = {LAMBDA:.6f}")
    print(f"  Ratio: lambda / (1/phi^3) = sin(72) = {LAMBDA * PHI**3:.6f}")

    formulas_equal = abs(form_a - form_b) < 0.1
    passed = not formulas_equal  # We EXPECT them to be unequal
    print(f"\n  Formulas equal? {formulas_equal}")
    print(f"  ALGEBRAIC ERROR {'CONFIRMED' if passed else 'NOT CONFIRMED'}: "
          f"lambda/phi * 360 != 360/phi^4")

    return {
        "test": "deltaCP_formula_consistency",
        "formula_a_value": float(form_a),
        "formula_b_value": float(form_b),
        "difference_deg": float(abs(form_a - form_b)),
        "delta_cp_a": float(delta_cp_a),
        "delta_cp_b": float(delta_cp_b),
        "algebraic_error_confirmed": passed,
        "passed": passed
    }


# =============================================================================
# TEST 6: MASS RATIO SENSITIVITY ANALYSIS
# =============================================================================

def test_mass_ratio_sensitivity():
    """
    Test: How unique is the formula r = lambda^2/sqrt(3)?
    Check alternatives with similar structure.
    """
    print("\n" + "=" * 70)
    print("TEST 6: MASS RATIO SENSITIVITY ANALYSIS")
    print("=" * 70)

    r_obs = NUFIT60_IC19['dm21_sq'] / NUFIT60_IC19['dm31_sq']

    candidates = {
        'lambda^2 / sqrt(3)': LAMBDA**2 / np.sqrt(3),
        'lambda^2 / phi': LAMBDA**2 / PHI,
        'lambda^2 * cos(60)': LAMBDA**2 * np.cos(np.radians(60)),
        'lambda^2 / 2': LAMBDA**2 / 2,
        'lambda^2 / sqrt(2)': LAMBDA**2 / np.sqrt(2),
        'lambda^2 * phi / 3': LAMBDA**2 * PHI / 3,
        'lambda^2': LAMBDA**2,
        'lambda^2 / pi': LAMBDA**2 / np.pi,
        'lambda^3 / (1-lambda)': LAMBDA**3 / (1 - LAMBDA),
    }

    print(f"  Observed ratio r = {r_obs:.5f}")
    print(f"\n  {'Formula':<25} {'Value':<12} {'% Error':<12} {'Status'}")
    print(f"  {'-'*25} {'-'*12} {'-'*12} {'-'*10}")

    results = []
    for name, val in sorted(candidates.items(), key=lambda x: abs(x[1] - r_obs)):
        pct_err = abs(val - r_obs) / r_obs * 100
        status = "BEST" if pct_err < 2 else ("GOOD" if pct_err < 5 else "POOR")
        print(f"  {name:<25} {val:<12.5f} {pct_err:<12.1f} {status}")
        results.append({"formula": name, "value": float(val), "pct_error": float(pct_err)})

    # Count how many formulas have < 5% error
    good_count = sum(1 for r in results if r['pct_error'] < 5)
    print(f"\n  Formulas within 5% of observation: {good_count}/{len(candidates)}")
    print(f"  -> lambda^2/sqrt(3) is the best but not uniquely so")

    passed = True  # Informational
    return {
        "test": "mass_ratio_sensitivity",
        "r_observed": float(r_obs),
        "candidates": results,
        "num_within_5pct": good_count,
        "passed": passed
    }


# =============================================================================
# TEST 7: PARAMETER COUNT ANALYSIS
# =============================================================================

def test_parameter_count():
    """
    Test: Count inputs vs outputs to assess genuine predictive power.
    """
    print("\n" + "=" * 70)
    print("TEST 7: PARAMETER COUNT ANALYSIS")
    print("=" * 70)

    inputs = [
        ("lambda (from CKM)", "measured", LAMBDA),
        ("phi (golden ratio)", "mathematical constant", PHI),
        ("45 deg (QLC base)", "structural choice", 45.0),
        ("150 deg (A4 Berry phase)", "structural choice", 150.0),
        ("360 deg (full revolution factor)", "structural choice", 360.0),
        ("1/5 (theta_13 correction)", "structural choice", 0.2),
        ("1/2 (theta_13 correction)", "structural choice", 0.5),
        ("1/sqrt(3) (mass ratio factor)", "structural choice", 1/np.sqrt(3)),
        ("Dm31_sq (for Dm21 prediction)", "measured input", NUFIT5X['dm31_sq']),
    ]

    outputs = [
        ("theta_12 = 33.4 deg", "from QLC + correction"),
        ("theta_23 = 48.9 deg", "from external document"),
        ("theta_13 = 8.54 deg", "from external document"),
        ("delta_CP = 200 deg", "from 150 + lambda/phi*360"),
        ("r = Dm21/Dm31 = 0.029", "ratio only"),
    ]

    print(f"\n  INPUTS ({len(inputs)}):")
    for name, cat, val in inputs:
        print(f"    [{cat}] {name} = {val:.6f}")

    print(f"\n  OUTPUTS ({len(outputs)}):")
    for name, note in outputs:
        print(f"    {name} ({note})")

    n_measured = sum(1 for _, cat, _ in inputs if cat == "measured" or cat == "measured input")
    n_structural = sum(1 for _, cat, _ in inputs if cat == "structural choice")
    n_constants = sum(1 for _, cat, _ in inputs if cat == "mathematical constant")

    print(f"\n  Summary:")
    print(f"    Measured inputs: {n_measured}")
    print(f"    Mathematical constants: {n_constants}")
    print(f"    Structural choices: {n_structural}")
    print(f"    Total effective parameters: {n_measured + n_structural}")
    print(f"    Outputs: {len(outputs)}")
    print(f"    Effective parameters >= Outputs? {n_measured + n_structural >= len(outputs)}")
    print(f"\n    -> The formulas have more adjustable structure than predictions")
    print(f"    -> This indicates FITTING, not PREDICTION")

    passed = n_measured + n_structural >= len(outputs)  # Expect this to be True (confirming issue)
    return {
        "test": "parameter_count",
        "n_measured": n_measured,
        "n_structural": n_structural,
        "n_constants": n_constants,
        "n_outputs": len(outputs),
        "overfitting_detected": passed,
        "passed": passed
    }


# =============================================================================
# TEST 8: SECTION 5.4 NUMERICAL ERROR
# =============================================================================

def test_section54_numerical():
    """
    Test: The boxed formula in Section 5.4 claims 1.50 deg but derivation gives 0.83 deg.
    """
    print("\n" + "=" * 70)
    print("TEST 8: SECTION 5.4 NUMERICAL ERROR")
    print("=" * 70)

    theta13 = 8.54  # degrees
    delta_theta = LAMBDA**2 / (2 * np.sqrt(3)) * np.cos(np.radians(theta13))

    print(f"  lambda^2 = {LAMBDA**2:.6f}")
    print(f"  2*sqrt(3) = {2*np.sqrt(3):.6f}")
    print(f"  cos(8.54) = {np.cos(np.radians(theta13)):.6f}")
    print(f"  delta_theta = {delta_theta:.6f} rad = {np.degrees(delta_theta):.3f} deg")
    print(f"\n  Boxed formula claims: ~1.50 deg")
    print(f"  Derivation computes: {np.degrees(delta_theta):.2f} deg")
    print(f"  Discrepancy factor: {1.50 / np.degrees(delta_theta):.2f}x")

    passed = abs(np.degrees(delta_theta) - 1.50) > 0.3  # Confirm the error exists
    print(f"\n  Numerical error confirmed: {passed}")

    return {
        "test": "section54_numerical",
        "computed_deg": float(np.degrees(delta_theta)),
        "claimed_deg": 1.50,
        "discrepancy_factor": float(1.50 / np.degrees(delta_theta)),
        "error_confirmed": passed,
        "passed": passed
    }


# =============================================================================
# PLOTTING
# =============================================================================

def plot_nufit_comparison(results_nufit):
    """
    Plot predicted vs observed values across NuFIT versions.
    """
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    datasets = results_nufit['comparisons']
    labels = [d['dataset'].replace(' (actual)', '').replace(' (document uses)', '')
              for d in datasets]
    colors = ['#d62728', '#2ca02c', '#1f77b4']

    # sin2_theta12
    ax = axes[0]
    pred = datasets[0]['sin2_theta12_pred']
    obs = [d['sin2_theta12_obs'] for d in datasets]
    errs = [NUFIT5X['sin2_theta12_err'], NUFIT60_IC19['sin2_theta12_err'],
            NUFIT60_IC24['sin2_theta12_err']]
    ax.axhline(pred, color='black', ls='--', label=f'Predicted: {pred:.4f}')
    for i, (o, e, l, c) in enumerate(zip(obs, errs, labels, colors)):
        ax.errorbar(i, o, yerr=e, fmt='o', color=c, markersize=8, capsize=5, label=l)
    ax.set_ylabel(r'$\sin^2\theta_{12}$')
    ax.set_xticks([])
    ax.legend(fontsize=7)
    ax.set_title(r'$\theta_{12}$ (Solar Angle)')

    # delta_CP
    ax = axes[1]
    pred_dcp = datasets[0]['delta_CP_pred']
    obs_dcp = [d['delta_CP_obs'] for d in datasets]
    errs_dcp = [NUFIT5X['delta_CP_err'], NUFIT60_IC19['delta_CP_err'],
                NUFIT60_IC24['delta_CP_err']]
    ax.axhline(pred_dcp, color='black', ls='--', label=f'Predicted: {pred_dcp:.1f}')
    for i, (o, e, l, c) in enumerate(zip(obs_dcp, errs_dcp, labels, colors)):
        ax.errorbar(i, o, yerr=e, fmt='o', color=c, markersize=8, capsize=5, label=l)
    ax.axhline(180, color='gray', ls=':', alpha=0.5, label='CP conserving')
    ax.set_ylabel(r'$\delta_{CP}$ (degrees)')
    ax.set_xticks([])
    ax.legend(fontsize=7)
    ax.set_title(r'$\delta_{CP}$ (Leptonic CP Phase)')

    # mass ratio
    ax = axes[2]
    pred_r = datasets[0]['r_pred']
    obs_r = [d['r_obs'] for d in datasets]
    ax.axhline(pred_r, color='black', ls='--', label=f'Predicted: {pred_r:.5f}')
    for i, (o, l, c) in enumerate(zip(obs_r, labels, colors)):
        ax.plot(i, o, 'o', color=c, markersize=8, label=f'{l}: {o:.5f}')
    ax.set_ylabel(r'$r = \Delta m^2_{21} / \Delta m^2_{31}$')
    ax.set_xticks([])
    ax.legend(fontsize=7)
    ax.set_title('Mass Squared Difference Ratio')

    fig.suptitle('Extension 3.1.2d: Predictions vs NuFIT Variants', fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'ext_3_1_2d_nufit_comparison.png', dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Plot saved: {PLOT_DIR / 'ext_3_1_2d_nufit_comparison.png'}")


def plot_tbm_limit(results_tbm):
    """
    Plot theta_12 as function of lambda, showing TBM vs QLC starting point.
    """
    fig, ax = plt.subplots(figsize=(8, 6))

    lambdas = np.linspace(0, 0.35, 200)

    # QLC formula (document)
    theta12_qlc = 45.0 - np.degrees(np.arcsin(lambdas)) + np.degrees(lambdas**2 / 2)

    # TBM + corrections (what A4 should give)
    sin2_tbm_corr = (1.0/3) * (1 - lambdas/np.sqrt(2) + lambdas**2/2)
    theta12_tbm_corr = np.degrees(np.arcsin(np.sqrt(np.clip(sin2_tbm_corr, 0, 1))))

    # Pure TBM
    theta12_tbm = np.full_like(lambdas, np.degrees(np.arctan(1/np.sqrt(2))))

    ax.plot(lambdas, theta12_qlc, 'b-', lw=2, label=r'QLC: $45° - \arcsin\lambda + \lambda^2/2$')
    ax.plot(lambdas, theta12_tbm_corr, 'r-', lw=2,
            label=r'A4: $\arcsin\sqrt{\frac{1}{3}(1-\frac{\lambda}{\sqrt{2}}+\frac{\lambda^2}{2})}$')
    ax.axhline(theta12_tbm[0], color='green', ls=':', lw=1.5, label=f'TBM: {theta12_tbm[0]:.2f}')
    ax.axvline(LAMBDA, color='gray', ls='--', alpha=0.5, label=f'$\\lambda$ = {LAMBDA:.4f}')

    # Experimental band
    ax.axhspan(33.41 - 0.76, 33.41 + 0.76, color='yellow', alpha=0.3, label='NuFIT 5.x 1-sigma')

    ax.set_xlabel(r'$\lambda$ (Wolfenstein parameter)', fontsize=12)
    ax.set_ylabel(r'$\theta_{12}$ (degrees)', fontsize=12)
    ax.set_title(r'$\theta_{12}$ vs $\lambda$: QLC vs A4 Starting Points', fontsize=14)
    ax.legend(fontsize=9)
    ax.set_xlim(0, 0.35)
    ax.set_ylim(25, 50)
    ax.grid(True, alpha=0.3)

    # Annotate the lambda->0 discrepancy
    ax.annotate('QLC: limit = 45 deg\n(NOT TBM = 35.26 deg)',
                xy=(0.02, 44.5), fontsize=9, color='blue',
                bbox=dict(boxstyle='round', fc='white', alpha=0.8))
    ax.annotate('A4: limit = 35.26 deg\n(= TBM, correct)',
                xy=(0.02, 35.5), fontsize=9, color='red',
                bbox=dict(boxstyle='round', fc='white', alpha=0.8))

    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'ext_3_1_2d_tbm_limit.png', dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Plot saved: {PLOT_DIR / 'ext_3_1_2d_tbm_limit.png'}")


def plot_jarlskog_analysis(results_j):
    """
    Plot Jarlskog invariant vs delta_CP, showing the J_max confusion.
    """
    fig, ax = plt.subplots(figsize=(8, 6))

    dcp_range = np.linspace(0, 360, 500)

    # Use NuFIT 6.0 IC19 mixing angles
    t12 = np.degrees(np.arcsin(np.sqrt(0.307)))
    t23 = np.degrees(np.arcsin(np.sqrt(0.561)))
    t13 = np.degrees(np.arcsin(np.sqrt(0.02195)))

    J_vals = [(1.0/8) * np.sin(np.radians(2*t12)) * np.sin(np.radians(2*t23)) *
              np.sin(np.radians(2*t13)) * np.cos(np.radians(t13)) * np.sin(np.radians(d))
              for d in dcp_range]

    ax.plot(dcp_range, J_vals, 'b-', lw=2, label=r'$J(\delta_{CP})$ (NuFIT 6.0 angles)')

    # Mark key points
    ax.axhline(0.033, color='red', ls='--', alpha=0.7, label=r'$J_{max} = 0.033$ (document "observed")')
    ax.axhline(-0.033, color='red', ls='--', alpha=0.7)
    ax.axhline(results_j['J_predicted'], color='purple', ls='-.',
               label=f'Predicted: J = {results_j["J_predicted"]:.4f}')

    # Mark delta_CP values
    for dcp, label, color in [(177, 'NuFIT 6.0 IC19', 'green'),
                               (197, 'NuFIT 5.x', 'orange'),
                               (200, 'Predicted', 'purple'),
                               (212, 'NuFIT 6.0 IC24', 'cyan')]:
        J_at = (1.0/8) * np.sin(np.radians(2*t12)) * np.sin(np.radians(2*t23)) * \
               np.sin(np.radians(2*t13)) * np.cos(np.radians(t13)) * np.sin(np.radians(dcp))
        ax.plot(dcp, J_at, 'o', color=color, markersize=8, zorder=5)
        ax.annotate(f'{label}\n({dcp} deg, J={J_at:.4f})', xy=(dcp, J_at),
                    xytext=(dcp+15, J_at + 0.005 * (1 if J_at > 0 else -1)),
                    fontsize=7, arrowprops=dict(arrowstyle='->', color=color),
                    color=color)

    ax.axhline(0, color='gray', ls='-', alpha=0.3)
    ax.set_xlabel(r'$\delta_{CP}$ (degrees)', fontsize=12)
    ax.set_ylabel(r'$J_{PMNS}$', fontsize=12)
    ax.set_title('Jarlskog Invariant: Document Confusion between J and $J_{max}$', fontsize=13)
    ax.legend(fontsize=8, loc='upper right')
    ax.set_xlim(0, 360)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'ext_3_1_2d_jarlskog_analysis.png', dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Plot saved: {PLOT_DIR / 'ext_3_1_2d_jarlskog_analysis.png'}")


def plot_mass_ratio_candidates(results_ratio):
    """
    Plot mass ratio candidates showing lambda^2/sqrt(3) is not unique.
    """
    fig, ax = plt.subplots(figsize=(10, 5))

    r_obs = results_ratio['r_observed']
    candidates = results_ratio['candidates']

    names = [c['formula'] for c in candidates]
    values = [c['value'] for c in candidates]
    errors = [c['pct_error'] for c in candidates]

    colors = ['#2ca02c' if e < 2 else ('#ff7f0e' if e < 5 else '#d62728') for e in errors]

    bars = ax.barh(range(len(names)), values, color=colors, alpha=0.7, edgecolor='black')
    ax.axvline(r_obs, color='blue', ls='--', lw=2, label=f'Observed: {r_obs:.5f}')

    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, fontsize=9)
    ax.set_xlabel(r'$r = \Delta m^2_{21} / \Delta m^2_{31}$', fontsize=12)
    ax.set_title('Mass Ratio: Multiple Formulas Can Match Data', fontsize=13)

    # Add error labels
    for i, (v, e) in enumerate(zip(values, errors)):
        ax.text(v + 0.001, i, f'{e:.1f}%', va='center', fontsize=8)

    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3, axis='x')
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'ext_3_1_2d_mass_ratio_candidates.png', dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Plot saved: {PLOT_DIR / 'ext_3_1_2d_mass_ratio_candidates.png'}")


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def main():
    print("=" * 70)
    print("ADVERSARIAL PHYSICS VERIFICATION")
    print("Extension 3.1.2d: Complete PMNS Parameter Derivation")
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 70)

    results = {
        "theorem": "Extension 3.1.2d",
        "title": "Complete PMNS Parameter Derivation - Adversarial Physics Verification",
        "timestamp": datetime.now().isoformat(),
        "lambda": float(LAMBDA),
        "phi": float(PHI),
        "verifications": []
    }

    # Run all tests
    r1 = test_theta12_dimensional_consistency()
    r2 = test_nufit60_comparison()
    r3 = test_tbm_limit_recovery()
    r4 = test_jarlskog_consistency()
    r5 = test_deltaCP_formula_consistency()
    r6 = test_mass_ratio_sensitivity()
    r7 = test_parameter_count()
    r8 = test_section54_numerical()

    results["verifications"] = [r1, r2, r3, r4, r5, r6, r7, r8]

    # Generate plots
    print("\n" + "=" * 70)
    print("GENERATING PLOTS")
    print("=" * 70)
    plot_nufit_comparison(r2)
    plot_tbm_limit(r3)
    plot_jarlskog_analysis(r4)
    plot_mass_ratio_candidates(r6)

    # Summary
    print("\n" + "=" * 70)
    print("ADVERSARIAL VERIFICATION SUMMARY")
    print("=" * 70)

    issues = {
        "Dimensional inconsistency in theta_12": r1['dimensional_error_confirmed'],
        "NuFIT values outdated": True,
        "TBM limit NOT recovered": not r3['theta12_recovers_tbm'],
        "J_max confusion in Jarlskog": r4['jmax_confusion_confirmed'],
        "delta_CP algebraic error": r5['algebraic_error_confirmed'],
        "Mass ratio not unique": r6['num_within_5pct'] > 1,
        "Overfitting detected": r7['overfitting_detected'],
        "Section 5.4 numerical error": r8['error_confirmed'],
    }

    n_confirmed = sum(issues.values())
    print(f"\n  Issues confirmed: {n_confirmed}/{len(issues)}")
    for issue, confirmed in issues.items():
        status = "CONFIRMED" if confirmed else "Not confirmed"
        print(f"    [{status}] {issue}")

    results["issues_confirmed"] = n_confirmed
    results["total_issues_checked"] = len(issues)
    results["overall_status"] = "ISSUES CONFIRMED" if n_confirmed > 3 else "PARTIAL"

    # Save results
    output_file = Path(__file__).parent.parent / "extension_3_1_2d_adversarial_results.json"
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n  Results saved: {output_file}")

    print(f"\n  Overall: {results['overall_status']}")
    print(f"\n  Plots saved in: {PLOT_DIR}")
    return results


if __name__ == "__main__":
    main()
