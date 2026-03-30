#!/usr/bin/env python3
"""
Proposition 7.4.3: Adversarial Physics Verification
=====================================================

ADVERSARIAL VERIFICATION PROTOCOL

You are an independent verification agent. Your role is ADVERSARIAL.
Your job is to find errors, gaps, and inconsistencies.

CHECKLIST:
1. LOGICAL VALIDITY - Does each step follow? Hidden assumptions?
2. MATHEMATICAL CORRECTNESS - Re-derive key equations independently
3. DIMENSIONAL ANALYSIS - Consistent units throughout?
4. LIMITING CASES - Reduces to known physics appropriately?
5. PHYSICAL REASONABLENESS - No pathologies?
6. NUMERICAL ACCURACY - Within expected bounds?

Related Documents:
    - Statement: docs/proofs/Phase7/Proposition-7.4.3-FCC-Lattice-Perturbation-Theory.md
    - Derivation: docs/proofs/Phase7/Proposition-7.4.3-FCC-Lattice-Perturbation-Theory-Derivation.md
    - Applications: docs/proofs/Phase7/Proposition-7.4.3-FCC-Lattice-Perturbation-Theory-Applications.md
    - Multi-Agent Report: docs/proofs/verification-records/Proposition-7.4.3-Multi-Agent-Verification-2026-02-13.md

Key Claims Under Adversarial Test:
    (a) b_0 = 11/(16*pi^2) universal on FCC
    (b) Asymptotic scaling: a(beta) ~ exp(-beta/(12*b_0))
    (c) D_4 isotropy: Delta T = 0 (rotational artifacts at O(a^4) not O(a^2))
    (d) Lambda ratio: Lambda_FCC / Lambda_MSbar ~ 34.0
    (ADVERSARIAL) Tadpole integral: claimed 0.1549 vs MC ~0.088
    (ADVERSARIAL) Laplacian normalization: k_hat^2 -> k^2 or (3/2)*k^2?
    (ADVERSARIAL) Sign error in RG derivation
    (ADVERSARIAL) Vertex correction delta_vertex ~ 0.023 (unverified)

Verification Date: 2026-02-13
"""

import numpy as np
import json
import os
from dataclasses import dataclass, field
from datetime import datetime
from typing import Dict, List

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
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
# PHYSICAL CONSTANTS
# =============================================================================

N_C = 3                                        # SU(3) color
N_F = 0                                        # Pure gauge (no quarks)
HBAR_C = 197.327                               # MeV * fm
R_STELLA = 0.44847                             # fm (observed)
SQRT_SIGMA_PHYS = HBAR_C / R_STELLA           # ~ 440 MeV

# Perturbative coefficients — exact symbolic values
b_0_exact = 11.0 / (16 * np.pi**2)            # 0.069658...
b_1_exact = 102.0 / (16 * np.pi**2)**2        # 0.004090...
b1_over_2b0sq = 102.0 / (2 * 121)             # 51/121 = 0.42149...

# Values claimed in the proof text
b_0_claimed = 0.06971
b_1_claimed = 0.004098

# Lattice QCD reference
I_CUBIC_EXACT = 0.15493                        # Standard cubic tadpole integral
LAMBDA_CUBIC_OVER_MSBAR = 28.8                 # Dashen & Gross (1981)
LAMBDA_MSBAR_MEV = 340.0                       # Lambda_MSbar for pure SU(3)

# =============================================================================
# TEST INFRASTRUCTURE
# =============================================================================

@dataclass
class TestResult:
    name: str
    passed: bool
    details: str
    severity: str = "INFO"
    numerical_data: Dict = field(default_factory=dict)


all_results: List[TestResult] = []


def record_test(name: str, passed: bool, details: str,
                severity: str = "INFO", numerical_data: Dict = None):
    """Record a test result."""
    result = TestResult(
        name=name, passed=passed, details=details,
        severity=severity, numerical_data=numerical_data or {}
    )
    all_results.append(result)
    icon = "PASS" if passed else "FAIL"
    print(f"  [{icon}] {name}")
    if not passed:
        print(f"         {details}")
    return result


# =============================================================================
# FCC LATTICE MOMENTUM FUNCTIONS
# =============================================================================

def d4_nearest_neighbors():
    """Generate the 24 minimal vectors of the D_4 root lattice.

    These are (+-1, +-1, 0, 0) and all permutations of coordinates.
    """
    neighbors = []
    for mu in range(4):
        for nu in range(mu + 1, 4):
            for s1 in [-1, 1]:
                for s2 in [-1, 1]:
                    n = np.zeros(4)
                    n[mu] = s1
                    n[nu] = s2
                    neighbors.append(n)
    return np.array(neighbors)


def fcc_k_hat_squared_from_neighbors(k, neighbors):
    """Compute k_hat^2_FCC from the lattice Laplacian definition.

    hat{k}^2 = (2/z) * sum_{i=1}^{z} [1 - cos(k . n_i)]

    where n_i are the nearest-neighbor vectors (NOT unit vectors).
    The factor 2/z comes from the normalization:
    in the continuum limit, hat{k}^2 -> k^2.
    """
    z = len(neighbors)
    k_hat_sq = 0.0
    for n in neighbors:
        k_hat_sq += 1.0 - np.cos(np.dot(k, n))
    # With normalization factor to give k^2 in continuum limit
    return 2.0 * k_hat_sq / z * z  # = 2 * sum[1 - cos(k.n)]


def fcc_k_hat_squared_raw(k, neighbors):
    """Raw sum: sum_{i=1}^{z} [1 - cos(k . n_i)], no normalization."""
    total = 0.0
    for n in neighbors:
        total += 1.0 - np.cos(np.dot(k, n))
    return total


def fcc_k_hat_squared_formula(kx, ky, kz, kw):
    """FCC k_hat^2 using the formula from the derivation (Eq in §5.1).

    hat{k}^2 = sum_{mu<nu} 4*sin^2((k_mu + k_nu)/4) + 4*sin^2((k_mu - k_nu)/4)

    This is the formula used in the existing verification script.
    """
    k = np.array([kx, ky, kz, kw])
    k_hat_sq = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):
            k_hat_sq += 4 * np.sin((k[mu] + k[nu]) / 4)**2
            k_hat_sq += 4 * np.sin((k[mu] - k[nu]) / 4)**2
    return k_hat_sq


def cubic_k_hat_squared(kx, ky, kz, kw):
    """Standard hypercubic lattice momentum squared."""
    return (4 * np.sin(kx / 2)**2 + 4 * np.sin(ky / 2)**2 +
            4 * np.sin(kz / 2)**2 + 4 * np.sin(kw / 2)**2)


# =============================================================================
# ASYMPTOTIC SCALING
# =============================================================================

def asymptotic_scaling_a(beta, Lambda_lat=1.0):
    """Lattice spacing a(beta) from asymptotic scaling formula."""
    exponent = -beta / (12 * b_0_exact)
    prefactor = (6 * b_0_exact / beta) ** (-b1_over_2b0sq)
    return prefactor * np.exp(exponent) / Lambda_lat


# =============================================================================
# C1: NUMERICAL PRECISION OF b_0 AND b_1
# =============================================================================

def test_c1_beta_function_precision():
    """C1: Adversarial check on numerical precision of b_0, b_1.

    The proof text claims b_0 ≈ 0.06971 and b_1 ≈ 0.004098.
    The exact values are b_0 = 11/(16*pi^2) ≈ 0.069658 and
    b_1 = 102/(16*pi^2)^2 ≈ 0.004090.

    Multi-agent review flagged these as errors E1, E2.
    """
    print("\n" + "=" * 70)
    print("C1: BETA FUNCTION COEFFICIENT PRECISION")
    print("=" * 70)

    # Exact values
    b0_exact = 11.0 / (16 * np.pi**2)
    b1_exact = 102.0 / (16 * np.pi**2)**2

    # Cross-check: alternative formula
    b0_alt = 11 * N_C / (3 * (4 * np.pi)**2)
    b1_alt = 34 * N_C**2 / (3 * (4 * np.pi)**4)

    # Verify equivalence of formulas
    formula_match = abs(b0_exact - b0_alt) < 1e-15 and abs(b1_exact - b1_alt) < 1e-15

    # Check claimed values
    b0_err = abs(b_0_claimed - b0_exact) / b0_exact
    b1_err = abs(b_1_claimed - b1_exact) / b1_exact

    # Derived quantities
    b1_over_2b0sq_exact = b1_exact / (2 * b0_exact**2)
    b1_over_2b0sq_symbolic = 51.0 / 121  # 102/(2*11^2)
    derived_match = abs(b1_over_2b0sq_exact - b1_over_2b0sq_symbolic) < 1e-12

    # The proof uses b_0^2 = 0.004860, but exact is 0.004852
    b0_sq_claimed = 0.004860
    b0_sq_exact = b0_exact**2
    b0sq_err = abs(b0_sq_claimed - b0_sq_exact) / b0_sq_exact

    passed = (b0_err < 0.001 and b1_err < 0.01 and formula_match
              and derived_match)

    record_test(
        "C1: b_0, b_1 precision and formula consistency",
        passed,
        f"b_0 exact = {b0_exact:.8f}, claimed = {b_0_claimed}, "
        f"error = {b0_err:.4%}. "
        f"b_1 exact = {b1_exact:.8f}, claimed = {b_1_claimed}, "
        f"error = {b1_err:.4%}. "
        f"b_0^2 exact = {b0_sq_exact:.6f}, claimed = {b0_sq_claimed}, "
        f"error = {b0sq_err:.4%}. "
        f"b_1/(2*b_0^2) exact = {b1_over_2b0sq_exact:.6f}, "
        f"symbolic 51/121 = {b1_over_2b0sq_symbolic:.6f}. "
        f"Formula match: {formula_match}.",
        severity="WARNING" if not passed else "INFO",
        numerical_data={
            "b0_exact": b0_exact, "b0_claimed": b_0_claimed, "b0_error": b0_err,
            "b1_exact": b1_exact, "b1_claimed": b_1_claimed, "b1_error": b1_err,
            "b0_sq_exact": b0_sq_exact, "b0_sq_claimed": b0_sq_claimed,
            "b1_over_2b0sq": b1_over_2b0sq_exact,
            "formula_match": formula_match
        }
    )


# =============================================================================
# C2: LAPLACIAN NORMALIZATION (CRITICAL - ERROR E4)
# =============================================================================

def test_c2_laplacian_normalization():
    """C2: CRITICAL — Does the FCC Laplacian give k^2 or (3/2)*k^2?

    Multi-agent review (E4) found that the derivation formula gives
    (3/2)*k^2 in the continuum limit, not k^2.

    We independently verify by:
    1. Computing hat{k}^2 from the D_4 neighbor definition
    2. Computing hat{k}^2 from the formula in the derivation
    3. Taking the continuum limit of both
    4. Comparing with the correctly normalized cubic Laplacian
    """
    print("\n" + "=" * 70)
    print("C2: LAPLACIAN NORMALIZATION (CRITICAL)")
    print("=" * 70)

    neighbors = d4_nearest_neighbors()
    z = len(neighbors)

    # Test at a small k (continuum limit regime)
    k_small = np.array([0.01, 0.02, 0.015, 0.005])
    k2_continuum = np.sum(k_small**2)

    # Method 1: From neighbor sum (raw, no normalization)
    raw_sum = 0.0
    for n in neighbors:
        raw_sum += 1.0 - np.cos(np.dot(k_small, n))
    # In continuum limit: sum_i (k.n_i)^2 / 2 for small k
    # For D_4 with 24 NN of norm sqrt(2): sum_i (k.n_i)^2 = z*|n|^2*k^2/(d) * ...
    # More precisely, by isotropy: sum_i (k.n_i)^2 = (z*|n|^2/d)*k^2 for isotropic lattice

    # Method 2: From the derivation formula (§5.1, line 35)
    k_hat_sq_formula = fcc_k_hat_squared_formula(*k_small)

    # Method 3: From definition with proper normalization
    # Standard lattice Laplacian: hat{k}^2 = (1/a^2)*sum_i 2*(1 - cos(k.n_i*a))
    # For D_4 with NN vectors of length a*sqrt(2)/2 (after scaling by a):
    # In our convention, n_i are dimensionless (in units of a), length sqrt(2)
    # hat{k}^2 = sum_i 2*(1 - cos(k_mu n_i_mu)) / |n_i|^2
    # OR we can normalize by requiring hat{k}^2 -> k^2

    # Method 4: Cubic lattice for comparison
    k_hat_sq_cubic = cubic_k_hat_squared(*k_small)

    # Compute ratios to k^2 in continuum limit
    ratio_formula_to_k2 = k_hat_sq_formula / k2_continuum
    ratio_cubic_to_k2 = k_hat_sq_cubic / k2_continuum
    ratio_raw_to_k2 = raw_sum / k2_continuum

    # The formula gives sum_{mu<nu} 4*sin^2((k_mu+k_nu)/4) + 4*sin^2((k_mu-k_nu)/4)
    # For small k: ~ sum_{mu<nu} [(k_mu+k_nu)^2/4 + (k_mu-k_nu)^2/4]
    #            = sum_{mu<nu} [(k_mu^2 + k_nu^2)/2]
    #            = (d-1)/2 * sum_mu k_mu^2 = (3/2)*k^2 for d=4
    # So the formula DOES give (3/2)*k^2, NOT k^2!

    # Verify analytically
    analytical_ratio = (4 - 1) / 2.0  # (d-1)/2 = 3/2

    # The raw 1-cos sum gives the same: sum_i [1 - cos(k.n_i)] ~ sum_i (k.n_i)^2/2
    # For D_4: sum_i (k.n_i)^2 = sum_{mu<nu} [(k_mu+k_nu)^2 + (k_mu-k_nu)^2]
    #                           = sum_{mu<nu} 2*(k_mu^2 + k_nu^2) = 2*(d-1)*k^2 = 6*k^2
    # So raw sum ~ 3*k^2, and formula gives same (since factor 4*sin^2(x/4) ~ x^2/4)

    formula_gives_3over2 = abs(ratio_formula_to_k2 - 1.5) < 0.01
    cubic_gives_1 = abs(ratio_cubic_to_k2 - 1.0) < 0.01

    passed = formula_gives_3over2 and cubic_gives_1

    record_test(
        "C2: FCC Laplacian normalization — formula gives (3/2)*k^2, NOT k^2",
        passed,
        f"k^2 = {k2_continuum:.8f}. "
        f"Formula hat{{k}}^2 = {k_hat_sq_formula:.8f}, "
        f"ratio = {ratio_formula_to_k2:.4f} (expected 1.5). "
        f"Cubic hat{{k}}^2 = {k_hat_sq_cubic:.8f}, "
        f"ratio = {ratio_cubic_to_k2:.4f} (expected 1.0). "
        f"Raw 1-cos sum = {raw_sum:.8f}, "
        f"ratio = {ratio_raw_to_k2:.4f}. "
        f"CONFIRMS E4: formula needs 2/3 normalization factor.",
        severity="CRITICAL",
        numerical_data={
            "k2_continuum": k2_continuum,
            "k_hat_sq_formula": k_hat_sq_formula,
            "ratio_formula": ratio_formula_to_k2,
            "k_hat_sq_cubic": k_hat_sq_cubic,
            "ratio_cubic": ratio_cubic_to_k2,
            "analytical_ratio": analytical_ratio,
            "error_confirmed": formula_gives_3over2
        }
    )


# =============================================================================
# C3: TADPOLE INTEGRAL DISCREPANCY (CRITICAL - ERROR E5)
# =============================================================================

def test_c3_tadpole_integral():
    """C3: CRITICAL — Tadpole integral: claimed 0.1549 vs MC ~0.088.

    The proof claims I_FCC ≈ 0.1549, but MC integration gives ~0.088.
    This is related to the Laplacian normalization issue (C2).

    We compute three estimates:
    1. MC with the formula as-written (unnormalized) — should give ~0.088
    2. MC with 2/3 normalization correction — should give ~0.132
    3. MC on cubic lattice for comparison — should give ~0.1549
    """
    print("\n" + "=" * 70)
    print("C3: TADPOLE INTEGRAL DISCREPANCY (CRITICAL)")
    print("=" * 70)

    n_samples = 1_000_000
    rng = np.random.RandomState(42)
    k = rng.uniform(-np.pi, np.pi, size=(n_samples, 4))

    # FCC with formula as written (no normalization correction)
    k_sq_fcc_raw = np.zeros(n_samples)
    for mu in range(4):
        for nu in range(mu + 1, 4):
            k_sq_fcc_raw += 4 * np.sin((k[:, mu] + k[:, nu]) / 4)**2
            k_sq_fcc_raw += 4 * np.sin((k[:, mu] - k[:, nu]) / 4)**2

    # FCC with 2/3 normalization (corrected)
    k_sq_fcc_corrected = k_sq_fcc_raw * (2.0 / 3.0)

    # Cubic
    k_sq_cubic = np.sum(4 * np.sin(k / 2)**2, axis=1)

    # Compute tadpole integrals (MC over [-pi,pi]^4)
    def mc_tadpole(k_sq):
        mask = k_sq > 1e-12
        integrand = np.zeros(n_samples)
        integrand[mask] = 1.0 / k_sq[mask]
        return np.mean(integrand), np.std(integrand) / np.sqrt(n_samples)

    I_fcc_raw, I_fcc_raw_err = mc_tadpole(k_sq_fcc_raw)
    I_fcc_corr, I_fcc_corr_err = mc_tadpole(k_sq_fcc_corrected)
    I_cubic, I_cubic_err = mc_tadpole(k_sq_cubic)

    # Check: is the raw FCC value approximately the claimed 0.1549?
    # If not, does the normalization explain the difference?
    raw_matches_claimed = abs(I_fcc_raw - 0.1549) < 0.01
    raw_matches_088 = abs(I_fcc_raw - 0.088) < 0.01
    cubic_matches_exact = abs(I_cubic - I_CUBIC_EXACT) < 0.01
    corrected_estimate = I_fcc_raw * 1.5  # 1/(k^2*2/3) = 1.5/k^2, so I_corr ~ 1.5*I_raw

    # The key insight: if hat{k}^2 is 3/2 times too large, then 1/hat{k}^2 is 2/3 times
    # too small, so the integral I = int 1/hat{k}^2 is 2/3 of the correct value.
    # Correct I_FCC ~ I_raw * 3/2 = 0.088 * 1.5 = 0.132
    # This is STILL not 0.1549, suggesting the BZ volume is also an issue.
    # The D_4 BZ (24-cell) has volume (2pi)^4/4 vs (2pi)^4 for cubic.
    # But we're integrating over [-pi,pi]^4 in both cases (cubic BZ).
    # For D_4, the correct BZ is a 24-cell with volume (2pi)^4 * det(D_4_basis) = ...

    passed = raw_matches_088 and cubic_matches_exact

    record_test(
        "C3: Tadpole integral — raw MC ≈ 0.088, NOT 0.1549",
        passed,
        f"I_FCC (raw formula) = {I_fcc_raw:.4f} +/- {I_fcc_raw_err:.4f} "
        f"(expected ~0.088). "
        f"I_FCC (2/3 corrected) = {I_fcc_corr:.4f} +/- {I_fcc_corr_err:.4f}. "
        f"I_FCC (raw * 3/2) = {corrected_estimate:.4f}. "
        f"I_cubic = {I_cubic:.4f} +/- {I_cubic_err:.4f} "
        f"(exact = {I_CUBIC_EXACT}). "
        f"Raw matches 0.088: {raw_matches_088}. "
        f"Raw matches 0.1549: {raw_matches_claimed}. "
        f"CONFIRMS E5: claimed value 0.1549 is wrong for the formula as written.",
        severity="CRITICAL",
        numerical_data={
            "I_fcc_raw": I_fcc_raw, "I_fcc_raw_err": I_fcc_raw_err,
            "I_fcc_corrected": I_fcc_corr, "I_fcc_corr_err": I_fcc_corr_err,
            "I_fcc_raw_times_1p5": corrected_estimate,
            "I_cubic": I_cubic, "I_cubic_err": I_cubic_err,
            "I_cubic_exact": I_CUBIC_EXACT,
            "claimed_I_fcc": 0.1549
        }
    )


# =============================================================================
# C4: SIGN ERROR IN RG INTEGRATION (ERROR E3)
# =============================================================================

def test_c4_rg_sign_error():
    """C4: Sign error in RG integration (Derivation §5.4, line 100).

    The derivation writes:
        ln(a*Lambda) = +1/(2*b_0*g_0^2) + b_1/(2*b_0^2)*ln(b_0*g_0^2) + ...

    But the correct sign is:
        ln(a*Lambda) = -1/(2*b_0*g_0^2) - b_1/(2*b_0^2)*ln(b_0*g_0^2) + ...

    because a*Lambda < 1 requires ln(a*Lambda) < 0, and at weak coupling
    (g_0 -> 0), 1/(2*b_0*g_0^2) -> +infinity, so we need the minus sign.

    The boxed formula (line 92-93) IS correct despite this intermediate error.
    """
    print("\n" + "=" * 70)
    print("C4: SIGN ERROR IN RG INTEGRATION")
    print("=" * 70)

    # Test: does the boxed formula give a -> 0 as beta -> infinity?
    betas_test = [10, 20, 50, 100, 200]
    a_vals = [asymptotic_scaling_a(b) for b in betas_test]

    # All a values should be positive and decreasing
    all_positive = all(a > 0 for a in a_vals)
    monotone_decreasing = all(a_vals[i] > a_vals[i+1] for i in range(len(a_vals)-1))
    approaches_zero = a_vals[-1] < 1e-50

    # Test the intermediate formula with WRONG sign
    # ln(a*Lambda) = +1/(2*b_0*g_0^2) would give a -> infinity as beta -> infinity
    beta_test = 100.0
    g0_sq = 6.0 / beta_test

    ln_aL_wrong = +1.0 / (2 * b_0_exact * g0_sq)   # WRONG sign
    ln_aL_correct = -1.0 / (2 * b_0_exact * g0_sq)  # CORRECT sign

    wrong_gives_large_a = ln_aL_wrong > 0  # exp(+large) = very large
    correct_gives_small_a = ln_aL_correct < 0  # exp(-large) = very small

    # Verify that the boxed formula uses the correct sign by checking its output
    a_100 = asymptotic_scaling_a(100.0)
    boxed_correct = a_100 < 1e-40  # Should be astronomically small

    passed = all_positive and monotone_decreasing and approaches_zero and boxed_correct

    record_test(
        "C4: Boxed formula correct despite sign error in derivation",
        passed,
        f"a values at betas {betas_test}: "
        f"{[f'{a:.4e}' for a in a_vals]}. "
        f"Monotone decreasing: {monotone_decreasing}. "
        f"a(200) < 1e-50: {approaches_zero}. "
        f"ln(a*Lambda) at beta=100: wrong sign = {ln_aL_wrong:.2f} (would give a->inf), "
        f"correct sign = {ln_aL_correct:.2f} (gives a->0). "
        f"Boxed formula gives a(100) = {a_100:.4e}: CORRECT.",
        severity="SIGNIFICANT",
        numerical_data={
            "a_values": dict(zip(betas_test, a_vals)),
            "ln_aL_wrong_sign": ln_aL_wrong,
            "ln_aL_correct_sign": ln_aL_correct,
            "boxed_formula_correct": boxed_correct
        }
    )


# =============================================================================
# C5: D_4 FOURTH-MOMENT ISOTROPY (VERIFIED)
# =============================================================================

def test_c5_d4_isotropy():
    """C5: D_4 fourth-moment isotropy — Lemma 6.3.1.

    Verify that Delta T = 0 for the D_4 lattice and Delta T != 0 for cubic.
    This is the strongest claim in Part (c) and was confirmed by all agents.
    """
    print("\n" + "=" * 70)
    print("C5: D_4 FOURTH-MOMENT ISOTROPY")
    print("=" * 70)

    neighbors = d4_nearest_neighbors()
    z = len(neighbors)
    d = 4

    # Normalize neighbors to unit length
    norms = np.linalg.norm(neighbors, axis=1)
    n_hat = neighbors / norms[:, np.newaxis]

    # Compute T_{ijkl} = sum_i hat{n}_i_j hat{n}_i_k hat{n}_i_l hat{n}_i_m
    T = np.zeros((d, d, d, d))
    for n in n_hat:
        for i in range(d):
            for j in range(d):
                for k in range(d):
                    for l in range(d):
                        T[i, j, k, l] += n[i] * n[j] * n[k] * n[l]

    # Isotropic reference
    prefactor = z / (d * (d + 2))  # 24/(4*6) = 1
    T_iso = np.zeros((d, d, d, d))
    for i in range(d):
        for j in range(d):
            for k in range(d):
                for l in range(d):
                    val = 0.0
                    if i == j and k == l: val += 1
                    if i == k and j == l: val += 1
                    if i == l and j == k: val += 1
                    T_iso[i, j, k, l] = prefactor * val

    delta_T_fcc = np.max(np.abs(T - T_iso))

    # Check specific components
    T_1111 = T[0, 0, 0, 0]
    T_1122 = T[0, 0, 1, 1]
    T_1212 = T[0, 1, 0, 1]

    # For perfect isotropy: T_1111 = 3*prefactor, T_1122 = T_1212 = prefactor
    T_1111_expected = 3 * prefactor
    T_1122_expected = prefactor

    # Cubic lattice for comparison
    cubic_neighbors = []
    for mu in range(4):
        for s in [-1, 1]:
            n = np.zeros(4)
            n[mu] = s
            cubic_neighbors.append(n)
    z_cubic = len(cubic_neighbors)  # 8

    T_cubic = np.zeros((d, d, d, d))
    for n in cubic_neighbors:
        for i in range(d):
            for j in range(d):
                for k in range(d):
                    for l in range(d):
                        T_cubic[i, j, k, l] += n[i] * n[j] * n[k] * n[l]

    prefactor_cubic = z_cubic / (d * (d + 2))
    T_iso_cubic = np.zeros((d, d, d, d))
    for i in range(d):
        for j in range(d):
            for k in range(d):
                for l in range(d):
                    val = 0.0
                    if i == j and k == l: val += 1
                    if i == k and j == l: val += 1
                    if i == l and j == k: val += 1
                    T_iso_cubic[i, j, k, l] = prefactor_cubic * val

    delta_T_cubic = np.max(np.abs(T_cubic - T_iso_cubic))

    fcc_isotropic = delta_T_fcc < 1e-14
    cubic_anisotropic = delta_T_cubic > 0.01

    passed = fcc_isotropic and cubic_anisotropic

    record_test(
        "C5: D_4 isotropy: Delta T_FCC = 0, Delta T_cubic != 0",
        passed,
        f"D_4 neighbors: {z}. Max |Delta T_FCC| = {delta_T_fcc:.2e} "
        f"(machine precision). "
        f"T_1111 = {T_1111:.4f} (expected {T_1111_expected:.4f}), "
        f"T_1122 = {T_1122:.4f} (expected {T_1122_expected:.4f}). "
        f"Cubic: max |Delta T| = {delta_T_cubic:.4f}. "
        f"FCC isotropic: {fcc_isotropic}. Cubic anisotropic: {cubic_anisotropic}.",
        numerical_data={
            "delta_T_fcc": delta_T_fcc, "delta_T_cubic": delta_T_cubic,
            "T_1111": T_1111, "T_1122": T_1122, "T_1212": T_1212,
            "z_fcc": z, "z_cubic": z_cubic,
            "fcc_isotropic": fcc_isotropic,
            "cubic_anisotropic": cubic_anisotropic
        }
    )


# =============================================================================
# C6: COORDINATION NUMBER CONFUSION (ERROR E9)
# =============================================================================

def test_c6_coordination_number():
    """C6: Coordination number: 12 vs 24.

    The text alternates between 12 and 24 nearest neighbors.
    - 3D FCC has coordination number 12
    - 4D D_4 root lattice has 24 minimal vectors
    - The derivation §5.1 says '12 nearest-neighbor vectors'
    - Appendix A says '24 nearest neighbors'

    Both are correct in different contexts, but the text is inconsistent.
    """
    print("\n" + "=" * 70)
    print("C6: COORDINATION NUMBER CONSISTENCY")
    print("=" * 70)

    # Generate all D_4 minimal vectors
    neighbors = d4_nearest_neighbors()
    z_d4 = len(neighbors)

    # Verify they are all the same length
    norms = np.linalg.norm(neighbors, axis=1)
    all_same_length = np.max(np.abs(norms - norms[0])) < 1e-14
    norm_value = norms[0]

    # The D_4 lattice Laplacian sums over all 24 minimal vectors
    # The "12 nearest-neighbor" count seems to come from 4D FCC having
    # C(4,2) = 6 pairs of coordinates, each with 2 sign choices = 12
    # But that's only half — you need both (+,+), (+,-), (-,+), (-,-) = 24 total

    # Actually, for mu < nu, we get 4 vectors each from C(4,2)=6 pairs = 24
    count_from_pairs = 0
    for mu in range(4):
        for nu in range(mu + 1, 4):
            count_from_pairs += 4  # (++, +-, -+, --)

    record_test(
        "C6: D_4 coordination number is 24, not 12",
        z_d4 == 24 and count_from_pairs == 24,
        f"D_4 minimal vectors: {z_d4} (expected 24). "
        f"All same length: {all_same_length}, norm = {norm_value:.4f}. "
        f"Count from mu<nu pairs: {count_from_pairs}. "
        f"The derivation §5.1 line 21-23 says '12' which is INCORRECT for D_4. "
        f"3D FCC has coordination 12; 4D D_4 has coordination 24.",
        numerical_data={
            "z_d4": z_d4, "norm": norm_value,
            "count_from_pairs": count_from_pairs
        }
    )


# =============================================================================
# C7: ASYMPTOTIC SCALING MONOTONICITY AND LIMITS
# =============================================================================

def test_c7_asymptotic_scaling():
    """C7: Asymptotic scaling formula — monotonicity, limits, Lambda independence.

    Verify:
    1. a(beta) is monotonically decreasing for beta > 0
    2. a(beta) -> 0 as beta -> infinity (continuum limit)
    3. Lattice spacing ratio a(b1)/a(b2) is Lambda-independent
    4. N_f dependence: asymptotic freedom lost at N_f = 16.5
    """
    print("\n" + "=" * 70)
    print("C7: ASYMPTOTIC SCALING FORMULA")
    print("=" * 70)

    # Monotonicity
    betas = np.linspace(2, 50, 200)
    a_vals = np.array([asymptotic_scaling_a(b) for b in betas])
    monotone = all(a_vals[i] > a_vals[i+1] for i in range(len(a_vals)-1))

    # Continuum limit
    a_100 = asymptotic_scaling_a(100)
    a_200 = asymptotic_scaling_a(200)
    ratio_200_100 = a_200 / a_100
    approaches_zero = ratio_200_100 < 1e-10

    # Lambda independence of ratio
    ratio_L1 = asymptotic_scaling_a(6.0, Lambda_lat=1.0) / asymptotic_scaling_a(8.0, Lambda_lat=1.0)
    ratio_L100 = asymptotic_scaling_a(6.0, Lambda_lat=100.0) / asymptotic_scaling_a(8.0, Lambda_lat=100.0)
    lambda_independent = abs(ratio_L1 - ratio_L100) / abs(ratio_L1) < 1e-12

    # Asymptotic freedom loss check
    # b_0(N_f) = (11*N_c - 2*N_f) / (3*(4*pi)^2)
    # b_0 = 0 when N_f = 11*N_c/2 = 16.5
    N_f_critical = 11 * N_C / 2.0
    b0_at_16 = (11 * N_C - 2 * 16) / (3 * (4 * np.pi)**2)
    b0_at_17 = (11 * N_C - 2 * 17) / (3 * (4 * np.pi)**2)
    af_lost_correctly = b0_at_16 > 0 and b0_at_17 < 0

    passed = monotone and approaches_zero and lambda_independent and af_lost_correctly

    record_test(
        "C7: Asymptotic scaling — monotone, approaches zero, Lambda-independent",
        passed,
        f"Monotone (2 to 50): {monotone}. "
        f"a(200)/a(100) = {ratio_200_100:.4e} (approaches zero: {approaches_zero}). "
        f"Ratio Lambda-independent: {lambda_independent}. "
        f"N_f_critical = {N_f_critical}. b_0(16) = {b0_at_16:.6f} > 0, "
        f"b_0(17) = {b0_at_17:.6f} < 0: AF correctly lost.",
        numerical_data={
            "monotone": monotone, "ratio_200_100": ratio_200_100,
            "lambda_independent": lambda_independent,
            "N_f_critical": N_f_critical,
            "b0_at_16": b0_at_16, "b0_at_17": b0_at_17
        }
    )


# =============================================================================
# C8: LAMBDA RATIO SENSITIVITY ANALYSIS
# =============================================================================

def test_c8_lambda_ratio_sensitivity():
    """C8: Lambda ratio sensitivity to tadpole integral and vertex correction.

    The claimed Lambda_FCC/Lambda_MSbar ~ 34.0 depends on:
    - I_FCC (DISPUTED: 0.1549 vs 0.088)
    - delta_vertex ≈ 0.023 (UNVERIFIED, Warning W1)

    We compute Lambda ratio for both tadpole values and explore sensitivity.
    """
    print("\n" + "=" * 70)
    print("C8: LAMBDA RATIO SENSITIVITY")
    print("=" * 70)

    # Scenario 1: Using claimed I_FCC = 0.1549
    I_fcc_claimed = 0.1549
    delta_vertex = 0.023  # Unverified
    delta_tadpole_1 = I_CUBIC_EXACT - I_fcc_claimed
    delta_finite_1 = N_C / (4 * np.pi) * delta_tadpole_1 + delta_vertex
    Lambda_ratio_1 = np.exp(delta_finite_1 / (2 * b_0_exact)) * LAMBDA_CUBIC_OVER_MSBAR

    # Scenario 2: Using MC I_FCC ≈ 0.088
    I_fcc_mc = 0.088
    delta_tadpole_2 = I_CUBIC_EXACT - I_fcc_mc
    delta_finite_2 = N_C / (4 * np.pi) * delta_tadpole_2 + delta_vertex
    Lambda_ratio_2 = np.exp(delta_finite_2 / (2 * b_0_exact)) * LAMBDA_CUBIC_OVER_MSBAR

    # Scenario 3: Without vertex correction (delta_vertex = 0)
    delta_finite_3a = N_C / (4 * np.pi) * delta_tadpole_1
    Lambda_ratio_3a = np.exp(delta_finite_3a / (2 * b_0_exact)) * LAMBDA_CUBIC_OVER_MSBAR

    delta_finite_3b = N_C / (4 * np.pi) * delta_tadpole_2
    Lambda_ratio_3b = np.exp(delta_finite_3b / (2 * b_0_exact)) * LAMBDA_CUBIC_OVER_MSBAR

    # Scenario 4: Corrected I_FCC (raw * 3/2 ≈ 0.132)
    I_fcc_corrected = 0.088 * 1.5  # ~0.132
    delta_tadpole_4 = I_CUBIC_EXACT - I_fcc_corrected
    delta_finite_4 = N_C / (4 * np.pi) * delta_tadpole_4 + delta_vertex
    Lambda_ratio_4 = np.exp(delta_finite_4 / (2 * b_0_exact)) * LAMBDA_CUBIC_OVER_MSBAR

    # The key question: is the claimed ~34.0 reasonable?
    # It should be: Lambda_FCC/Lambda_MSbar = f(I_FCC, delta_vertex) * 28.8
    # The sensitivity is through exp(delta/(2*b_0))

    # Range of plausible Lambda ratios
    in_range = 25 < Lambda_ratio_1 < 50

    record_test(
        "C8: Lambda ratio sensitivity — depends critically on I_FCC",
        in_range,
        f"Scenario 1 (I=0.1549, dv=0.023): Lambda_FCC/MSbar = {Lambda_ratio_1:.1f}. "
        f"Scenario 2 (I=0.088, dv=0.023): Lambda_FCC/MSbar = {Lambda_ratio_2:.1f}. "
        f"Scenario 3a (I=0.1549, dv=0): Lambda_FCC/MSbar = {Lambda_ratio_3a:.1f}. "
        f"Scenario 3b (I=0.088, dv=0): Lambda_FCC/MSbar = {Lambda_ratio_3b:.1f}. "
        f"Scenario 4 (I=0.132 corrected, dv=0.023): Lambda_FCC/MSbar = {Lambda_ratio_4:.1f}. "
        f"The Lambda ratio varies from {min(Lambda_ratio_3a, Lambda_ratio_3b, Lambda_ratio_2):.1f} "
        f"to {max(Lambda_ratio_1, Lambda_ratio_2):.1f} across scenarios.",
        severity="SIGNIFICANT",
        numerical_data={
            "Lambda_ratio_claimed_I": Lambda_ratio_1,
            "Lambda_ratio_mc_I": Lambda_ratio_2,
            "Lambda_ratio_no_vertex_claimed": Lambda_ratio_3a,
            "Lambda_ratio_no_vertex_mc": Lambda_ratio_3b,
            "Lambda_ratio_corrected_I": Lambda_ratio_4,
            "I_fcc_claimed": I_fcc_claimed,
            "I_fcc_mc": I_fcc_mc,
            "I_fcc_corrected": I_fcc_corrected,
            "delta_vertex": delta_vertex
        }
    )


# =============================================================================
# C9: VERTEX CORRECTION BOUND
# =============================================================================

def test_c9_vertex_correction():
    """C9: Vertex correction delta_vertex ≈ 0.023 — plausibility check.

    Warning W1: delta_vertex is asserted without derivation.
    We check if the claimed value is dimensionally consistent and in a
    plausible range based on the triangular vs square plaquette geometry.
    """
    print("\n" + "=" * 70)
    print("C9: VERTEX CORRECTION PLAUSIBILITY")
    print("=" * 70)

    delta_vertex = 0.023

    # The vertex correction arises from the difference in the plaquette expansion:
    # Triangular plaquette: Tr(U_triangle) = Tr[1 + ig_0*a*(A1+A2+A3) - ...]
    # Square plaquette: Tr(U_square) = Tr[1 + ig_0*a^2*F_12 + ...]
    #
    # The difference scales as O(g_0^2) at one loop.
    # A natural estimate: delta_vertex ~ N_c/(4*pi) * (geometric factor)
    # where geometric factor ~ O(0.01 - 0.1) from plaquette shape difference.

    # Dimensional check: delta_vertex is dimensionless (OK)
    # Sign check: should be positive if FCC has larger Lambda than cubic
    # Magnitude check: typical one-loop corrections are O(alpha_s/(4*pi)) ~ 0.01-0.1

    alpha_s_over_4pi = N_C / (4 * np.pi)  # ~ 0.239 for g^2*N_c/(4*pi) at g=1
    natural_scale = alpha_s_over_4pi * 0.1  # geometric factor ~ 0.1
    within_order_of_magnitude = 0.001 < delta_vertex < 0.1

    # Impact on Lambda ratio
    impact = np.exp(delta_vertex / (2 * b_0_exact))
    impact_pct = (impact - 1) * 100

    record_test(
        "C9: delta_vertex = 0.023 — plausible but UNVERIFIED",
        within_order_of_magnitude,
        f"delta_vertex = {delta_vertex}. "
        f"Dimensionless: YES. "
        f"Within plausible range (0.001, 0.1): {within_order_of_magnitude}. "
        f"Natural scale alpha_s/(4pi)*0.1 ~ {natural_scale:.4f}. "
        f"Impact on Lambda ratio: factor {impact:.3f} ({impact_pct:.1f}%). "
        f"WARNING: This is the DOMINANT contribution to the FCC vs cubic "
        f"Lambda difference and needs a proper derivation.",
        severity="WARNING",
        numerical_data={
            "delta_vertex": delta_vertex,
            "natural_scale": natural_scale,
            "impact_factor": impact,
            "impact_pct": impact_pct
        }
    )


# =============================================================================
# C10: DASHEN-GROSS DIRECTION CHECK
# =============================================================================

def test_c10_dashen_gross_direction():
    """C10: Lambda ratio direction — which is larger, Lambda_L or Lambda_MSbar?

    The proof says Lambda_cubic/Lambda_MSbar = 28.8.
    Literature says Lambda_MSbar/Lambda_L ≈ 28.8 (Dashen & Gross 1981).
    These are INVERSE statements!

    Standard result: Lambda_MSbar/Lambda_lattice ≈ 28.8 for Wilson action on cubic,
    meaning Lambda_lattice < Lambda_MSbar.
    """
    print("\n" + "=" * 70)
    print("C10: DASHEN-GROSS DIRECTION CHECK")
    print("=" * 70)

    # Standard Dashen-Gross result for SU(3) Wilson action on cubic lattice:
    # Lambda_MSbar / Lambda_lattice = 38.852704 * exp(-3*pi^2/(11*N_c^2))
    # For N_c = 3: = 38.852704 * exp(-3*pi^2/99) = 38.852704 * exp(-0.29987)
    #            = 38.852704 * 0.7408 = 28.78

    prefactor = 38.852704
    exponential = np.exp(-3 * np.pi**2 / (11 * N_C**2))
    standard_ratio = prefactor * exponential

    # This is Lambda_MSbar / Lambda_lattice, meaning Lambda_MSbar > Lambda_lattice
    # The proof text writes Lambda_cubic/Lambda_MSbar = 28.8
    # which would mean Lambda_cubic > Lambda_MSbar — OPPOSITE direction!

    # Check which direction makes physical sense
    # Lambda_MSbar ~ 340 MeV (standard QCD value)
    # Lambda_lattice ~ Lambda_MSbar / 28.8 ~ 11.8 MeV
    # OR Lambda_lattice ~ 28.8 * Lambda_MSbar ~ 9792 MeV?

    # Standard convention: Lambda_lattice is SMALLER than Lambda_MSbar
    # because the lattice regulator is "rougher" — more modes contribute to running

    direction_correct = standard_ratio > 1  # Lambda_MSbar > Lambda_lattice

    # The proof's Lambda ratio formula should be checked for consistency:
    # If Lambda_cubic/Lambda_MSbar = 28.8, then Lambda_FCC/Lambda_MSbar = 34.0
    # means Lambda_FCC > Lambda_cubic, both much larger than Lambda_MSbar.
    # But standard: Lambda_MSbar/Lambda_cubic = 28.8, so Lambda_cubic ~ 11.8 MeV.
    # Then Lambda_FCC ~ 34.0 * Lambda_cubic / 28.8 * Lambda_MSbar...
    # This gets confusing. Let's just flag the direction ambiguity.

    record_test(
        "C10: Dashen-Gross ratio = Lambda_MSbar/Lambda_L = {:.1f}".format(standard_ratio),
        True,  # Pass but flag the warning
        f"Standard Dashen-Gross: Lambda_MSbar/Lambda_lattice = {standard_ratio:.2f}. "
        f"Prefactor = {prefactor}, exp factor = {exponential:.4f}. "
        f"This means Lambda_MSbar > Lambda_lattice (standard direction). "
        f"The proof writes 'Lambda_cubic/Lambda_MSbar = 28.8' which is the INVERSE "
        f"of the standard convention. This needs clarification — the Lambda ratio "
        f"formula in Part (d) may use the inverted ratio internally, and the final "
        f"result Lambda_FCC/Lambda_MSbar ~ 34.0 should be Lambda_MSbar/Lambda_FCC ~ 34.0.",
        severity="WARNING",
        numerical_data={
            "standard_ratio_MSbar_over_L": standard_ratio,
            "prefactor": prefactor,
            "exp_factor": exponential,
            "Lambda_MSbar_MeV": LAMBDA_MSBAR_MEV,
            "Lambda_lattice_MeV_if_standard": LAMBDA_MSBAR_MEV / standard_ratio
        }
    )


# =============================================================================
# C11: BRILLOUIN ZONE VOLUME CROSS-CHECK
# =============================================================================

def test_c11_brillouin_zone():
    """C11: D_4 Brillouin zone — volume and structure check.

    The BZ of D_4 is a 24-cell. The existing MC integration uses [-pi,pi]^4
    (the cubic BZ) for both lattices. For D_4, the correct BZ is different.

    The D_4 lattice has 4 lattice points per cubic unit cell, so its BZ
    has volume (2*pi)^4 * 4 in momentum space... or does it?
    """
    print("\n" + "=" * 70)
    print("C11: BRILLOUIN ZONE VOLUME")
    print("=" * 70)

    # D_4 lattice basis vectors (standard):
    # e1 = (1,1,0,0)/sqrt(2), e2 = (1,-1,0,0)/sqrt(2),
    # e3 = (0,0,1,1)/sqrt(2), e4 = (0,0,1,-1)/sqrt(2)
    # But for the FCC lattice as defined in the proof, the basis is:
    # e1 = a/2*(0,1,1,0), e2 = a/2*(1,0,1,0), e3 = a/2*(1,1,0,0), e4 = a/2*(0,0,1,1)

    # The FCC lattice is a sublattice of Z^4 with index 2
    # (constraint: sum of coordinates is even)
    # So the BZ is TWICE the volume of the cubic BZ
    # BZ_D4 = 2 * (2*pi)^4 / a^4 ... but this depends on conventions

    # Compute the determinant of the D_4 basis matrix (in units of a)
    basis = np.array([
        [0, 1, 1, 0],
        [1, 0, 1, 0],
        [1, 1, 0, 0],
        [0, 0, 1, 1]
    ]) * 0.5  # a/2 factor

    det = abs(np.linalg.det(basis))
    # Unit cell volume in real space: det * a^4
    # BZ volume = (2*pi)^4 / (det * a^4) * (a/2pi)^4... let's compute properly

    # Volume of fundamental domain = |det(basis)|
    # Reciprocal lattice vectors satisfy: b_i . e_j = 2*pi * delta_ij
    # BZ volume = (2*pi)^4 / |det(basis)|

    reciprocal_basis = 2 * np.pi * np.linalg.inv(basis).T
    bz_volume = abs(np.linalg.det(reciprocal_basis))
    cubic_bz_volume = (2 * np.pi)**4

    # Ratio
    volume_ratio = bz_volume / cubic_bz_volume

    # The existing MC integrates over [-pi,pi]^4. If BZ_D4 is different,
    # the MC is integrating over the WRONG region.
    # For D_4 as a sublattice of Z^4 with index 2,
    # the BZ volume should be (2*pi)^4 * 2 (index of sublattice = 2)

    record_test(
        "C11: D_4 BZ volume ratio to cubic = {:.2f}".format(volume_ratio),
        True,  # Informational
        f"D_4 basis det = {det:.4f}. "
        f"BZ volume = {bz_volume:.2f}, cubic BZ = {cubic_bz_volume:.2f}. "
        f"Ratio = {volume_ratio:.2f}. "
        f"The MC integration over [-pi,pi]^4 may need volume correction "
        f"if BZ ratio != 1. This affects the tadpole integral computation.",
        severity="WARNING",
        numerical_data={
            "basis_det": det,
            "bz_volume": bz_volume,
            "cubic_bz_volume": cubic_bz_volume,
            "volume_ratio": volume_ratio
        }
    )


# =============================================================================
# C12: BETA* COMPUTATION FOR CG LATTICE SPACING
# =============================================================================

def test_c12_beta_star():
    """C12: CG lattice spacing matching — beta* ~ 34.1.

    Prop 0.0.17r predicts a^2 = (8/sqrt(3))*ln(3)*l_P^2.
    Using asymptotic scaling, this gives beta* = 12*b_0*ln(1/(a*Lambda_FCC)).
    """
    print("\n" + "=" * 70)
    print("C12: CG LATTICE SPACING BETA*")
    print("=" * 70)

    l_P = 1.616255e-35  # m
    a_CG_sq = (8 / np.sqrt(3)) * np.log(3) * l_P**2
    a_CG = np.sqrt(a_CG_sq)  # m

    # Lambda_FCC in inverse meters
    hbarc_GeV_fm = 0.197327  # GeV * fm
    Lambda_FCC_GeV = 34.0 * 0.340  # GeV (using claimed ratio)
    Lambda_FCC_inv_m = Lambda_FCC_GeV / (hbarc_GeV_fm * 1e-15)

    product = a_CG * Lambda_FCC_inv_m
    beta_star = 12 * b_0_exact * np.log(1.0 / product) if product > 0 else np.inf

    # Cross-check from proof: beta* ≈ 34.1
    near_claimed = abs(beta_star - 34.1) < 1.0

    # Is this deep in perturbative regime?
    deep_perturbative = beta_star > 20

    record_test(
        "C12: beta* = {:.1f} (claimed ~34.1)".format(beta_star),
        deep_perturbative and near_claimed,
        f"a_CG = {a_CG:.4e} m = {a_CG*1e15:.4e} fm. "
        f"Lambda_FCC = {Lambda_FCC_GeV:.1f} GeV. "
        f"a*Lambda = {product:.4e}. "
        f"beta* = {beta_star:.2f} (claimed ~34.1). "
        f"Deep perturbative: {deep_perturbative}.",
        numerical_data={
            "a_CG_m": a_CG, "Lambda_FCC_GeV": Lambda_FCC_GeV,
            "a_Lambda_product": product, "beta_star": beta_star,
            "deep_perturbative": deep_perturbative
        }
    )


# =============================================================================
# SUMMARY AND OUTPUT
# =============================================================================

def generate_summary():
    """Print summary and save results."""
    print("\n" + "=" * 70)
    print("ADVERSARIAL PHYSICS VERIFICATION SUMMARY")
    print("Proposition 7.4.3: FCC Lattice Perturbation Theory and Beta Function")
    print("=" * 70)

    n_pass = sum(1 for r in all_results if r.passed)
    n_fail = sum(1 for r in all_results if not r.passed)
    n_total = len(all_results)

    print(f"\n  Total tests:  {n_total}")
    print(f"  Passed:       {n_pass}")
    print(f"  Failed:       {n_fail}")

    if n_fail > 0:
        print("\n  FAILURES:")
        for r in all_results:
            if not r.passed:
                print(f"    [{r.severity}] {r.name}")

    # Count by severity
    critical = sum(1 for r in all_results if r.severity == "CRITICAL")
    significant = sum(1 for r in all_results if r.severity == "SIGNIFICANT")
    warnings = sum(1 for r in all_results if r.severity == "WARNING")

    print(f"\n  Severity breakdown:")
    print(f"    CRITICAL:    {critical}")
    print(f"    SIGNIFICANT: {significant}")
    print(f"    WARNING:     {warnings}")

    overall = "PASS" if n_fail == 0 else "PARTIAL" if n_fail <= 2 else "FAIL"
    print(f"\n  OVERALL: {overall}")
    print(f"  ({n_pass}/{n_total} tests passed)")

    print("\n  KEY FINDINGS:")
    print("  1. b_0 = 0.06966 (exact), NOT 0.06971 (claimed) — minor precision error")
    print("  2. CRITICAL: FCC Laplacian formula gives (3/2)*k^2, needs normalization")
    print("  3. CRITICAL: Tadpole integral MC gives ~0.088, NOT claimed 0.1549")
    print("  4. Sign error in RG derivation (§5.4) but boxed formula is correct")
    print("  5. D_4 fourth-moment isotropy CONFIRMED (Delta T = 0 to machine precision)")
    print("  6. Coordination number inconsistency (12 vs 24) needs clarification")
    print("  7. Lambda ratio ~34.0 depends critically on disputed tadpole + unverified vertex")
    print("  8. delta_vertex ≈ 0.023 is plausible but UNVERIFIED")
    print("  9. Dashen-Gross ratio direction needs clarification")
    print("  10. CG beta* ≈ 34.1 confirmed, deep in perturbative regime")
    print("  11. D_4 BZ volume differs from cubic — MC integration may need correction")

    print("\n  RECOMMENDED ACTIONS:")
    print("  [CRITICAL] Fix Laplacian normalization: include 2/3 factor or redefine spacing")
    print("  [CRITICAL] Recompute I_FCC with correct normalization and proper BZ")
    print("  [SIGNIFICANT] Fix sign error in derivation §5.4 line 100")
    print("  [WARNING] Derive delta_vertex properly from triangular plaquette expansion")
    print("  [WARNING] Clarify Dashen-Gross direction convention")
    print("  [MINOR] Correct b_0 ≈ 0.06971 to b_0 ≈ 0.06966 throughout")

    # Save results
    output = {
        "proposition": "7.4.3",
        "title": "FCC Lattice Perturbation Theory and Beta Function",
        "verification_type": "adversarial_physics",
        "date": datetime.now().isoformat(),
        "parameters": {
            "N_c": N_C, "N_f": N_F,
            "b_0_exact": b_0_exact,
            "b_1_exact": b_1_exact,
            "b1_over_2b0sq": b1_over_2b0sq,
            "Lambda_MSbar_MeV": LAMBDA_MSBAR_MEV,
            "I_cubic_exact": I_CUBIC_EXACT
        },
        "tests_total": n_total,
        "tests_passed": n_pass,
        "tests_failed": n_fail,
        "severity_counts": {
            "CRITICAL": critical,
            "SIGNIFICANT": significant,
            "WARNING": warnings
        },
        "overall": overall,
        "results": [
            {
                "name": r.name,
                "passed": r.passed,
                "details": r.details,
                "severity": r.severity,
                "numerical_data": {
                    k: (float(v) if isinstance(v, (np.floating, np.float64)) else
                        int(v) if isinstance(v, (np.integer, np.int64)) else
                        bool(v) if isinstance(v, (np.bool_,)) else
                        v)
                    for k, v in r.numerical_data.items()
                },
            }
            for r in all_results
        ],
    }

    output_path = os.path.join(SCRIPT_DIR, 'prop_7_4_3_adversarial_results.json')
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\n  Results saved to: {output_path}")

    return n_fail == 0


# =============================================================================
# PLOT GENERATION
# =============================================================================

def generate_plots():
    """Generate adversarial diagnostic plots (2x2 grid)."""
    if not HAS_MATPLOTLIB:
        print("\n  [SKIP] matplotlib not available, skipping plots")
        return

    print("\n" + "=" * 70)
    print("GENERATING ADVERSARIAL DIAGNOSTIC PLOTS")
    print("=" * 70)

    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(14, 10))

    # ---- Plot 1: Laplacian normalization comparison ----
    k_magnitudes = np.linspace(0.01, 2.0, 200)
    ratio_formula = []
    ratio_cubic = []

    for km in k_magnitudes:
        k = np.array([km, km * 0.7, km * 0.3, km * 0.5])
        k2 = np.sum(k**2)

        k_hat_fcc = fcc_k_hat_squared_formula(*k)
        k_hat_cub = cubic_k_hat_squared(*k)

        ratio_formula.append(k_hat_fcc / k2 if k2 > 0 else 0)
        ratio_cubic.append(k_hat_cub / k2 if k2 > 0 else 0)

    ax1.plot(k_magnitudes, ratio_formula, 'r-', linewidth=2,
             label=r'FCC formula: $\hat{k}^2_{\mathrm{FCC}} / k^2$')
    ax1.plot(k_magnitudes, ratio_cubic, 'b-', linewidth=2,
             label=r'Cubic: $\hat{k}^2_{\mathrm{cubic}} / k^2$')
    ax1.axhline(y=1.5, color='r', linestyle='--', alpha=0.5, label=r'$3/2$ (FCC limit)')
    ax1.axhline(y=1.0, color='b', linestyle='--', alpha=0.5, label=r'$1$ (cubic limit)')
    ax1.set_xlabel(r'$|k|$ [lattice units]', fontsize=12)
    ax1.set_ylabel(r'$\hat{k}^2 / k^2$', fontsize=12)
    ax1.set_title('C2: Laplacian Normalization (CRITICAL)', fontsize=13, color='red')
    ax1.legend(fontsize=9)
    ax1.grid(True, alpha=0.3)
    ax1.set_ylim(0.8, 2.0)

    # ---- Plot 2: D_4 isotropy vs cubic ----
    neighbors_d4 = d4_nearest_neighbors()
    z_d4 = len(neighbors_d4)
    n_hat_d4 = neighbors_d4 / np.linalg.norm(neighbors_d4, axis=1)[:, np.newaxis]

    cubic_nn = []
    for mu in range(4):
        for s in [-1, 1]:
            n = np.zeros(4)
            n[mu] = s
            cubic_nn.append(n)
    z_cub = len(cubic_nn)

    # Compute T_{iiii} and T_{iijj} components
    components_d4 = []
    components_cubic = []
    labels = []

    for i in range(4):
        for j in range(i, 4):
            T_d4 = sum(n[i]**2 * n[j]**2 for n in n_hat_d4)
            T_cub = sum(n[i]**2 * n[j]**2 for n in cubic_nn)

            # Isotropic reference
            if i == j:
                T_iso_d4 = 3 * z_d4 / (4 * 6)
                T_iso_cub = 3 * z_cub / (4 * 6)
            else:
                T_iso_d4 = z_d4 / (4 * 6)
                T_iso_cub = z_cub / (4 * 6)

            components_d4.append(T_d4 - T_iso_d4)
            components_cubic.append(T_cub - T_iso_cub)
            labels.append(f"({i},{j})")

    x = np.arange(len(labels))
    width = 0.35
    ax2.bar(x - width/2, [abs(c) for c in components_d4], width,
            label='FCC (D_4)', color='blue', alpha=0.7)
    ax2.bar(x + width/2, [abs(c) for c in components_cubic], width,
            label='Cubic', color='red', alpha=0.7)
    ax2.set_xlabel('Component (i,j)')
    ax2.set_ylabel(r'$|T_{iijj} - T_{iijj}^{\mathrm{iso}}|$')
    ax2.set_title('C5: Fourth-Moment Isotropy Deviation', fontsize=13)
    ax2.set_xticks(x)
    ax2.set_xticklabels(labels, fontsize=8)
    ax2.legend(fontsize=9)
    ax2.set_yscale('symlog', linthresh=1e-15)

    # ---- Plot 3: Lambda ratio sensitivity ----
    I_fcc_range = np.linspace(0.05, 0.20, 100)
    delta_vertex_vals = [0.0, 0.023, 0.05]
    colors = ['blue', 'red', 'green']

    for dv, color in zip(delta_vertex_vals, colors):
        Lambda_ratios = []
        for I_fcc in I_fcc_range:
            delta_tad = I_CUBIC_EXACT - I_fcc
            delta_fin = N_C / (4 * np.pi) * delta_tad + dv
            ratio = np.exp(delta_fin / (2 * b_0_exact)) * LAMBDA_CUBIC_OVER_MSBAR
            Lambda_ratios.append(ratio)
        ax3.plot(I_fcc_range, Lambda_ratios, color=color, linewidth=2,
                 label=rf'$\delta_{{\mathrm{{vertex}}}} = {dv}$')

    ax3.axvline(x=0.1549, color='orange', linestyle='--', alpha=0.7,
                label=r'$I_{\mathrm{FCC}}$ claimed (0.1549)')
    ax3.axvline(x=0.088, color='purple', linestyle='--', alpha=0.7,
                label=r'$I_{\mathrm{FCC}}$ MC (0.088)')
    ax3.axhline(y=34.0, color='gray', linestyle=':', alpha=0.5,
                label='Claimed ratio (34.0)')
    ax3.set_xlabel(r'$I_{\mathrm{FCC}}$', fontsize=12)
    ax3.set_ylabel(r'$\Lambda_{\mathrm{FCC}} / \Lambda_{\overline{MS}}$', fontsize=12)
    ax3.set_title('C8: Lambda Ratio Sensitivity', fontsize=13)
    ax3.legend(fontsize=8)
    ax3.grid(True, alpha=0.3)
    ax3.set_ylim(20, 60)

    # ---- Plot 4: Asymptotic scaling ----
    betas = np.linspace(3, 50, 200)
    a_vals = np.array([asymptotic_scaling_a(b) for b in betas])

    ax4.semilogy(betas, a_vals, 'b-', linewidth=2,
                 label=r'$a(\beta) \cdot \Lambda_{\mathrm{FCC}}$')
    ax4.axvline(x=34.1, color='r', linestyle='--', alpha=0.7,
                label=r'$\beta^* \approx 34.1$ (CG)')
    ax4.axhline(y=asymptotic_scaling_a(34.1), color='r', linestyle=':', alpha=0.3)
    ax4.set_xlabel(r'$\beta = 6/g_0^2$', fontsize=12)
    ax4.set_ylabel(r'$a \cdot \Lambda_{\mathrm{FCC}}$', fontsize=12)
    ax4.set_title('C7/C12: Asymptotic Scaling', fontsize=13)
    ax4.legend(fontsize=9)
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()
    plot_path = os.path.join(PLOT_DIR, 'prop_7_4_3_adversarial_diagnostics.png')
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {plot_path}")


# =============================================================================
# MAIN
# =============================================================================

if __name__ == '__main__':
    print("=" * 70)
    print("ADVERSARIAL PHYSICS VERIFICATION")
    print("Proposition 7.4.3: FCC Lattice Perturbation Theory and Beta Function")
    print("=" * 70)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"b_0 = {b_0_exact:.8f} (exact: 11/(16*pi^2))")
    print(f"b_1 = {b_1_exact:.8f} (exact: 102/(16*pi^2)^2)")
    print(f"b_1/(2*b_0^2) = {b1_over_2b0sq:.8f} (exact: 51/121)")
    print(f"I_cubic = {I_CUBIC_EXACT}")
    print(f"Lambda_MSbar = {LAMBDA_MSBAR_MEV} MeV")
    print()

    test_c1_beta_function_precision()
    test_c2_laplacian_normalization()
    test_c3_tadpole_integral()
    test_c4_rg_sign_error()
    test_c5_d4_isotropy()
    test_c6_coordination_number()
    test_c7_asymptotic_scaling()
    test_c8_lambda_ratio_sensitivity()
    test_c9_vertex_correction()
    test_c10_dashen_gross_direction()
    test_c11_brillouin_zone()
    test_c12_beta_star()

    success = generate_summary()
    generate_plots()

    import sys
    sys.exit(0 if success else 1)
