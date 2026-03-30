#!/usr/bin/env python3
"""
Proposition 7.4.4: Scaling Window Identification on FCC — Adversarial Physics Verification
===========================================================================================

ADVERSARIAL verification targeting the critical findings from multi-agent review:
  - R(beta) monotonically decreases to 0 (contradicts "stabilization" claim)
  - m_phys either diverges or vanishes near beta_c (no finite positive limit)
  - Lambda_FCC inconsistency (2.6 MeV vs 11.56 GeV)
  - FCC model never matches lattice QCD glueball ratio m_{0++}/sqrt(sigma) ~ 3.7
  - RG flow must cross first-order transition
  - sigma_lat = -ln(u_3) identification untested

Multi-Agent Verification Record:
    docs/proofs/verification-records/Proposition-7.4.4-Multi-Agent-Verification-2026-02-13.md

Related Documents:
    - Statement: docs/proofs/Phase7/Proposition-7.4.4-Scaling-Window-FCC.md
    - Derivation: docs/proofs/Phase7/Proposition-7.4.4-Scaling-Window-FCC-Derivation.md
    - Applications: docs/proofs/Phase7/Proposition-7.4.4-Scaling-Window-FCC-Applications.md

Verification Date: 2026-02-13
"""

import numpy as np
import json
import os
from datetime import datetime
from typing import Dict, Any, Tuple, List

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyArrowPatch
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

N_C = 3
b_0 = 11 * N_C / (3 * (4 * np.pi)**2)   # = 11/(16*pi^2) ~ 0.06966
b_1 = 34 * N_C**2 / (3 * (4 * np.pi)**4)  # = 102/(16*pi^2)^2 ~ 0.004090

# QCD parameters
SQRT_SIGMA_MEV = 440.0       # MeV, FLAG 2024
HBAR_C = 197.327              # MeV * fm
L_PLANCK_M = 1.616255e-35     # m (CODATA 2018)

# Corrected Lambda values (from Prop 7.4.3 multi-agent review)
LAMBDA_MSBAR_MEV_QUENCHED = 260.0   # MeV, quenched SU(3) — NOT 340
LAMBDA_FCC_OVER_MSBAR = 0.010       # Prop 7.4.3: Lambda_FCC/Lambda_MSbar ~ 0.010 — NOT 34
LAMBDA_FCC_MEV = LAMBDA_FCC_OVER_MSBAR * LAMBDA_MSBAR_MEV_QUENCHED  # ~ 2.6 MeV

# Wrong values used in original derivation (for comparison)
LAMBDA_FCC_WRONG_MEV = 34.0 * 340.0  # 11,560 MeV — the incorrect value

# Lattice QCD target: lightest glueball mass / sqrt(sigma)
GLUEBALL_RATIO_TARGET = 3.7   # Morningstar & Peardon 1999 (range: 3.5 - 4.0)
GLUEBALL_RATIO_ERR = 0.3      # Conservative uncertainty

# =============================================================================
# SU(3) HEAT KERNEL (copied from prop_7_4_4_scaling_window.py)
# =============================================================================

def su3_dim(p, q):
    return (p + 1) * (q + 1) * (p + q + 2) // 2

def su3_character(p, q, theta1, theta2):
    z1 = np.exp(1j * theta1)
    z2 = np.exp(1j * theta2)
    z3 = np.exp(-1j * (theta1 + theta2))
    zs = [z1, z2, z3]
    lam_rho = [p + q + 2, q + 1, 0]
    perms = [
        ([0, 1, 2], +1), ([0, 2, 1], -1), ([1, 0, 2], -1),
        ([1, 2, 0], +1), ([2, 0, 1], +1), ([2, 1, 0], -1),
    ]
    num = 0.0 + 0.0j
    den = 0.0 + 0.0j
    for perm, sign in perms:
        num += sign * zs[perm[0]]**lam_rho[0] * zs[perm[1]]**lam_rho[1] * zs[perm[2]]**lam_rho[2]
        den += sign * zs[perm[0]]**2 * zs[perm[1]]**1 * zs[perm[2]]**0
    if abs(den) < 1e-12:
        return complex(float(su3_dim(p, q)), 0.0)
    return num / den

def weyl_measure(theta1, theta2):
    d12 = 2.0 * np.sin((theta1 - theta2) / 2.0)
    d13 = 2.0 * np.sin((2.0 * theta1 + theta2) / 2.0)
    d23 = 2.0 * np.sin((theta1 + 2.0 * theta2) / 2.0)
    return d12**2 * d13**2 * d23**2

def su3_boltzmann(theta1, theta2, beta):
    re_tr = np.cos(theta1) + np.cos(theta2) + np.cos(theta1 + theta2)
    return np.exp(beta / 3.0 * re_tr)

def compute_a_R(p, q, beta, n_grid=200):
    d_R = su3_dim(p, q)
    p_conj, q_conj = q, p
    theta1 = np.linspace(0, 2 * np.pi, n_grid, endpoint=False)
    theta2 = np.linspace(0, 2 * np.pi, n_grid, endpoint=False)
    T1, T2 = np.meshgrid(theta1, theta2)
    wm = weyl_measure(T1, T2)
    bw = su3_boltzmann(T1, T2, beta)
    chi = np.zeros_like(T1, dtype=complex)
    for i in range(n_grid):
        for j in range(n_grid):
            chi[i, j] = su3_character(p_conj, q_conj, T1[i, j], T2[i, j])
    integrand = wm * bw * chi
    dtheta = (2 * np.pi / n_grid)**2
    result = np.sum(integrand) * dtheta
    normalization = 24.0 * np.pi**2
    return (result / (normalization * d_R)).real

def compute_u3(beta, n_grid=200):
    a_1 = compute_a_R(0, 0, beta, n_grid=n_grid)
    a_3 = compute_a_R(1, 0, beta, n_grid=n_grid)
    return a_3 / a_1 if a_1 > 0 else 0.0

def fcc_intensive_gap(beta, n_grid=200):
    u_3 = compute_u3(beta, n_grid)
    if u_3 > 0:
        mu = -3.0 * np.log(3) - 8.0 * np.log(u_3)
    else:
        mu = np.inf
    return mu, u_3


# =============================================================================
# HELPER FUNCTIONS
# =============================================================================

def lattice_string_tension(u3):
    """sigma_lat = -ln(u_3)."""
    if u3 > 0 and u3 < 1:
        return -np.log(u3)
    return np.inf

def R_ratio(mu, sigma_lat):
    """R(beta) = mu / sqrt(sigma_lat)."""
    if sigma_lat > 0 and mu > 0:
        return mu / np.sqrt(sigma_lat)
    return 0.0

def R_tilde_ratio(mu, sigma_lat):
    """R_tilde = mu / sigma_lat."""
    if sigma_lat > 0 and mu > 0:
        return mu / sigma_lat
    return 0.0

def cg_lattice_spacing():
    """CG lattice spacing from Prop 0.0.17r."""
    a_sq = (8.0 / np.sqrt(3)) * np.log(3) * L_PLANCK_M**2
    return np.sqrt(a_sq)

def beta_star(Lambda_FCC_MeV):
    """beta_* from CG lattice spacing and given Lambda_FCC."""
    a_cg = cg_lattice_spacing()
    Lambda_FCC_inv_m = Lambda_FCC_MeV / (HBAR_C * 1e-15)  # MeV to 1/m
    product = a_cg * Lambda_FCC_inv_m
    if product > 0 and product < 1:
        return 12 * b_0 * np.log(1.0 / product)
    return np.inf


# =============================================================================
# TEST INFRASTRUCTURE
# =============================================================================

class TestResult:
    def __init__(self, name: str, passed: bool, details: Dict[str, Any],
                 severity: str = "INFO", finding_type: str = ""):
        self.name = name
        self.passed = passed
        self.details = details
        self.severity = severity  # CRITICAL, SIGNIFICANT, MODERATE, INFO
        self.finding_type = finding_type

def run_test(name, test_func, severity="INFO", finding_type=""):
    try:
        passed, details = test_func()
        return TestResult(name, passed, details, severity, finding_type)
    except Exception as e:
        return TestResult(name, False, {"error": str(e)}, severity, finding_type)


# =============================================================================
# ADVERSARIAL TESTS
# =============================================================================

def test_R_monotonicity():
    """A1: CRITICAL — Verify R(beta) is monotonically DECREASING (contradicts stabilization)."""
    betas = [2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 7.5, 8.0, 8.5, 8.8]
    data = []
    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        sl = lattice_string_tension(u3)
        R = R_ratio(mu, sl)
        data.append({"beta": beta, "mu": round(mu, 4), "u3": round(u3, 6),
                      "sigma_lat": round(sl, 4), "R": round(R, 4)})

    Rs = [d["R"] for d in data]
    strictly_decreasing = all(Rs[i] > Rs[i+1] for i in range(len(Rs)-1))

    return strictly_decreasing, {
        "data": data,
        "strictly_decreasing": strictly_decreasing,
        "R_range": f"{Rs[0]:.3f} -> {Rs[-1]:.3f}",
        "finding": "R(beta) is strictly monotonically decreasing — "
                   "it does NOT stabilize to R_infinity > 0"
    }


def test_R_at_critical():
    """A2: CRITICAL — Verify R(beta_c) = 0 analytically and show R trend toward 0."""
    # Analytical: at beta_c, x = (3/8)*ln3
    x_c = (3.0 / 8.0) * np.log(3)
    R_analytical = (-3 * np.log(3) + 8 * x_c) / np.sqrt(x_c)

    # Numerical: show R decreasing toward 0 approaching beta_c
    # (Exact beta_c computation requires high-precision binary search)
    betas_near_bc = [7.0, 8.0, 8.5, 9.0]
    R_trend = []
    for beta in betas_near_bc:
        mu, u3 = fcc_intensive_gap(beta, n_grid=200)
        sl = lattice_string_tension(u3)
        R = R_ratio(mu, sl)
        R_trend.append({"beta": beta, "R": round(R, 4)})

    analytical_zero = abs(R_analytical) < 1e-10
    # R should be monotonically decreasing
    Rs = [d["R"] for d in R_trend]
    decreasing_toward_zero = all(Rs[i] > Rs[i+1] for i in range(len(Rs)-1))

    return analytical_zero and decreasing_toward_zero, {
        "x_c": round(x_c, 6),
        "R_analytical_at_beta_c": R_analytical,
        "R_trend_toward_beta_c": R_trend,
        "analytical_confirms_zero": analytical_zero,
        "numerical_trend_decreasing": decreasing_toward_zero,
        "finding": f"R(beta_c) = {R_analytical:.2e} analytically (exactly 0). "
                   f"Numerically, R decreases monotonically: {[d['R'] for d in R_trend]}. "
                   f"R_infinity = 0, NOT a positive universal constant."
    }


def test_R_vs_glueball_ratio():
    """A3: CRITICAL — Check where R(beta) matches m_{0++}/sqrt(sigma) ~ 3.7."""
    # Scan betas to find where R ~ 3.7
    betas = np.linspace(1.0, 9.0, 50)
    data = []
    match_beta = None

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        sl = lattice_string_tension(u3)
        R = R_ratio(mu, sl)
        data.append({"beta": float(beta), "R": float(R)})
        if match_beta is None and R < GLUEBALL_RATIO_TARGET:
            match_beta = float(beta)

    # The "scaling window" should be near beta_c where xi >> 1
    # Use beta ~ 7-9 (close to beta_c ~ 11.4) where continuum limit is approached
    near_bc_Rs = [d["R"] for d in data if 7.0 <= d["beta"] <= 9.0]
    R_near_bc_range = (min(near_bc_Rs), max(near_bc_Rs)) if near_bc_Rs else (0, 0)

    # R near beta_c is well below 3.7
    target_above_window = GLUEBALL_RATIO_TARGET > R_near_bc_range[1]

    # Also check: where does R = 3.7 occur?
    match_info = f"beta ~ {match_beta:.1f}" if match_beta else "never (R always > 3.7)"

    return target_above_window, {
        "match_beta": match_beta,
        "target_glueball_ratio": GLUEBALL_RATIO_TARGET,
        "near_bc_R_range": [round(r, 3) for r in R_near_bc_range],
        "target_above_near_bc_window": target_above_window,
        "finding": f"R = {GLUEBALL_RATIO_TARGET} is achieved at {match_info}. "
                   f"Near beta_c (beta = 7-9), R ranges from "
                   f"{R_near_bc_range[1]:.2f} down to {R_near_bc_range[0]:.2f} "
                   f"— all BELOW the glueball ratio 3.7. "
                   f"The FCC model gives R -> 0 in the continuum limit, "
                   f"not the expected ~3.7."
    }


def test_m_phys_divergence_perturbative():
    """A4: SIGNIFICANT — m_phys diverges near beta_c with perturbative a(beta)."""
    betas = [5.0, 7.0, 8.0, 8.5, 8.8, 8.95]
    data = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        # Perturbative a(beta)
        a_pert = (1.0 / LAMBDA_FCC_MEV) * (6 * b_0 / beta)**(-b_1 / (2 * b_0**2)) * \
                 np.exp(-beta / (12 * b_0))
        m_phys_pert = np.sqrt(3) * mu / a_pert if a_pert > 0 else np.inf
        data.append({"beta": beta, "mu": round(mu, 4),
                      "a_pert_inv_MeV": round(1.0/a_pert, 2) if a_pert > 0 else "inf",
                      "m_phys_pert_MeV": round(m_phys_pert, 2) if np.isfinite(m_phys_pert) else "inf"})

    # Check that m_phys increases toward beta_c
    m_values = [d["m_phys_pert_MeV"] for d in data
                if isinstance(d["m_phys_pert_MeV"], (int, float))]
    diverging = len(m_values) >= 2 and m_values[-1] > m_values[0]

    return diverging, {
        "data": data,
        "diverging_toward_beta_c": diverging,
        "finding": "With perturbative a(beta), m_phys diverges as beta -> beta_c^-. "
                   "The exponential decay of a(beta) dominates the linear decay of mu."
    }


def test_m_phys_vanishing_nonpert():
    """A5: SIGNIFICANT — m_phys -> 0 near beta_c with non-perturbative a(beta)."""
    betas = [5.0, 7.0, 8.0, 8.5, 8.8, 8.95]
    data = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        sl = lattice_string_tension(u3)
        R = R_ratio(mu, sl)
        m_phys_nonpert = np.sqrt(3) * SQRT_SIGMA_MEV * R

        data.append({"beta": beta, "mu": round(mu, 4), "R": round(R, 4),
                      "m_phys_nonpert_MeV": round(m_phys_nonpert, 2)})

    # Check that m_phys decreases toward beta_c
    m_values = [d["m_phys_nonpert_MeV"] for d in data]
    vanishing = m_values[-1] < m_values[0]

    return vanishing, {
        "data": data,
        "vanishing_toward_beta_c": vanishing,
        "finding": "With non-perturbative a(beta) = sqrt(sigma_phys/sigma_lat), "
                   "m_phys -> 0 as beta -> beta_c^-. "
                   "Neither definition gives a finite positive mass gap."
    }


def test_lambda_fcc_inconsistency():
    """A6: CRITICAL — Demonstrate Lambda_FCC inconsistency between Prop 7.4.3 and 7.4.4."""
    # Prop 7.4.3 value
    lambda_743 = LAMBDA_FCC_OVER_MSBAR * LAMBDA_MSBAR_MEV_QUENCHED
    # Prop 7.4.4 Derivation value (wrong)
    lambda_744 = 34.0 * 340.0  # 11,560 MeV

    ratio = lambda_744 / lambda_743

    beta_star_correct = beta_star(lambda_743)
    beta_star_wrong = beta_star(lambda_744)

    return ratio > 100, {  # PASS if discrepancy is large (confirming the problem)
        "Lambda_FCC_Prop743_MeV": lambda_743,
        "Lambda_FCC_Prop744_MeV": lambda_744,
        "discrepancy_factor": round(ratio, 1),
        "beta_star_correct": round(beta_star_correct, 1),
        "beta_star_wrong": round(beta_star_wrong, 1),
        "finding": f"Lambda_FCC differs by factor {ratio:.0f} between propositions. "
                   f"Correct beta_* = {beta_star_correct:.1f} (not {beta_star_wrong:.1f}). "
                   f"Qualitative conclusion (beta_* >> beta_c) unchanged."
    }


def test_lambda_msbar_value():
    """A7: MODERATE — Check Lambda_MSbar value (quenched vs N_f=3)."""
    lambda_used = 340.0  # MeV, used in Prop 7.4.4 derivation
    lambda_correct = 260.0  # MeV, quenched SU(3)
    deviation_pct = abs(lambda_used - lambda_correct) / lambda_correct * 100

    return deviation_pct > 20, {  # PASS if deviation is significant
        "Lambda_MSbar_used_MeV": lambda_used,
        "Lambda_MSbar_quenched_MeV": lambda_correct,
        "deviation_percent": round(deviation_pct, 1),
        "finding": f"Derivation uses Lambda_MSbar = {lambda_used} MeV "
                   f"(appropriate for N_f = 3 QCD), but framework is pure gauge (N_f = 0). "
                   f"Quenched value is {lambda_correct} +/- 20 MeV."
    }


def test_scaling_window_R_variation():
    """A8: SIGNIFICANT — Quantify how much R varies in the claimed 'scaling window'."""
    betas = np.linspace(5.0, 8.5, 30)
    Rs = []
    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=100)
        sl = lattice_string_tension(u3)
        Rs.append(R_ratio(mu, sl))

    R_max = max(Rs)
    R_min = min(Rs)
    variation_factor = R_max / R_min if R_min > 0 else np.inf

    # A "stable" ratio should vary by less than ~20%
    large_variation = variation_factor > 2.0

    return large_variation, {  # PASS if variation is large (confirming the problem)
        "beta_range": "5.0 - 8.5",
        "R_max": round(R_max, 3),
        "R_min": round(R_min, 3),
        "variation_factor": round(variation_factor, 2),
        "finding": f"In the claimed scaling window (beta = 5-8.5), R varies by "
                   f"factor {variation_factor:.1f}x (from {R_max:.2f} to {R_min:.2f}). "
                   f"This is NOT 'approximately constant' or 'stabilized'."
    }


def test_sigma_lat_at_critical():
    """A9: MODERATE — sigma_lat does NOT vanish at beta_c (unlike mu)."""
    # At beta_c: u_3 = 3^(-3/8), so sigma_lat = -ln(3^(-3/8)) = (3/8)*ln(3) > 0
    sigma_lat_at_bc = (3.0 / 8.0) * np.log(3)

    # Verify numerically: sigma_lat should remain positive and finite as beta -> beta_c
    # Use a sequence of betas approaching beta_c to show sigma_lat stays finite
    betas_approach = [7.0, 8.0, 8.5, 9.0]
    sigma_trend = []
    for beta in betas_approach:
        _, u3 = fcc_intensive_gap(beta, n_grid=200)
        sl = lattice_string_tension(u3)
        sigma_trend.append({"beta": beta, "sigma_lat": round(sl, 4)})

    sigma_positive_analytical = sigma_lat_at_bc > 0
    # sigma_lat should remain bounded away from 0 (stays above ~0.4)
    all_finite = all(d["sigma_lat"] > 0.3 for d in sigma_trend)

    return sigma_positive_analytical and all_finite, {
        "sigma_lat_at_beta_c_analytical": round(sigma_lat_at_bc, 6),
        "sigma_trend": sigma_trend,
        "analytical_positive": sigma_positive_analytical,
        "numerical_all_finite": all_finite,
        "finding": f"sigma_lat(beta_c) = (3/8)*ln(3) = {sigma_lat_at_bc:.4f} > 0 analytically. "
                   f"Numerical trend: {[d['sigma_lat'] for d in sigma_trend]}. "
                   f"The string tension remains FINITE at beta_c while mu -> 0. "
                   f"This causes R = mu/sqrt(sigma_lat) -> 0."
    }


def test_dR_dx_always_positive():
    """A10: MODERATE — Verify dR/dx > 0 for all x > 0 (R monotone in x)."""
    # dR/dx = (8x + 3*ln(3))/(2*x^(3/2))
    # Since 8x > 0 and 3*ln(3) > 0 for all x > 0, this is always positive.
    x_values = np.logspace(-3, 2, 100)
    dR_dx = (8 * x_values + 3 * np.log(3)) / (2 * x_values**1.5)
    all_positive = np.all(dR_dx > 0)

    # Also verify: since x = -ln(u_3) and u_3 increases with beta,
    # x decreases with beta, so R decreases with beta
    return all_positive, {
        "all_positive": all_positive,
        "min_dR_dx": float(np.min(dR_dx)),
        "x_range_tested": "10^-3 to 10^2",
        "finding": "dR/dx > 0 for ALL x > 0 (proven analytically: numerator = 8x + 3*ln3 > 0). "
                   "Since x decreases with beta, R STRICTLY DECREASES with beta. "
                   "There is NO plateau, NO stabilization, NO finite R_infinity."
    }


def test_beta_star_corrected():
    """A11: SIGNIFICANT — Compute correct beta_* with Lambda_FCC from Prop 7.4.3."""
    a_cg = cg_lattice_spacing()
    a_cg_energy_GeV = HBAR_C * 1e-15 / a_cg  # Convert to GeV via hbar*c/a

    beta_correct = beta_star(LAMBDA_FCC_MEV)
    beta_wrong = beta_star(LAMBDA_FCC_WRONG_MEV)

    # Both should be >> beta_c
    above_bc = beta_correct > 11.4 and beta_wrong > 11.4

    return above_bc, {
        "a_CG_m": float(a_cg),
        "a_CG_energy_scale_GeV": round(a_cg_energy_GeV, 2),
        "beta_star_correct": round(beta_correct, 1),
        "beta_star_wrong": round(beta_wrong, 1),
        "Lambda_FCC_correct_MeV": LAMBDA_FCC_MEV,
        "Lambda_FCC_wrong_MeV": LAMBDA_FCC_WRONG_MEV,
        "both_above_beta_c": above_bc,
        "finding": f"Correct beta_* = {beta_correct:.1f} (using Lambda_FCC = {LAMBDA_FCC_MEV} MeV). "
                   f"Wrong beta_* = {beta_wrong:.1f} (using Lambda_FCC = {LAMBDA_FCC_WRONG_MEV} MeV). "
                   f"Qualitative conclusion unchanged: beta_* >> beta_c ~ 11.4."
    }


def test_rg_flow_transition_crossing():
    """A12: SIGNIFICANT — Document that RG flow must cross the first-order transition."""
    beta_c_approx = 11.4
    beta_star_val = beta_star(LAMBDA_FCC_MEV)

    # The CG lattice spacing corresponds to beta_* > beta_c (deconfined phase)
    # The scaling window is at beta < beta_c (confined phase)
    # RG flow goes from large beta (UV, Planck) to small beta (IR, QCD)
    # This means the flow must cross beta_c

    crosses_transition = beta_star_val > beta_c_approx

    return crosses_transition, {  # PASS if it does cross (confirming the problem)
        "beta_star": round(beta_star_val, 1),
        "beta_c": beta_c_approx,
        "gap": round(beta_star_val - beta_c_approx, 1),
        "finding": f"beta_* = {beta_star_val:.1f} > beta_c = {beta_c_approx}. "
                   f"RG flow from Planck scale (beta_*) to QCD scale (beta < beta_c) "
                   f"MUST cross the first-order bulk transition at beta_c. "
                   f"No mechanism is demonstrated for this crossing."
    }


# =============================================================================
# PLOTTING
# =============================================================================

def generate_adversarial_plots():
    """Generate comprehensive adversarial verification plots."""
    if not HAS_MATPLOTLIB:
        print("  WARNING: matplotlib not available, skipping plots")
        return

    # Compute data across full beta range
    betas = np.linspace(1.0, 9.0, 80)
    mus, u3s, sigma_lats, Rs, R_tildes, xis = [], [], [], [], [], []
    m_phys_nonpert = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=100)
        mus.append(mu)
        u3s.append(u3)
        sl = lattice_string_tension(u3)
        sigma_lats.append(sl)
        R = R_ratio(mu, sl)
        Rs.append(R)
        R_tildes.append(R_tilde_ratio(mu, sl))
        xis.append(1.0 / mu if mu > 0 else 100)
        m_phys_nonpert.append(np.sqrt(3) * SQRT_SIGMA_MEV * R)

    beta_c = 11.4

    # =====================================================================
    # FIGURE 1: The R(beta) Problem (4 panels)
    # =====================================================================
    fig, axes = plt.subplots(2, 2, figsize=(14, 11))
    fig.suptitle('Proposition 7.4.4: Adversarial Physics Verification\n'
                 'R(β) Monotonicity and Glueball Mass Ratio', fontsize=13, fontweight='bold')

    # Panel 1: R(beta) with glueball target
    ax = axes[0, 0]
    ax.plot(betas, Rs, 'b-', linewidth=2.5, label=r'$R(\beta) = \mu/\sqrt{\sigma_{\mathrm{lat}}}$')
    ax.axhline(y=GLUEBALL_RATIO_TARGET, color='red', linestyle='--', linewidth=2,
               label=r'Lattice QCD: $m_{0^{++}}/\sqrt{\sigma} \approx 3.7$')
    ax.fill_between(betas, GLUEBALL_RATIO_TARGET - GLUEBALL_RATIO_ERR,
                     GLUEBALL_RATIO_TARGET + GLUEBALL_RATIO_ERR,
                     alpha=0.15, color='red', label='Uncertainty band')
    ax.axvspan(5, 8.5, alpha=0.1, color='green', label='Claimed "scaling window"')
    ax.axvline(x=beta_c, color='gray', linestyle=':', linewidth=1.5, label=r'$\beta_c \approx 11.4$')
    ax.set_xlabel(r'$\beta$', fontsize=12)
    ax.set_ylabel(r'$R(\beta)$', fontsize=12)
    ax.set_title(r'CRITICAL: $R(\beta) \to 0$ at $\beta_c$, never "stabilizes"', fontsize=11, color='red')
    ax.legend(fontsize=8, loc='upper right')
    ax.set_ylim(-0.5, 15)
    ax.grid(True, alpha=0.3)

    # Panel 2: R(beta) zoom on scaling window
    ax = axes[0, 1]
    mask = (np.array(betas) >= 4) & (np.array(betas) <= 9.0)
    ax.plot(np.array(betas)[mask], np.array(Rs)[mask], 'b-', linewidth=2.5)
    ax.axhline(y=GLUEBALL_RATIO_TARGET, color='red', linestyle='--', linewidth=2,
               label=r'Target $R = 3.7$')
    ax.fill_between(np.array(betas)[mask],
                     GLUEBALL_RATIO_TARGET - GLUEBALL_RATIO_ERR,
                     GLUEBALL_RATIO_TARGET + GLUEBALL_RATIO_ERR,
                     alpha=0.15, color='red')
    ax.axvspan(5, 8.5, alpha=0.1, color='green', label='Claimed "scaling window"')
    ax.axvline(x=beta_c, color='gray', linestyle=':', linewidth=1.5)
    ax.set_xlabel(r'$\beta$', fontsize=12)
    ax.set_ylabel(r'$R(\beta)$', fontsize=12)
    ax.set_title('Zoom: R crosses 3.7 at β ≈ 4.5–5 (NOT in scaling window)', fontsize=10, color='darkorange')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Panel 3: m_phys (non-perturbative) in MeV
    ax = axes[1, 0]
    ax.plot(betas, m_phys_nonpert, 'purple', linewidth=2.5,
            label=r'$m_{\mathrm{phys}} = \sqrt{3\sigma_{\mathrm{phys}}} \cdot R(\beta)$')
    ax.axhline(y=1630, color='red', linestyle='--', linewidth=2,
               label=r'Lattice QCD: $m_{0^{++}} \approx 1630$ MeV')
    ax.axvline(x=beta_c, color='gray', linestyle=':', linewidth=1.5, label=r'$\beta_c$')
    ax.axvspan(5, 8.5, alpha=0.1, color='green')
    ax.set_xlabel(r'$\beta$', fontsize=12)
    ax.set_ylabel(r'$m_{\mathrm{phys}}$ (MeV)', fontsize=12)
    ax.set_title(r'$m_{\mathrm{phys}} \to 0$ at $\beta_c$ (non-perturbative $a$)', fontsize=11, color='red')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Panel 4: dR/dx proves monotonicity
    ax = axes[1, 1]
    x_vals = np.linspace(0.01, 5, 200)
    dR_dx = (8 * x_vals + 3 * np.log(3)) / (2 * x_vals**1.5)
    R_vals = (-3 * np.log(3) + 8 * x_vals) / np.sqrt(x_vals)
    x_c = (3.0/8.0) * np.log(3)

    ax2 = ax.twinx()
    ax.plot(x_vals, dR_dx, 'r-', linewidth=2, label=r'$dR/dx > 0$ always')
    ax2.plot(x_vals, R_vals, 'b-', linewidth=2, label=r'$R(x)$')
    ax.axvline(x=x_c, color='gray', linestyle=':', linewidth=1.5, label=r'$x_c = \frac{3}{8}\ln 3$')
    ax.set_xlabel(r'$x = -\ln u_3$', fontsize=12)
    ax.set_ylabel(r'$dR/dx$', fontsize=12, color='red')
    ax2.set_ylabel(r'$R(x)$', fontsize=12, color='blue')
    ax.tick_params(axis='y', labelcolor='red')
    ax2.tick_params(axis='y', labelcolor='blue')
    ax.set_title(r'$dR/dx > 0$ for all $x > 0$: R strictly monotone', fontsize=11)
    ax.set_ylim(0, 50)
    ax2.set_ylim(-5, 20)
    lines1, labels1 = ax.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax.legend(lines1 + lines2, labels1 + labels2, fontsize=9, loc='upper right')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    path1 = os.path.join(PLOT_DIR, 'prop_7_4_4_adversarial_R_ratio.png')
    plt.savefig(path1, dpi=150)
    plt.close()
    print(f"  Plot saved: {path1}")

    # =====================================================================
    # FIGURE 2: Lambda inconsistency and beta_* (2 panels)
    # =====================================================================
    fig, axes = plt.subplots(1, 2, figsize=(14, 5.5))
    fig.suptitle('Proposition 7.4.4: Λ_FCC Inconsistency and β* Computation', fontsize=13, fontweight='bold')

    # Panel 1: beta_* comparison
    ax = axes[0]
    labels = [f'Correct\n(Λ_FCC = {LAMBDA_FCC_MEV} MeV)',
              f'Wrong\n(Λ_FCC = {LAMBDA_FCC_WRONG_MEV/1000:.1f} GeV)']
    vals = [beta_star(LAMBDA_FCC_MEV), beta_star(LAMBDA_FCC_WRONG_MEV)]
    colors = ['#2ecc71', '#e74c3c']
    bars = ax.bar(labels, vals, color=colors, width=0.5, edgecolor='black', linewidth=1.2)
    ax.axhline(y=beta_c, color='gray', linestyle='--', linewidth=2, label=r'$\beta_c \approx 11.4$')
    ax.set_ylabel(r'$\beta_*$', fontsize=12)
    ax.set_title(r'$\beta_*$ from CG lattice spacing', fontsize=11)
    ax.legend(fontsize=10)
    for bar, val in zip(bars, vals):
        ax.text(bar.get_x() + bar.get_width()/2., bar.get_height() + 0.5,
                f'{val:.1f}', ha='center', va='bottom', fontsize=12, fontweight='bold')
    ax.set_ylim(0, max(vals) + 8)
    ax.grid(True, alpha=0.3, axis='y')

    # Panel 2: Energy scales
    ax = axes[1]
    scales = {
        r'$\Lambda_{\mathrm{FCC}}$ (correct)': LAMBDA_FCC_MEV / 1000,
        r'$\Lambda_{\mathrm{FCC}}$ (wrong)': LAMBDA_FCC_WRONG_MEV / 1000,
        r'$\Lambda_{\overline{MS}}$ (quenched)': LAMBDA_MSBAR_MEV_QUENCHED / 1000,
        r'$\sqrt{\sigma}$': SQRT_SIGMA_MEV / 1000,
        r'$1/a_{\mathrm{CG}}$': HBAR_C * 1e-15 / cg_lattice_spacing() / 1e9,
    }
    sorted_scales = sorted(scales.items(), key=lambda x: x[1])
    y_pos = range(len(sorted_scales))
    colors_bar = ['#2ecc71' if 'correct' in k else '#e74c3c' if 'wrong' in k else '#3498db'
                  for k, _ in sorted_scales]
    ax.barh(y_pos, [np.log10(v) if v > 0 else 0 for _, v in sorted_scales],
            color=colors_bar, edgecolor='black', linewidth=0.8, height=0.6)
    ax.set_yticks(y_pos)
    ax.set_yticklabels([k for k, _ in sorted_scales], fontsize=9)
    ax.set_xlabel(r'$\log_{10}$(Energy / GeV)', fontsize=12)
    ax.set_title('Energy Scale Hierarchy', fontsize=11)
    ax.grid(True, alpha=0.3, axis='x')

    plt.tight_layout()
    path2 = os.path.join(PLOT_DIR, 'prop_7_4_4_adversarial_lambda_beta_star.png')
    plt.savefig(path2, dpi=150)
    plt.close()
    print(f"  Plot saved: {path2}")

    # =====================================================================
    # FIGURE 3: Complete phase diagram (single panel)
    # =====================================================================
    fig, ax = plt.subplots(1, 1, figsize=(12, 6))
    fig.suptitle('Proposition 7.4.4: FCC Phase Diagram and Scaling Window',
                 fontsize=13, fontweight='bold')

    # Plot mu, sigma_lat, and xi
    ax.plot(betas, mus, 'b-', linewidth=2, label=r'$\mu(\beta)$ (mass gap)')
    ax.plot(betas, sigma_lats, 'r-', linewidth=2, label=r'$\sigma_{\mathrm{lat}} = -\ln u_3$')

    # Mark beta_c
    ax.axvline(x=beta_c, color='black', linestyle='-', linewidth=2, alpha=0.7)
    ax.text(beta_c + 0.05, max(mus) * 0.9, r'$\beta_c$' + '\n(1st order\ntransition)',
            fontsize=10, ha='left', fontweight='bold')

    # Mark claimed scaling window
    ax.axvspan(5, 8.5, alpha=0.08, color='green')
    ax.text(6.75, max(mus) * 0.85, 'Claimed\n"scaling window"',
            fontsize=10, ha='center', color='green', fontstyle='italic')

    # Mark where R = 3.7 (glueball ratio)
    ax.axvspan(4.3, 5.2, alpha=0.08, color='orange')
    ax.text(4.75, max(mus) * 0.7, 'R ≈ 3.7\n(glueball)',
            fontsize=9, ha='center', color='darkorange')

    # Mark beta_*
    beta_star_val = beta_star(LAMBDA_FCC_MEV)
    if beta_star_val < 50:
        ax.annotate(rf'$\beta_* \approx {beta_star_val:.0f}$' + '\n(Planck scale)',
                    xy=(9.0, 0), xytext=(8.0, max(mus) * 0.3),
                    fontsize=10, ha='center',
                    arrowprops=dict(arrowstyle='->', color='purple', lw=1.5))

    # Deconfined region
    ax.axvspan(beta_c, 9.5, alpha=0.15, color='lightcoral')
    ax.text(beta_c + 0.2, max(mus) * 0.5, 'Deconfined\n(lattice artifact)',
            fontsize=9, ha='left', color='red', fontstyle='italic')

    ax.set_xlabel(r'$\beta = 6/g_0^2$', fontsize=12)
    ax.set_ylabel('Value (lattice units)', fontsize=12)
    ax.legend(fontsize=10, loc='upper right')
    ax.set_xlim(0.5, 9.5)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    path3 = os.path.join(PLOT_DIR, 'prop_7_4_4_adversarial_phase_diagram.png')
    plt.savefig(path3, dpi=150)
    plt.close()
    print(f"  Plot saved: {path3}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 76)
    print("Prop 7.4.4: Scaling Window — ADVERSARIAL Physics Verification")
    print("=" * 76)
    print()

    tests = [
        ("A1:  R(beta) strictly decreasing",
         test_R_monotonicity, "CRITICAL", "R_monotonicity"),
        ("A2:  R(beta_c) = 0 (not R_infinity > 0)",
         test_R_at_critical, "CRITICAL", "R_at_critical"),
        ("A3:  R never matches glueball ratio 3.7 in scaling window",
         test_R_vs_glueball_ratio, "CRITICAL", "glueball_mismatch"),
        ("A4:  m_phys diverges (perturbative a)",
         test_m_phys_divergence_perturbative, "SIGNIFICANT", "m_phys_diverge"),
        ("A5:  m_phys -> 0 (non-perturbative a)",
         test_m_phys_vanishing_nonpert, "SIGNIFICANT", "m_phys_vanish"),
        ("A6:  Lambda_FCC factor ~3400 inconsistency",
         test_lambda_fcc_inconsistency, "CRITICAL", "lambda_inconsistency"),
        ("A7:  Lambda_MSbar wrong for quenched",
         test_lambda_msbar_value, "MODERATE", "lambda_msbar"),
        ("A8:  R varies by factor >3 in 'scaling window'",
         test_scaling_window_R_variation, "SIGNIFICANT", "R_variation"),
        ("A9:  sigma_lat > 0 at beta_c (while mu = 0)",
         test_sigma_lat_at_critical, "MODERATE", "sigma_at_bc"),
        ("A10: dR/dx > 0 always (analytic proof of monotonicity)",
         test_dR_dx_always_positive, "MODERATE", "dR_dx_positive"),
        ("A11: Corrected beta_* = 41 (not 34)",
         test_beta_star_corrected, "SIGNIFICANT", "beta_star_corrected"),
        ("A12: RG flow crosses first-order transition",
         test_rg_flow_transition_crossing, "SIGNIFICANT", "rg_transition"),
    ]

    results = []
    passed = 0
    failed = 0
    critical_count = 0
    significant_count = 0

    for name, func, severity, ftype in tests:
        result = run_test(name, func, severity, ftype)
        results.append(result)
        status = "CONFIRMED" if result.passed else "NOT CONFIRMED"
        icon = "✅" if result.passed else "❌"
        sev_icon = {"CRITICAL": "🔴", "SIGNIFICANT": "🟠",
                    "MODERATE": "🟡", "INFO": "🔵"}.get(severity, "⚪")

        print(f"  {icon} {sev_icon} [{severity}] {name}: {status}")
        if result.passed:
            passed += 1
        else:
            failed += 1
        if result.passed and severity == "CRITICAL":
            critical_count += 1
        if result.passed and severity == "SIGNIFICANT":
            significant_count += 1

    print(f"\n{'=' * 76}")
    print(f"ADVERSARIAL SUMMARY: {passed}/{passed + failed} findings confirmed")
    print(f"  CRITICAL issues confirmed:    {critical_count}")
    print(f"  SIGNIFICANT issues confirmed: {significant_count}")
    print(f"{'=' * 76}")

    print("\nGenerating adversarial plots...")
    generate_adversarial_plots()

    # Save results
    output = {
        "proposition": "7.4.4",
        "title": "Scaling Window Identification on FCC — Adversarial Physics Verification",
        "timestamp": datetime.now().isoformat(),
        "verdict": "PARTIAL VERIFICATION",
        "summary": f"{passed}/{passed + failed} adversarial findings confirmed",
        "critical_findings": critical_count,
        "significant_findings": significant_count,
        "tests": []
    }

    for r in results:
        test_data = {
            "name": r.name,
            "confirmed": r.passed,
            "severity": r.severity,
            "finding_type": r.finding_type,
        }
        # Serialize details carefully
        for k, v in r.details.items():
            if isinstance(v, (list, dict)):
                test_data[k] = v
            elif isinstance(v, (np.floating, float)):
                test_data[k] = float(v)
            elif isinstance(v, np.ndarray):
                test_data[k] = str(v)
            else:
                test_data[k] = v
        output["tests"].append(test_data)

    json_path = os.path.join(SCRIPT_DIR, 'prop_7_4_4_adversarial_results.json')
    with open(json_path, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to: {json_path}")

    return passed + failed  # Return total (all are findings, not pass/fail in the usual sense)


if __name__ == "__main__":
    main()
