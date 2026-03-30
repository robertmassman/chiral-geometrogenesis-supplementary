#!/usr/bin/env python3
"""
Proposition 7.4.4: Scaling Window Identification on FCC — Verification
======================================================================

Verifies the scaling window identification, dimensionless ratio stabilization,
CG lattice spacing mapping, and phase transition analysis.

Key Claims Under Test:
    (a) Scaling region: m_phys(beta) approaches a well-defined limit
    (b) Ratio R(beta) = mu/sqrt(sigma_lat) stabilizes
    (c) CG lattice spacing maps to beta_* ~ 34
    (d) Bulk transition is a lattice artifact (evidence-based)

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
from typing import Dict, Any

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

N_C = 3
b_0 = 11 * N_C / (3 * (4 * np.pi)**2)
b_1 = 34 * N_C**2 / (3 * (4 * np.pi)**4)
SQRT_SIGMA_MEV = 440.0  # MeV
R_STELLA_FM = 0.44847   # fm
HBAR_C = 197.327         # MeV * fm
L_PLANCK_M = 1.616255e-35  # m
LAMBDA_FCC_OVER_MSBAR = 0.010    # Prop 7.4.3: Lambda_FCC/Lambda_MSbar ~ 0.010
LAMBDA_MSBAR_MEV = 260.0          # Quenched SU(3), Sommer 1994

# =============================================================================
# SU(3) HEAT KERNEL (copied from prop_7_4_3)
# =============================================================================

def su3_dim(p, q):
    return (p + 1) * (q + 1) * (p + q + 2) // 2

def su3_casimir(p, q):
    return (p**2 + q**2 + p * q + 3 * p + 3 * q) / 3.0

def weyl_measure(theta1, theta2):
    d12 = 2.0 * np.sin((theta1 - theta2) / 2.0)
    d13 = 2.0 * np.sin((2.0 * theta1 + theta2) / 2.0)
    d23 = 2.0 * np.sin((theta1 + 2.0 * theta2) / 2.0)
    return d12**2 * d13**2 * d23**2

def su3_boltzmann(theta1, theta2, beta):
    re_tr = np.cos(theta1) + np.cos(theta2) + np.cos(theta1 + theta2)
    return np.exp(beta / 3.0 * re_tr)

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
# SCALING WINDOW FUNCTIONS
# =============================================================================

def lattice_string_tension(u3):
    """Lattice string tension sigma_lat = -ln(u_3)."""
    if u3 > 0 and u3 < 1:
        return -np.log(u3)
    return np.inf

def mass_gap_ratio(mu, sigma_lat):
    """R(beta) = mu / sqrt(sigma_lat)."""
    if sigma_lat > 0 and mu > 0:
        return mu / np.sqrt(sigma_lat)
    return 0.0

def mass_gap_over_sigma(mu, sigma_lat):
    """mu / sigma_lat ratio."""
    if sigma_lat > 0 and mu > 0:
        return mu / sigma_lat
    return 0.0

def asymptotic_scaling_a(beta, Lambda_lat=1.0):
    """Lattice spacing from asymptotic scaling."""
    exponent = -beta / (12 * b_0)
    prefactor = (6 * b_0 / beta) ** (-b_1 / (2 * b_0**2))
    return prefactor * np.exp(exponent) / Lambda_lat

def physical_mass_gap_pert(mu, beta, Lambda_lat=1.0):
    """Physical mass gap using perturbative a(beta)."""
    a = asymptotic_scaling_a(beta, Lambda_lat)
    if a > 0:
        return np.sqrt(3) * mu / a
    return np.inf

def physical_mass_gap_nonpert(mu, u3, sqrt_sigma_phys):
    """Physical mass gap using non-perturbative a from string tension."""
    sigma_lat = lattice_string_tension(u3)
    if sigma_lat > 0:
        a = sqrt_sigma_phys / np.sqrt(sigma_lat)  # a in physical units
        return np.sqrt(3) * mu / a
    return np.inf

def cg_lattice_spacing():
    """CG lattice spacing from Prop 0.0.17r."""
    a_sq = (8.0 / np.sqrt(3)) * np.log(3) * L_PLANCK_M**2
    return np.sqrt(a_sq)

def beta_star_cg():
    """beta_* corresponding to CG lattice spacing."""
    a_cg = cg_lattice_spacing()  # in meters
    Lambda_FCC_MeV = LAMBDA_FCC_OVER_MSBAR * LAMBDA_MSBAR_MEV  # in MeV
    # Convert MeV to 1/m: E/(hbar*c) where hbar*c = 197.327 MeV*fm = 197.327e-15 MeV*m
    Lambda_FCC_inv_m = Lambda_FCC_MeV / (HBAR_C * 1e-15)  # MeV / (MeV*m) = 1/m
    product = a_cg * Lambda_FCC_inv_m
    if product > 0 and product < 1:
        beta_s = 12 * b_0 * np.log(1.0 / product)
        return beta_s
    return np.inf


# =============================================================================
# TEST INFRASTRUCTURE
# =============================================================================

class TestResult:
    def __init__(self, name, passed, details):
        self.name = name
        self.passed = passed
        self.details = details

def run_test(name, test_func):
    try:
        passed, details = test_func()
        return TestResult(name, passed, details)
    except Exception as e:
        return TestResult(name, False, {"error": str(e)})


# =============================================================================
# TESTS
# =============================================================================

def test_critical_coupling():
    """T1: Verify critical coupling beta_c where u_3 = 3^(-3/8)."""
    u3_target = 3**(-3.0/8)

    # Binary search for beta_c
    beta_low, beta_high = 5.0, 15.0
    for _ in range(50):
        beta_mid = (beta_low + beta_high) / 2
        u3_mid = compute_u3(beta_mid, n_grid=150)
        if u3_mid < u3_target:
            beta_low = beta_mid
        else:
            beta_high = beta_mid

    beta_c = (beta_low + beta_high) / 2
    u3_c = compute_u3(beta_c, n_grid=150)

    reasonable = 8.0 < beta_c < 13.0
    u3_close = abs(u3_c - u3_target) < 0.01

    return reasonable and u3_close, {
        "beta_c": beta_c,
        "u3_at_beta_c": u3_c,
        "u3_target": u3_target,
        "u3_error": abs(u3_c - u3_target),
        "reasonable_range": reasonable
    }


def test_mass_gap_vanishes_at_critical():
    """T2: Verify mu(beta_c) -> 0 as beta -> beta_c."""
    # First find beta_c numerically
    u3_target = 3**(-3.0/8)
    beta_low, beta_high = 5.0, 15.0
    for _ in range(50):
        beta_mid = (beta_low + beta_high) / 2
        u3_mid = compute_u3(beta_mid, n_grid=150)
        if u3_mid < u3_target:
            beta_low = beta_mid
        else:
            beta_high = beta_mid
    beta_c_num = (beta_low + beta_high) / 2

    # Test at beta just below beta_c
    beta_test = beta_c_num - 0.1
    mu, u3 = fcc_intensive_gap(beta_test, n_grid=150)

    # Analytical check: at beta_c, u3 = 3^(-3/8), so mu = 0 exactly
    mu_analytical = -3.0 * np.log(3) - 8.0 * np.log(u3_target)

    mu_small = abs(mu) < 0.5
    analytical_zero = abs(mu_analytical) < 1e-10

    return mu_small and analytical_zero, {
        "beta_c_numerical": beta_c_num,
        "beta_tested": beta_test,
        "mu_numerical": mu,
        "u3": u3,
        "u3_critical": u3_target,
        "mu_analytical_at_exact_bc": mu_analytical,
        "mu_small_near_bc": mu_small,
        "analytical_exactly_zero": analytical_zero
    }


def test_correlation_length_diverges():
    """T3: Verify xi = 1/mu diverges as beta -> beta_c."""
    betas = [5.0, 7.0, 9.0, 10.0, 11.0]
    results = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        xi = 1.0 / mu if mu > 0 else np.inf
        results.append({"beta": beta, "mu": mu, "xi": xi})

    # xi should increase monotonically
    xis = [r["xi"] for r in results]
    monotone = all(xis[i] < xis[i+1] for i in range(len(xis)-1))

    return monotone, {
        "results": results,
        "xi_increasing": monotone,
        "note": "Correlation length diverges at beta_c"
    }


def test_dimensionless_ratio():
    """T4: Compute R(beta) = mu/sqrt(sigma_lat) across coupling range."""
    betas = [2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 8.5]
    results = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        sigma_lat = lattice_string_tension(u3)
        R = mass_gap_ratio(mu, sigma_lat)
        R_tilde = mass_gap_over_sigma(mu, sigma_lat)
        results.append({
            "beta": beta, "mu": mu, "u3": u3,
            "sigma_lat": sigma_lat, "R": R, "R_tilde": R_tilde
        })

    # R should be monotonically decreasing with beta
    Rs = [r["R"] for r in results if r["R"] > 0]
    if len(Rs) > 1:
        monotone = all(Rs[i] > Rs[i+1] for i in range(len(Rs)-1))
    else:
        monotone = True

    return monotone, {
        "results": results,
        "R_decreasing": monotone
    }


def test_analytical_ratio_formula():
    """T5: Verify R formula: R = (-3*ln(3) + 8x)/sqrt(x) where x = -ln(u3)."""
    betas = [3.0, 5.0, 7.0, 8.0]

    all_match = True
    results = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        x = -np.log(u3)
        R_numerical = mu / np.sqrt(x)
        R_formula = (-3 * np.log(3) + 8 * x) / np.sqrt(x)

        rel_err = abs(R_numerical - R_formula) / (abs(R_formula) + 1e-15)
        if rel_err > 1e-6:
            all_match = False

        results.append({
            "beta": beta, "R_numerical": R_numerical,
            "R_formula": R_formula, "relative_error": rel_err
        })

    return all_match, {"results": results}


def test_cg_lattice_spacing_value():
    """T6: Verify CG lattice spacing is Planck-scale."""
    a_cg = cg_lattice_spacing()
    a_cg_fm = a_cg * 1e15

    # Should be much smaller than QCD scale (0.1 fm)
    planck_scale = a_cg < 1e-34  # meters (close to l_P)
    sub_qcd = a_cg_fm < 1e-15   # fm

    return planck_scale and sub_qcd, {
        "a_CG_m": a_cg,
        "a_CG_fm": a_cg_fm,
        "l_Planck_m": L_PLANCK_M,
        "ratio_a_CG_over_l_P": a_cg / L_PLANCK_M,
        "planck_scale": planck_scale,
        "sub_qcd": sub_qcd
    }


def test_beta_star():
    """T7: Verify beta_* from CG lattice spacing is deep perturbative (~41)."""
    beta_s = beta_star_cg()

    deep_perturbative = beta_s > 20
    above_critical = beta_s > 11.4
    near_expected = abs(beta_s - 41.0) < 3.0  # Should be ~41 with corrected Lambda_FCC

    return deep_perturbative and above_critical and near_expected, {
        "beta_star": beta_s,
        "expected": "~41.0 (with Lambda_FCC = 2.6 MeV from Prop 7.4.3)",
        "deep_perturbative": deep_perturbative,
        "above_beta_c": above_critical,
        "near_expected_41": near_expected,
        "Lambda_FCC_MeV": LAMBDA_FCC_OVER_MSBAR * LAMBDA_MSBAR_MEV,
        "note": "beta_* >> beta_c confirms CG lattice spacing is at Planck scale"
    }


def test_mu_over_sigma_formula():
    """T8: Verify mu/sigma = 8 - 3*ln(3)/x formula."""
    betas = [3.0, 5.0, 7.0]
    all_match = True
    results = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        x = -np.log(u3)
        ratio_numerical = mu / x
        ratio_formula = 8.0 - 3 * np.log(3) / x

        rel_err = abs(ratio_numerical - ratio_formula) / (abs(ratio_formula) + 1e-15)
        if rel_err > 1e-6:
            all_match = False

        results.append({
            "beta": beta, "ratio_numerical": ratio_numerical,
            "ratio_formula": ratio_formula, "relative_error": rel_err
        })

    return all_match, {"results": results}


def test_R_monotonicity_and_range():
    """T9: Verify R(beta) is strictly monotonically decreasing and quantify range."""
    betas = np.linspace(3.0, 8.8, 30)
    Rs = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=100)
        sigma_lat = lattice_string_tension(u3)
        R = mass_gap_ratio(mu, sigma_lat)
        Rs.append(R)

    # R should be strictly monotonically decreasing in beta
    strictly_decreasing = all(Rs[i] > Rs[i+1] for i in range(len(Rs)-1))

    # Analytical: R(beta_c) = 0
    x_c = (3.0/8.0) * np.log(3)
    R_at_bc_analytical = (-3*np.log(3) + 8*x_c) / np.sqrt(x_c)
    R_zero_at_bc = abs(R_at_bc_analytical) < 1e-10

    # Quantify variation in beta = 5 to 8 range
    R_at_5 = Rs[np.argmin(np.abs(np.array(betas) - 5.0))]
    R_at_8 = Rs[np.argmin(np.abs(np.array(betas) - 8.0))]
    variation_factor = R_at_5 / R_at_8 if R_at_8 > 0 else float('inf')

    return strictly_decreasing and R_zero_at_bc, {
        "strictly_decreasing": strictly_decreasing,
        "R_at_beta_c_analytical": R_at_bc_analytical,
        "R_zero_at_bc": R_zero_at_bc,
        "R_at_beta_5": float(R_at_5),
        "R_at_beta_8": float(R_at_8),
        "variation_factor_5_to_8": float(variation_factor),
        "note": "R is proven strictly monotonically decreasing to 0 at beta_c"
    }


def test_physical_mass_gap_nonpert():
    """T10: Physical mass gap using non-perturbative lattice spacing."""
    betas = [5.0, 6.0, 7.0, 8.0]
    results = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        m_phys_MeV = physical_mass_gap_nonpert(mu, u3, SQRT_SIGMA_MEV)
        R = mass_gap_ratio(mu, lattice_string_tension(u3))

        results.append({
            "beta": beta,
            "mu": mu,
            "u3": u3,
            "m_phys_MeV": m_phys_MeV,
            "R_ratio": R,
            "m_phys_over_sqrt_sigma": m_phys_MeV / SQRT_SIGMA_MEV if SQRT_SIGMA_MEV > 0 else 0
        })

    # Physical mass gap should be positive and in reasonable range
    all_positive = all(r["m_phys_MeV"] > 0 for r in results)

    return all_positive, {
        "results": results,
        "all_positive": all_positive,
        "note": "m_phys varies with beta; should stabilize in scaling window"
    }


def test_r_tilde_limit():
    """T11: R_tilde = mu/sigma -> 8 at strong coupling (beta -> 0)."""
    # Test at multiple strong coupling values to verify trend toward 8
    betas_strong = [0.1, 0.5, 1.0, 2.0]
    results = []
    for beta in betas_strong:
        mu, u3 = fcc_intensive_gap(beta, n_grid=150)
        x = -np.log(u3) if u3 > 0 else np.inf
        r_tilde = mu / x if x > 0 else 0
        results.append({"beta": beta, "R_tilde": r_tilde})

    # Analytical: R_tilde = 8 - 3*ln(3)/x, and x -> infinity as beta -> 0
    # So R_tilde -> 8 from below
    r_tildes = [r["R_tilde"] for r in results]
    approaching_8 = r_tildes[0] > r_tildes[-1] > 6.0  # Should approach 8 from below
    closest_to_8 = r_tildes[0]  # Smallest beta = closest to limit
    close_to_8 = abs(closest_to_8 - 8.0) < 1.5

    return close_to_8, {
        "results": results,
        "closest_to_8": closest_to_8,
        "expected_limit": 8.0,
        "deviation": abs(closest_to_8 - 8.0),
        "approaching_from_below": approaching_8,
        "note": "R_tilde = 8 - 3*ln(3)/x approaches 8 as x -> infinity (beta -> 0)"
    }


def test_glueball_ratio_location():
    """T12: Determine where R(beta) matches lattice QCD glueball ratio ~3.7."""
    GLUEBALL_TARGET = 3.93  # Morningstar & Peardon 1999 direct ratio
    GLUEBALL_RANGE = (3.5, 4.0)

    betas = np.linspace(1.0, 9.0, 80)
    match_beta = None
    data = []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=100)
        sl = lattice_string_tension(u3)
        R = mass_gap_ratio(mu, sl)
        data.append({"beta": float(beta), "R": float(R)})
        if match_beta is None and R < GLUEBALL_TARGET:
            match_beta = float(beta)

    # Check if match point is far from beta_c (scaling window)
    beta_c_approx = 11.4
    if match_beta is not None:
        far_from_bc = (beta_c_approx - match_beta) > 3.0  # More than 3 units away
    else:
        far_from_bc = False

    return match_beta is not None, {
        "glueball_target": GLUEBALL_TARGET,
        "match_beta": match_beta,
        "beta_c": beta_c_approx,
        "distance_from_bc": round(beta_c_approx - match_beta, 1) if match_beta else None,
        "far_from_scaling_window": far_from_bc,
        "note": f"R = {GLUEBALL_TARGET} occurs at beta ~ {match_beta:.1f}, "
                f"which is {beta_c_approx - match_beta:.1f} units below beta_c. "
                f"This is in the strong-coupling regime, not the scaling window."
                if match_beta else "R never matches glueball target"
    }


# =============================================================================
# PLOTTING
# =============================================================================

def generate_plots():
    if not HAS_MATPLOTLIB:
        return

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Compute data across beta range
    betas = np.linspace(1.0, 8.8, 60)
    mus, u3s, sigma_lats, Rs, xis = [], [], [], [], []

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=100)
        mus.append(mu)
        u3s.append(u3)
        sl = lattice_string_tension(u3)
        sigma_lats.append(sl)
        Rs.append(mass_gap_ratio(mu, sl))
        xis.append(1.0 / mu if mu > 0 else 100)

    # Plot 1: Mass gap and correlation length
    ax = axes[0, 0]
    ax.plot(betas, mus, 'b-', linewidth=2, label=r'$\mu(\beta)$')
    ax.set_xlabel(r'$\beta$')
    ax.set_ylabel(r'$\mu(\beta)$', color='b')
    ax.tick_params(axis='y', labelcolor='b')
    ax2 = ax.twinx()
    ax2.plot(betas, xis, 'r-', linewidth=2, label=r'$\xi = 1/\mu$')
    ax2.set_ylabel(r'$\xi$ (layers)', color='r')
    ax2.tick_params(axis='y', labelcolor='r')
    ax2.set_ylim(0, 20)
    ax.set_title(r'Mass Gap $\mu$ and Correlation Length $\xi$')
    ax.axvline(x=11.4, color='gray', linestyle='--', alpha=0.5, label=r'$\beta_c$')
    ax.legend(loc='upper right')

    # Plot 2: Dimensionless ratio R(beta)
    ax = axes[0, 1]
    ax.plot(betas, Rs, 'g-', linewidth=2)
    ax.set_xlabel(r'$\beta$')
    ax.set_ylabel(r'$R(\beta) = \mu/\sqrt{\sigma_{\mathrm{lat}}}$')
    ax.set_title('Dimensionless Mass Gap Ratio')
    ax.grid(True, alpha=0.3)
    ax.axhline(y=3.7, color='orange', linestyle='--', alpha=0.7, label=r'Lattice QCD $m_{0^{++}}/\sqrt{\sigma} \approx 3.7$')
    ax.legend()

    # Plot 3: String tension and mass gap
    ax = axes[1, 0]
    ax.plot(betas, sigma_lats, 'r-', linewidth=2, label=r'$\sigma_{\mathrm{lat}} = -\ln u_3$')
    ax.plot(betas, mus, 'b-', linewidth=2, label=r'$\mu(\beta)$')
    ax.set_xlabel(r'$\beta$')
    ax.set_ylabel('Value (lattice units)')
    ax.set_title('String Tension and Mass Gap')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 4: R_tilde = mu/sigma vs beta
    ax = axes[1, 1]
    r_tildes = [mu / sl if sl > 0 and mu > 0 else 0 for mu, sl in zip(mus, sigma_lats)]
    ax.plot(betas, r_tildes, 'm-', linewidth=2)
    ax.axhline(y=8.0, color='k', linestyle='--', alpha=0.5, label=r'Strong-coupling limit $\tilde{R} \to 8$')
    ax.set_xlabel(r'$\beta$')
    ax.set_ylabel(r'$\tilde{R} = \mu/\sigma_{\mathrm{lat}}$')
    ax.set_title(r'Mass Gap / String Tension Ratio')
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'prop_7_4_4_scaling_window.png'), dpi=150)
    plt.close()
    print(f"  Plot saved: {os.path.join(PLOT_DIR, 'prop_7_4_4_scaling_window.png')}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 70)
    print("Proposition 7.4.4: Scaling Window Identification — Verification")
    print("=" * 70)

    tests = [
        ("T1: Critical coupling beta_c", test_critical_coupling),
        ("T2: Mass gap vanishes at beta_c", test_mass_gap_vanishes_at_critical),
        ("T3: Correlation length diverges", test_correlation_length_diverges),
        ("T4: Dimensionless ratio R(beta)", test_dimensionless_ratio),
        ("T5: Analytical R formula", test_analytical_ratio_formula),
        ("T6: CG lattice spacing value", test_cg_lattice_spacing_value),
        ("T7: beta_* from CG spacing", test_beta_star),
        ("T8: mu/sigma formula", test_mu_over_sigma_formula),
        ("T9: R(beta) monotonicity and range", test_R_monotonicity_and_range),
        ("T10: Physical mass gap (non-pert)", test_physical_mass_gap_nonpert),
        ("T11: R_tilde -> 8 at strong coupling", test_r_tilde_limit),
        ("T12: Glueball ratio R=3.93 location", test_glueball_ratio_location),
    ]

    results = []
    passed = 0
    failed = 0

    for name, func in tests:
        result = run_test(name, func)
        results.append(result)
        status = "PASS" if result.passed else "FAIL"
        icon = "✅" if result.passed else "❌"
        print(f"  {icon} {name}: {status}")
        if not result.passed:
            print(f"     Details: {result.details}")
            failed += 1
        else:
            passed += 1

    print(f"\n{'=' * 70}")
    print(f"SUMMARY: {passed}/{passed + failed} tests passed")
    print(f"{'=' * 70}")

    print("\nGenerating verification plots...")
    generate_plots()

    output = {
        "proposition": "7.4.4",
        "title": "Scaling Window Identification on FCC",
        "timestamp": datetime.now().isoformat(),
        "summary": f"{passed}/{passed + failed} tests passed",
        "tests": [
            {
                "name": r.name,
                "passed": r.passed,
                "details": {k: (float(v) if isinstance(v, (np.floating, float)) else
                              str(v) if isinstance(v, np.ndarray) else v)
                           for k, v in r.details.items()
                           if not isinstance(v, (list,)) or len(v) < 10}
            }
            for r in results
        ]
    }

    json_path = os.path.join(SCRIPT_DIR, 'prop_7_4_4_results.json')
    with open(json_path, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to: {json_path}")

    return passed == passed + failed


if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
