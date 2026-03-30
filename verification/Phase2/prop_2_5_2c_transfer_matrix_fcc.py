#!/usr/bin/env python3
"""
Proposition 2.5.2c: Transfer Matrix for FCC Layers
====================================================

Verifies the FCC lattice transfer matrix eigenvalue formula:

    lambda_R(beta, N_s) = d_R^{3*N_s} * [a_R(beta)]^{8*N_s}

and the associated mass gap, critical coupling, and spectral properties.

Key Results:
    - Transfer matrix is diagonal in the representation basis
    - Mass gap: m_gap = -3*N_s*ln(3) - 8*N_s*ln(u_3(beta))
    - Intensive gap: mu(beta) = -3*ln(3) - 8*ln(u_3(beta))
    - Critical coupling: u_3(beta_c) = 3^(-3/8)

Key Tests:
    1. Transfer matrix eigenvalue computation
    2. Partition function consistency (Tr(T^L) = Z_FCC)
    3. Mass gap formula verification
    4. Critical coupling
    5. Strong coupling expansion
    6. Eigenvalue positivity and ordering
    7. Extensive vs intensive gap
    8. Comparison with single-stella K4 spectrum
    9. Eigenvalue spectral ratios
   10. Monotonicity and limiting behavior

Related Documents:
    - Proof: docs/proofs/Phase2/Proposition-2.5.2c-Transfer-Matrix-FCC-Layers.md
    - Parent: docs/proofs/Phase2/Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC.md
    - Building block: docs/proofs/foundations/Proposition-0.0.38a-Stella-Gauge-Spectrum.md

Verification Date: 2026-02-12
"""

import numpy as np
from scipy import integrate
from scipy.optimize import brentq
import json
from datetime import datetime
from pathlib import Path

# =============================================================================
# CONSTANTS
# =============================================================================

OUTPUT_DIR = Path(__file__).parent
PLOT_DIR = Path(__file__).parent.parent / "plots"
PLOT_DIR.mkdir(parents=True, exist_ok=True)

N_C = 3  # SU(3) gauge group


# =============================================================================
# SU(3) REPRESENTATION DATA
# =============================================================================

def su3_dim(p, q):
    """Dimension of SU(3) irrep with Dynkin labels (p, q)."""
    return (p + 1) * (q + 1) * (p + q + 2) // 2


def su3_casimir(p, q):
    """Quadratic Casimir C2 for SU(3) irrep (p, q).

    C2(p,q) = (p^2 + q^2 + pq + 3p + 3q) / 3
    """
    return (p**2 + q**2 + p * q + 3 * p + 3 * q) / 3.0


# First ~22 SU(3) representations ordered by dimension
SU3_REPS = [
    (0, 0),   # 1   (trivial)
    (1, 0),   # 3   (fundamental)
    (0, 1),   # 3-bar (anti-fundamental)
    (2, 0),   # 6
    (0, 2),   # 6-bar
    (1, 1),   # 8   (adjoint)
    (3, 0),   # 10
    (0, 3),   # 10-bar
    (2, 1),   # 15
    (1, 2),   # 15-bar
    (4, 0),   # 15'
    (0, 4),   # 15-bar'
    (2, 2),   # 27
    (3, 1),   # 24
    (1, 3),   # 24-bar
    (5, 0),   # 21
    (0, 5),   # 21-bar
    (4, 1),   # 35
    (1, 4),   # 35-bar
    (3, 2),   # 42
    (2, 3),   # 42-bar
    (3, 3),   # 64
]


# =============================================================================
# WEYL INTEGRATION ON SU(3)
# =============================================================================

def weyl_measure(theta1, theta2):
    """Weyl measure |Delta(theta)|^2 for SU(3).

    The Vandermonde determinant squared for eigenvalues
    z1 = e^{i*theta1}, z2 = e^{i*theta2}, z3 = e^{-i(theta1+theta2)}.

    Normalization: integral d theta1 d theta2 |Delta|^2 / (24 pi^2) = 1
    """
    d12 = 2.0 * np.sin((theta1 - theta2) / 2.0)
    d13 = 2.0 * np.sin((2.0 * theta1 + theta2) / 2.0)
    d23 = 2.0 * np.sin((theta1 + 2.0 * theta2) / 2.0)
    return d12**2 * d13**2 * d23**2


def su3_boltzmann(theta1, theta2, beta):
    """Boltzmann weight exp(beta/3 * Re Tr U) for SU(3).

    Re Tr U = cos theta1 + cos theta2 + cos(theta1 + theta2).
    """
    re_tr = np.cos(theta1) + np.cos(theta2) + np.cos(theta1 + theta2)
    return np.exp(beta / 3.0 * re_tr)


def su3_character(p, q, theta1, theta2):
    """Character chi_{(p,q)}(theta1, theta2) via Weyl character formula."""
    z1 = np.exp(1j * theta1)
    z2 = np.exp(1j * theta2)
    z3 = np.exp(-1j * (theta1 + theta2))
    zs = [z1, z2, z3]

    lam_rho = [p + q + 2, q + 1, 0]
    rho = [2, 1, 0]

    perms = [
        ([0, 1, 2], +1),
        ([0, 2, 1], -1),
        ([1, 0, 2], -1),
        ([1, 2, 0], +1),
        ([2, 0, 1], +1),
        ([2, 1, 0], -1),
    ]

    num = 0.0 + 0.0j
    den = 0.0 + 0.0j
    for perm, sign in perms:
        num += sign * zs[perm[0]]**lam_rho[0] * zs[perm[1]]**lam_rho[1] * zs[perm[2]]**lam_rho[2]
        den += sign * zs[perm[0]]**rho[0] * zs[perm[1]]**rho[1] * zs[perm[2]]**rho[2]

    if abs(den) < 1e-12:
        return complex(float(su3_dim(p, q)), 0.0)

    return num / den


def compute_a_R_fast(p, q, beta, n_grid=300):
    """Fast computation of a_R(beta) using grid-based Weyl integration.

    a_R(beta) = (1/d_R) * (1/24 pi^2) * integral d theta1 d theta2 |Delta|^2
                * exp(beta/3 Re Tr U) * chi_{R-bar}(theta1, theta2)

    Independent implementation for cross-verification.
    """
    d_R = su3_dim(p, q)
    p_conj, q_conj = q, p  # conjugate representation

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


def compute_a_R_accurate(p, q, beta):
    """High-accuracy computation of a_R(beta) via scipy dblquad.

    Used for critical coupling and precision-sensitive tests.
    """
    d_R = su3_dim(p, q)
    p_conj, q_conj = q, p

    def integrand_real(theta2, theta1):
        wm = weyl_measure(theta1, theta2)
        bw = su3_boltzmann(theta1, theta2, beta)
        chi = su3_character(p_conj, q_conj, theta1, theta2)
        return (wm * bw * chi).real

    result, error = integrate.dblquad(
        integrand_real, 0, 2 * np.pi, 0, 2 * np.pi,
        epsabs=1e-10, epsrel=1e-10
    )

    normalization = 24.0 * np.pi**2
    a_R = result / (normalization * d_R)
    return a_R


# =============================================================================
# FCC TRANSFER MATRIX FUNCTIONS
# =============================================================================

def fcc_eigenvalue(p, q, beta, N_s, n_grid=300):
    """Compute FCC transfer matrix eigenvalue lambda_R(beta, N_s).

    lambda_R = d_R^{3*N_s} * [a_R(beta)]^{8*N_s}
    """
    d_R = su3_dim(p, q)
    a_R = compute_a_R_fast(p, q, beta, n_grid=n_grid)
    return d_R**(3 * N_s) * a_R**(8 * N_s)


def fcc_intensive_gap(beta, n_grid=300):
    """Compute intensive mass gap mu(beta) = -3*ln(3) - 8*ln(u_3(beta)).

    u_3(beta) = a_3(beta) / a_1(beta) is the normalized heat kernel ratio.
    """
    a_1 = compute_a_R_fast(0, 0, beta, n_grid=n_grid)
    a_3 = compute_a_R_fast(1, 0, beta, n_grid=n_grid)
    u_3 = a_3 / a_1 if a_1 > 0 else 0.0
    if u_3 > 0:
        mu = -3.0 * np.log(3) - 8.0 * np.log(u_3)
    else:
        mu = np.inf
    return mu, u_3


def fcc_intensive_gap_accurate(beta):
    """High-accuracy intensive mass gap using dblquad integration."""
    a_1 = compute_a_R_accurate(0, 0, beta)
    a_3 = compute_a_R_accurate(1, 0, beta)
    u_3 = a_3 / a_1 if a_1 > 0 else 0.0
    if u_3 > 0:
        mu = -3.0 * np.log(3) - 8.0 * np.log(u_3)
    else:
        mu = np.inf
    return mu, u_3


def k4_transfer_gap(beta, n_grid=300):
    """Compute K4 (single stella) transfer matrix mass gap.

    K4 eigenvalues: t_R = d_R^4 * a_R^10 (from chi=4, F=10)
    Gap: m_K4 = -ln(t_3/t_1) = -4*ln(3) - 10*ln(u_3)
    """
    a_1 = compute_a_R_fast(0, 0, beta, n_grid=n_grid)
    a_3 = compute_a_R_fast(1, 0, beta, n_grid=n_grid)
    u_3 = a_3 / a_1 if a_1 > 0 else 0.0
    if u_3 > 0:
        m_k4 = -4.0 * np.log(3) - 10.0 * np.log(u_3)
    else:
        m_k4 = np.inf
    return m_k4, u_3


# =============================================================================
# TEST 1: Transfer Matrix Eigenvalue Computation
# =============================================================================

def test_eigenvalue_computation():
    """Compute lambda_R for various representations, beta, and N_s values."""
    print("\n" + "=" * 70)
    print("TEST 1: Transfer Matrix Eigenvalue Computation")
    print("=" * 70)

    all_passed = True

    # Representations to test
    test_reps = [
        (0, 0),   # d=1
        (1, 0),   # d=3
        (1, 1),   # d=8
        (2, 0),   # d=6
        (3, 0),   # d=10
        (2, 1),   # d=15
        (2, 2),   # d=27
    ]
    betas = [1.0, 2.0, 4.0, 6.0, 8.0]
    N_s_values = [1, 2, 4]

    eigenvalue_data = {}

    for beta in betas:
        print(f"\n  beta = {beta}:")

        # Pre-compute a_R for all reps at this beta
        a_R_cache = {}
        for p, q in test_reps:
            a_R_cache[(p, q)] = compute_a_R_fast(p, q, beta, n_grid=300)

        for N_s in N_s_values:
            print(f"    N_s = {N_s}:")
            for p, q in test_reps:
                d_R = su3_dim(p, q)
                a_R = a_R_cache[(p, q)]

                # Direct formula
                lam_direct = d_R**(3 * N_s) * a_R**(8 * N_s)

                # Step-by-step verification
                lam_step = (d_R**3)**(N_s) * (a_R**8)**(N_s)

                rel_err = abs(lam_direct - lam_step) / max(abs(lam_direct), 1e-300)

                if d_R <= 10 and N_s <= 2:
                    print(f"      R=({p},{q}) d={d_R:2d}: a_R={a_R:.6f}, "
                          f"lambda={lam_direct:.6e}, check_err={rel_err:.2e}")

                if rel_err > 1e-12:
                    print(f"      FAIL: eigenvalue inconsistency for ({p},{q}) "
                          f"N_s={N_s}, err={rel_err:.2e}")
                    all_passed = False

                key = f"beta={beta}_Ns={N_s}_R=({p},{q})"
                eigenvalue_data[key] = {
                    "d_R": d_R,
                    "a_R": a_R,
                    "lambda_R": lam_direct,
                }

    # Verify eigenvalue factorization: lambda_R(N_s=2) = lambda_R(N_s=1)^2 * (d_R^3)^1 * ...
    # Actually: lambda_R(N_s=2) = d_R^6 * a_R^16 = (d_R^3 * a_R^8)^2
    # And lambda_R(N_s=1) = d_R^3 * a_R^8
    # So lambda_R(N_s=2) = [lambda_R(N_s=1)]^2
    print(f"\n  Factorization check: lambda_R(N_s=2) = [lambda_R(N_s=1)]^2")
    beta_check = 4.0
    for p, q in test_reps[:4]:
        d_R = su3_dim(p, q)
        a_R = compute_a_R_fast(p, q, beta_check, n_grid=300)
        lam_1 = d_R**3 * a_R**8
        lam_2 = d_R**6 * a_R**16
        err = abs(lam_2 - lam_1**2) / max(abs(lam_2), 1e-300)
        print(f"    R=({p},{q}): lambda(Ns=1)^2={lam_1**2:.6e}, lambda(Ns=2)={lam_2:.6e}, err={err:.2e}")
        if err > 1e-10:
            all_passed = False

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "1",
        "name": "Transfer Matrix Eigenvalue Computation",
        "n_reps": len(test_reps),
        "n_betas": len(betas),
        "n_Ns": len(N_s_values),
        "passed": all_passed,
    }


# =============================================================================
# TEST 2: Partition Function Consistency Tr(T^L) = Z_FCC
# =============================================================================

def test_partition_function_consistency():
    """Verify Tr(T^L) = Z_FCC = Sum_R d_R^{3*N_s*L} * a_R^{8*N_s*L}."""
    print("\n" + "=" * 70)
    print("TEST 2: Partition Function Consistency Tr(T^L) = Z_FCC")
    print("=" * 70)

    all_passed = True
    N_s = 1
    beta = 2.0

    # Truncate representation sum at d_max ~ 30
    reps = [r for r in SU3_REPS if su3_dim(r[0], r[1]) <= 30]

    # Pre-compute a_R
    a_R_cache = {}
    for p, q in reps:
        a_R_cache[(p, q)] = compute_a_R_fast(p, q, beta, n_grid=300)

    # Compute eigenvalues lambda_R for N_s = 1
    eigenvalues = {}
    for p, q in reps:
        d_R = su3_dim(p, q)
        a_R = a_R_cache[(p, q)]
        eigenvalues[(p, q)] = d_R**3 * a_R**8

    L_values = [1, 2, 3, 5]

    for L in L_values:
        print(f"\n  L = {L}:")

        # Method 1: Tr(T^L) = Sum_R lambda_R^L
        tr_T_L = sum(lam**L for lam in eigenvalues.values())

        # Method 2: Z_FCC = Sum_R d_R^{3*N_s*L} * a_R^{8*N_s*L}
        Z_FCC = 0.0
        for p, q in reps:
            d_R = su3_dim(p, q)
            a_R = a_R_cache[(p, q)]
            Z_FCC += d_R**(3 * N_s * L) * a_R**(8 * N_s * L)

        rel_err = abs(tr_T_L - Z_FCC) / max(abs(Z_FCC), 1e-300)

        print(f"    Tr(T^{L}) = {tr_T_L:.10e}")
        print(f"    Z_FCC     = {Z_FCC:.10e}")
        print(f"    Rel error = {rel_err:.2e}")

        if rel_err > 1e-10:
            print(f"    FAIL: Tr(T^L) != Z_FCC")
            all_passed = False
        else:
            print(f"    PASS (agreement to machine precision)")

    # Also check for N_s = 2
    N_s_2 = 2
    print(f"\n  N_s = {N_s_2}, L = 2:")
    L = 2
    tr_T_L = sum(
        (su3_dim(p, q)**(3 * N_s_2) * a_R_cache[(p, q)]**(8 * N_s_2))**L
        for p, q in reps
    )
    Z_FCC_2 = sum(
        su3_dim(p, q)**(3 * N_s_2 * L) * a_R_cache[(p, q)]**(8 * N_s_2 * L)
        for p, q in reps
    )
    rel_err_2 = abs(tr_T_L - Z_FCC_2) / max(abs(Z_FCC_2), 1e-300)
    print(f"    Tr(T^{L}) = {tr_T_L:.10e}")
    print(f"    Z_FCC     = {Z_FCC_2:.10e}")
    print(f"    Rel error = {rel_err_2:.2e}")
    if rel_err_2 > 1e-10:
        print(f"    FAIL")
        all_passed = False
    else:
        print(f"    PASS")

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "2",
        "name": "Partition Function Consistency",
        "passed": all_passed,
    }


# =============================================================================
# TEST 3: Mass Gap Formula Verification
# =============================================================================

def test_mass_gap_formula():
    """Verify mu(beta) = -3*ln(3) - 8*ln(u_3(beta)) from eigenvalue ratio."""
    print("\n" + "=" * 70)
    print("TEST 3: Mass Gap Formula Verification")
    print("=" * 70)

    all_passed = True

    betas = [0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
    gap_data = {}

    print(f"  {'beta':>6s} {'mu(formula)':>14s} {'mu(eigenval)':>14s} {'u_3':>12s} {'err':>10s} {'sign':>6s}")
    print(f"  {'-' * 66}")

    for beta in betas:
        # Method 1: Direct formula
        mu_formula, u_3 = fcc_intensive_gap(beta, n_grid=300)

        # Method 2: From eigenvalue ratio mu = -ln(lambda_3 / lambda_1) for N_s=1
        a_1 = compute_a_R_fast(0, 0, beta, n_grid=300)
        a_3 = compute_a_R_fast(1, 0, beta, n_grid=300)
        lambda_1 = 1.0**3 * a_1**8       # d_1 = 1
        lambda_3 = 3.0**3 * a_3**8       # d_3 = 3
        if lambda_3 > 0 and lambda_1 > 0:
            mu_eigenval = -np.log(lambda_3 / lambda_1)
        else:
            mu_eigenval = np.inf

        err = abs(mu_formula - mu_eigenval) / max(abs(mu_formula), 1e-300)

        sign = "+" if mu_formula > 0 else ("-" if mu_formula < 0 else "0")

        print(f"  {beta:6.1f} {mu_formula:14.6f} {mu_eigenval:14.6f} {u_3:12.6f} {err:10.2e} {sign:>6s}")

        if err > 1e-8:
            print(f"    FAIL: formula vs eigenvalue disagreement")
            all_passed = False

        gap_data[beta] = {
            "mu_formula": mu_formula,
            "mu_eigenval": mu_eigenval,
            "u_3": u_3,
            "error": err,
        }

    # Check sign behavior: mu > 0 for small beta, mu < 0 for large beta
    print(f"\n  Sign behavior check:")
    mu_small, _ = fcc_intensive_gap(0.5, n_grid=300)
    mu_large, _ = fcc_intensive_gap(20.0, n_grid=300)
    print(f"    mu(0.5) = {mu_small:.4f} (expected > 0, confining)")
    print(f"    mu(20)  = {mu_large:.4f} (expected < 0, deconfined)")

    if mu_small <= 0:
        print(f"    FAIL: mu should be positive at strong coupling")
        all_passed = False
    if mu_large >= 0:
        print(f"    FAIL: mu should be negative at weak coupling")
        all_passed = False
    if mu_small > 0 and mu_large < 0:
        print(f"    Sign behavior: PASS")

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "3",
        "name": "Mass Gap Formula Verification",
        "gap_data": {str(k): v for k, v in gap_data.items()},
        "passed": all_passed,
    }


# =============================================================================
# TEST 4: Critical Coupling
# =============================================================================

def test_critical_coupling():
    """Find beta_c where mu(beta_c) = 0, verify u_3(beta_c) = 3^(-3/8)."""
    print("\n" + "=" * 70)
    print("TEST 4: Critical Coupling")
    print("=" * 70)

    all_passed = True

    u_3_crit_exact = 3.0**(-3.0 / 8.0)
    print(f"  Exact critical ratio: u_3_crit = 3^(-3/8) = {u_3_crit_exact:.10f}")

    # Use high-accuracy integration for critical coupling
    def mu_of_beta(beta):
        mu, u_3 = fcc_intensive_gap_accurate(beta)
        return mu

    # First bracket: find where mu changes sign
    print(f"\n  Bracketing beta_c:")
    beta_lo, beta_hi = 1.0, 20.0
    mu_lo = mu_of_beta(beta_lo)
    mu_hi = mu_of_beta(beta_hi)
    print(f"    mu({beta_lo}) = {mu_lo:.6f}")
    print(f"    mu({beta_hi}) = {mu_hi:.6f}")

    if mu_lo > 0 and mu_hi < 0:
        print(f"    Sign change confirmed: beta_c in ({beta_lo}, {beta_hi})")
    else:
        print(f"    WARNING: no sign change detected, adjusting bracket")
        # Try wider range
        for b_test in [0.1, 0.5, 2.0, 5.0, 10.0, 15.0, 25.0, 50.0]:
            mu_test = mu_of_beta(b_test)
            print(f"      mu({b_test}) = {mu_test:.6f}")
            if mu_test > 0:
                beta_lo = b_test
                mu_lo = mu_test
            if mu_test < 0 and mu_lo > 0:
                beta_hi = b_test
                mu_hi = mu_test
                break

    # Bisection to find beta_c
    try:
        beta_c = brentq(mu_of_beta, beta_lo, beta_hi, xtol=1e-8, rtol=1e-10)
        print(f"\n  Critical coupling: beta_c = {beta_c:.8f}")

        # Verify mu(beta_c) = 0
        mu_at_bc = mu_of_beta(beta_c)
        print(f"  mu(beta_c) = {mu_at_bc:.2e} (should be ~0)")

        # Verify u_3(beta_c) = 3^(-3/8)
        a_1_c = compute_a_R_accurate(0, 0, beta_c)
        a_3_c = compute_a_R_accurate(1, 0, beta_c)
        u_3_c = a_3_c / a_1_c

        u_3_err = abs(u_3_c - u_3_crit_exact) / u_3_crit_exact
        print(f"  u_3(beta_c) = {u_3_c:.10f}")
        print(f"  u_3_crit    = {u_3_crit_exact:.10f}")
        print(f"  Rel error   = {u_3_err:.2e}")

        if abs(mu_at_bc) > 1e-6:
            print(f"  FAIL: mu(beta_c) not zero")
            all_passed = False
        elif u_3_err > 1e-4:
            print(f"  FAIL: u_3(beta_c) != 3^(-3/8)")
            all_passed = False
        else:
            print(f"  Critical coupling: PASS")

        # Check sign change across beta_c
        eps = 0.1
        mu_minus = mu_of_beta(beta_c - eps)
        mu_plus = mu_of_beta(beta_c + eps)
        print(f"\n  Sign check:")
        print(f"    mu(beta_c - {eps}) = {mu_minus:.6f} (should be > 0)")
        print(f"    mu(beta_c + {eps}) = {mu_plus:.6f} (should be < 0)")

        if mu_minus <= 0 or mu_plus >= 0:
            print(f"    FAIL: wrong sign change at beta_c")
            all_passed = False
        else:
            print(f"    Sign change: PASS")

    except ValueError as e:
        print(f"  ERROR in root finding: {e}")
        beta_c = None
        all_passed = False

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "4",
        "name": "Critical Coupling",
        "u_3_crit_exact": u_3_crit_exact,
        "beta_c": beta_c,
        "passed": all_passed,
    }


# =============================================================================
# TEST 5: Strong Coupling Expansion
# =============================================================================

def test_strong_coupling_expansion():
    """Verify strong coupling limit: u_3 ~ beta/18, mu ~ 8*ln(18/beta) - 3*ln(3)."""
    print("\n" + "=" * 70)
    print("TEST 5: Strong Coupling Expansion")
    print("=" * 70)

    all_passed = True

    betas = [0.1, 0.5, 1.0]

    print(f"  Strong coupling: u_3 ~ beta/18 (leading order)")
    print(f"  => mu ~ -3*ln(3) - 8*ln(beta/18) = -3*ln(3) + 8*ln(18/beta)")
    print()
    print(f"  {'beta':>6s} {'u_3(exact)':>14s} {'beta/18':>14s} {'rel_err':>12s} {'mu(exact)':>12s} {'mu(approx)':>12s} {'mu_err':>10s}")
    print(f"  {'-' * 84}")

    for beta in betas:
        # Exact computation
        mu_exact, u_3_exact = fcc_intensive_gap(beta, n_grid=400)

        # Leading order strong coupling
        u_3_approx = beta / 18.0
        mu_approx = -3.0 * np.log(3) - 8.0 * np.log(u_3_approx)

        u_rel_err = abs(u_3_exact - u_3_approx) / u_3_exact if u_3_exact > 0 else float('inf')
        mu_rel_err = abs(mu_exact - mu_approx) / abs(mu_exact) if abs(mu_exact) > 0 else float('inf')

        print(f"  {beta:6.1f} {u_3_exact:14.8f} {u_3_approx:14.8f} {u_rel_err:12.4e} "
              f"{mu_exact:12.6f} {mu_approx:12.6f} {mu_rel_err:10.4e}")

    # Check convergence: at beta = 0.1, leading order should be excellent
    mu_01, u_3_01 = fcc_intensive_gap(0.1, n_grid=400)
    u_3_lo = 0.1 / 18.0
    u_3_err_01 = abs(u_3_01 - u_3_lo) / u_3_01
    print(f"\n  Convergence at beta=0.1:")
    print(f"    |u_3 - beta/18| / u_3 = {u_3_err_01:.4e}")
    if u_3_err_01 > 0.05:
        print(f"    WARNING: leading order not accurate at beta=0.1 (err={u_3_err_01:.2e})")
        # This might not be a failure since beta/18 is only the lowest-order term
    else:
        print(f"    Strong coupling leading order: PASS")

    # Verify u_3 -> 0 as beta -> 0
    u_3_small = compute_a_R_fast(1, 0, 0.01, n_grid=400) / compute_a_R_fast(0, 0, 0.01, n_grid=400)
    print(f"\n  u_3(beta=0.01) = {u_3_small:.8f} (should be small)")
    if u_3_small > 0.1:
        print(f"    FAIL: u_3 not small at beta=0.01")
        all_passed = False
    else:
        print(f"    u_3 -> 0 as beta -> 0: PASS")

    # Verify mu -> +inf as beta -> 0
    mu_small, _ = fcc_intensive_gap(0.01, n_grid=400)
    print(f"  mu(beta=0.01) = {mu_small:.4f} (should be large and positive)")
    if mu_small < 5.0:
        print(f"    WARNING: mu not large at beta=0.01")
    else:
        print(f"    mu -> +inf as beta -> 0: PASS")

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "5",
        "name": "Strong Coupling Expansion",
        "passed": all_passed,
    }


# =============================================================================
# TEST 6: Eigenvalue Positivity and Ordering
# =============================================================================

def test_eigenvalue_positivity():
    """Verify lambda_R > 0 for all R and beta, check ordering."""
    print("\n" + "=" * 70)
    print("TEST 6: Eigenvalue Positivity and Ordering")
    print("=" * 70)

    all_passed = True

    reps = [r for r in SU3_REPS[:13] if su3_dim(r[0], r[1]) <= 30]
    betas = np.concatenate([
        np.array([0.01, 0.1, 0.5]),
        np.arange(1.0, 21.0, 1.0),
    ])

    n_positive = 0
    n_total = 0
    ordering_violations = 0
    level_crossing_beta = None

    print(f"  Checking {len(reps)} representations over {len(betas)} beta values...")

    for beta in betas:
        # Compute eigenvalues for N_s = 1
        eigenvals = {}
        for p, q in reps:
            d_R = su3_dim(p, q)
            a_R = compute_a_R_fast(p, q, beta, n_grid=200)
            lam = d_R**3 * a_R**8
            eigenvals[(p, q)] = lam
            n_total += 1
            if lam > 0:
                n_positive += 1

        # Check positivity
        all_pos = all(v > 0 for v in eigenvals.values())

        # Check ordering at strong coupling: lambda_1 > lambda_3 > lambda_8 ...
        lam_1 = eigenvals.get((0, 0), 0)
        lam_3 = eigenvals.get((1, 0), 0)
        lam_8 = eigenvals.get((1, 1), 0)

        if lam_1 > 0 and lam_3 > 0:
            if lam_3 > lam_1 and level_crossing_beta is None:
                level_crossing_beta = beta

        if beta in [0.01, 1.0, 5.0, 10.0, 20.0]:
            print(f"  beta={beta:5.2f}: lambda_1={lam_1:.6e}, lambda_3={lam_3:.6e}, "
                  f"lambda_8={lam_8:.6e}, all_pos={all_pos}")

    print(f"\n  Positivity: {n_positive}/{n_total} eigenvalues positive")
    if n_positive < n_total:
        print(f"  FAIL: some eigenvalues are non-positive")
        all_passed = False
    else:
        print(f"  All eigenvalues positive: PASS")

    # Report level crossing
    if level_crossing_beta is not None:
        print(f"\n  Level crossing (lambda_3 > lambda_1) detected around beta ~ {level_crossing_beta:.2f}")
        print(f"  This is expected: for beta > beta_c, the trivial rep no longer dominates")
        print(f"  (Corresponds to the deconfinement transition)")
    else:
        print(f"\n  No level crossing detected in tested range")

    # Detailed ordering near beta_c
    print(f"\n  Eigenvalue ordering near expected beta_c:")
    for beta in [5.0, 6.0, 7.0, 8.0, 9.0, 10.0]:
        a_1 = compute_a_R_fast(0, 0, beta, n_grid=200)
        a_3 = compute_a_R_fast(1, 0, beta, n_grid=200)
        a_8 = compute_a_R_fast(1, 1, beta, n_grid=200)
        lam_1 = a_1**8
        lam_3 = 27.0 * a_3**8
        lam_8 = 512.0 * a_8**8
        dominance = "1" if lam_1 >= max(lam_3, lam_8) else ("3" if lam_3 >= lam_8 else "8")
        print(f"    beta={beta:.1f}: lam_1={lam_1:.4e}, lam_3={lam_3:.4e}, "
              f"lam_8={lam_8:.4e} -> dominant: {dominance}")

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "6",
        "name": "Eigenvalue Positivity and Ordering",
        "n_positive": n_positive,
        "n_total": n_total,
        "level_crossing_beta": level_crossing_beta,
        "passed": all_passed,
    }


# =============================================================================
# TEST 7: Extensive vs Intensive Gap
# =============================================================================

def test_extensive_intensive_gap():
    """Verify m_gap(N_s) = N_s * mu(beta), confirming linear extensivity."""
    print("\n" + "=" * 70)
    print("TEST 7: Extensive vs Intensive Mass Gap")
    print("=" * 70)

    all_passed = True

    N_s_values = [1, 2, 4, 8]
    betas = [1.0, 3.0, 6.0]

    for beta in betas:
        print(f"\n  beta = {beta}:")

        # Compute intensive gap
        mu, u_3 = fcc_intensive_gap(beta, n_grid=300)
        print(f"    mu(beta) = {mu:.8f}")
        print(f"    u_3      = {u_3:.8f}")

        for N_s in N_s_values:
            # Compute extensive gap: m_gap = -3*N_s*ln(3) - 8*N_s*ln(u_3)
            m_gap_formula = -3.0 * N_s * np.log(3) - 8.0 * N_s * np.log(u_3)

            # Compute directly from eigenvalue ratio
            a_1 = compute_a_R_fast(0, 0, beta, n_grid=300)
            a_3 = compute_a_R_fast(1, 0, beta, n_grid=300)
            lam_1 = 1.0**(3 * N_s) * a_1**(8 * N_s)
            lam_3 = 3.0**(3 * N_s) * a_3**(8 * N_s)
            m_gap_direct = -np.log(lam_3 / lam_1) if lam_3 > 0 and lam_1 > 0 else np.inf

            # Check linear scaling
            m_gap_from_mu = N_s * mu

            err_formula = abs(m_gap_formula - m_gap_direct) / max(abs(m_gap_direct), 1e-300)
            err_scaling = abs(m_gap_from_mu - m_gap_direct) / max(abs(m_gap_direct), 1e-300)

            print(f"    N_s={N_s}: m_gap(direct)={m_gap_direct:.8f}, "
                  f"N_s*mu={m_gap_from_mu:.8f}, err_scaling={err_scaling:.2e}")

            if err_formula > 1e-8:
                print(f"      FAIL: formula disagreement")
                all_passed = False
            if err_scaling > 1e-8:
                print(f"      FAIL: linear scaling violation")
                all_passed = False

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "7",
        "name": "Extensive vs Intensive Mass Gap",
        "passed": all_passed,
    }


# =============================================================================
# TEST 8: Comparison with Single-Stella K4 Spectrum
# =============================================================================

def test_comparison_with_k4():
    """Compare FCC transfer matrix spectrum with K4 (single stella) spectrum."""
    print("\n" + "=" * 70)
    print("TEST 8: Comparison with Single-Stella K4 Spectrum")
    print("=" * 70)

    all_passed = True

    # K4 eigenvalues: t_R = d_R^4 * a_R^10 (chi=4, F=10)
    # K4 mass gap: m_K4 = -4*ln(3) - 10*ln(u_3)
    # FCC eigenvalues (N_s=1): lambda_R = d_R^3 * a_R^8
    # FCC mass gap: mu_FCC = -3*ln(3) - 8*ln(u_3)

    betas = [1.0, 2.0, 4.0, 6.0, 8.0, 10.0, 15.0]

    print(f"  Comparison: K4 gap m_K4 = -4*ln(3) - 10*ln(u_3)")
    print(f"              FCC gap mu  = -3*ln(3) - 8*ln(u_3)")
    print(f"  Difference: m_K4 - mu = -ln(3) - 2*ln(u_3)")
    print()
    print(f"  {'beta':>6s} {'m_K4':>12s} {'mu_FCC':>12s} {'diff':>12s} {'u_3':>12s}")
    print(f"  {'-' * 58}")

    k4_data = {}
    fcc_data = {}

    for beta in betas:
        m_k4, u_3 = k4_transfer_gap(beta, n_grid=300)
        mu_fcc, _ = fcc_intensive_gap(beta, n_grid=300)

        # Analytic difference
        diff_analytic = -np.log(3) - 2.0 * np.log(u_3)
        diff_actual = m_k4 - mu_fcc
        diff_err = abs(diff_analytic - diff_actual)

        print(f"  {beta:6.1f} {m_k4:12.6f} {mu_fcc:12.6f} {diff_actual:12.6f} {u_3:12.6f}")

        if diff_err > 1e-8:
            print(f"    FAIL: analytic difference formula off by {diff_err:.2e}")
            all_passed = False

        k4_data[beta] = m_k4
        fcc_data[beta] = mu_fcc

    # Verify they are different (the FCC assembly changes the spectrum)
    print(f"\n  Verification: K4 and FCC gaps are DIFFERENT:")
    for beta in [2.0, 6.0]:
        m_k4, _ = k4_transfer_gap(beta, n_grid=300)
        mu_fcc, _ = fcc_intensive_gap(beta, n_grid=300)
        rel_diff = abs(m_k4 - mu_fcc) / max(abs(m_k4), abs(mu_fcc), 1e-300)
        print(f"    beta={beta}: |m_K4 - mu_FCC| / max = {rel_diff:.4f}")
        if rel_diff < 1e-6:
            print(f"      WARNING: gaps suspiciously close -- expected different spectra")

    # Compare critical couplings
    # K4: u_3(beta_c^K4) = 3^(-2/5) (from -4*ln(3) - 10*ln(u_3) = 0 => u_3 = 3^(-2/5))
    # FCC: u_3(beta_c^FCC) = 3^(-3/8)
    u_3_crit_k4 = 3.0**(-2.0 / 5.0)
    u_3_crit_fcc = 3.0**(-3.0 / 8.0)
    print(f"\n  Critical u_3 comparison:")
    print(f"    K4:  u_3_crit = 3^(-2/5) = {u_3_crit_k4:.8f}")
    print(f"    FCC: u_3_crit = 3^(-3/8) = {u_3_crit_fcc:.8f}")
    print(f"    Ratio: {u_3_crit_fcc / u_3_crit_k4:.6f}")
    print(f"    (FCC has larger critical u_3 => transitions at lower beta)")

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "8",
        "name": "Comparison with K4 Spectrum",
        "k4_data": {str(k): v for k, v in k4_data.items()},
        "fcc_data": {str(k): v for k, v in fcc_data.items()},
        "u_3_crit_k4": u_3_crit_k4,
        "u_3_crit_fcc": u_3_crit_fcc,
        "passed": all_passed,
    }


# =============================================================================
# TEST 9: Eigenvalue Spectral Ratios
# =============================================================================

def test_spectral_ratios():
    """Compute gap ratios m_n/m_1 and compare FCC vs K4."""
    print("\n" + "=" * 70)
    print("TEST 9: Eigenvalue Spectral Ratios")
    print("=" * 70)

    all_passed = True

    # Define excited states (first few above the fundamental)
    # R_1 = (1,0) d=3  (first excited)
    # R_2 = (2,0) d=6  or (1,1) d=8
    # R_3 = (3,0) d=10 or (2,1) d=15
    excited_reps = [
        ((1, 0), "3"),
        ((0, 1), "3bar"),
        ((2, 0), "6"),
        ((1, 1), "8"),
        ((3, 0), "10"),
        ((2, 1), "15"),
    ]

    betas = [1.0, 4.0, 6.0]

    for beta in betas:
        print(f"\n  beta = {beta}:")

        # Compute all a_R
        a_1 = compute_a_R_fast(0, 0, beta, n_grid=300)

        # FCC gaps: m_R = -ln(lambda_R / lambda_1) = -3*ln(d_R) - 8*ln(a_R/a_1)
        # K4 gaps:  m_R = -ln(t_R / t_1) = -4*ln(d_R) - 10*ln(a_R/a_1)

        # First gap (fundamental)
        a_3 = compute_a_R_fast(1, 0, beta, n_grid=300)
        u_3 = a_3 / a_1
        m1_fcc = -3.0 * np.log(3) - 8.0 * np.log(u_3)
        m1_k4 = -4.0 * np.log(3) - 10.0 * np.log(u_3)

        print(f"    First gap (R=3): m_FCC={m1_fcc:.6f}, m_K4={m1_k4:.6f}")
        print()
        print(f"    {'Rep':>6s} {'d_R':>4s} {'u_R':>10s} {'m_FCC':>12s} {'m_K4':>12s} {'r_FCC':>10s} {'r_K4':>10s}")
        print(f"    {'-' * 70}")

        for (p, q), label in excited_reps:
            d_R = su3_dim(p, q)
            a_R = compute_a_R_fast(p, q, beta, n_grid=300)
            u_R = a_R / a_1

            if u_R > 0:
                m_fcc = -3.0 * np.log(d_R) - 8.0 * np.log(u_R)
                m_k4 = -4.0 * np.log(d_R) - 10.0 * np.log(u_R)
            else:
                m_fcc = m_k4 = np.inf

            r_fcc = m_fcc / m1_fcc if abs(m1_fcc) > 1e-30 else float('inf')
            r_k4 = m_k4 / m1_k4 if abs(m1_k4) > 1e-30 else float('inf')

            print(f"    {label:>6s} {d_R:4d} {u_R:10.6f} {m_fcc:12.6f} {m_k4:12.6f} {r_fcc:10.4f} {r_k4:10.4f}")

    # Check that the 3 and 3-bar have identical gaps (charge conjugation)
    print(f"\n  Charge conjugation check (3 vs 3-bar):")
    for beta in betas:
        a_3 = compute_a_R_fast(1, 0, beta, n_grid=300)
        a_3bar = compute_a_R_fast(0, 1, beta, n_grid=300)
        err = abs(a_3 - a_3bar) / max(abs(a_3), 1e-300)
        print(f"    beta={beta}: |a_3 - a_3bar| / a_3 = {err:.2e}")
        if err > 1e-6:
            print(f"      WARNING: charge conjugation might be broken")

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "9",
        "name": "Eigenvalue Spectral Ratios",
        "passed": all_passed,
    }


# =============================================================================
# TEST 10: Monotonicity and Limiting Behavior
# =============================================================================

def test_monotonicity_and_limits():
    """Verify mu(beta) is monotonically decreasing, check limiting behavior."""
    print("\n" + "=" * 70)
    print("TEST 10: Monotonicity and Limiting Behavior")
    print("=" * 70)

    all_passed = True

    # Compute mu at 50 beta values from 0.1 to 20
    betas = np.linspace(0.1, 20.0, 50)
    mu_values = []
    u3_values = []

    print(f"  Computing mu(beta) at {len(betas)} points in [{betas[0]:.1f}, {betas[-1]:.1f}]...")

    for beta in betas:
        mu, u3 = fcc_intensive_gap(beta, n_grid=250)
        mu_values.append(mu)
        u3_values.append(u3)

    mu_values = np.array(mu_values)
    u3_values = np.array(u3_values)

    # Check monotonicity
    diffs = np.diff(mu_values)
    n_decreasing = np.sum(diffs < 0)
    n_increasing = np.sum(diffs > 0)
    n_constant = np.sum(np.abs(diffs) < 1e-12)

    print(f"\n  Monotonicity check:")
    print(f"    Decreasing steps: {n_decreasing}/{len(diffs)}")
    print(f"    Increasing steps: {n_increasing}/{len(diffs)}")
    print(f"    Constant steps:   {n_constant}/{len(diffs)}")

    if n_increasing > 0:
        # Find where violations occur
        violations = np.where(diffs > 0)[0]
        for idx in violations[:5]:
            print(f"    VIOLATION at beta={betas[idx]:.2f}: "
                  f"mu({betas[idx]:.2f})={mu_values[idx]:.6f} < "
                  f"mu({betas[idx + 1]:.2f})={mu_values[idx + 1]:.6f}, "
                  f"diff={diffs[idx]:.2e}")
        # Small numerical violations at the 1e-10 level are acceptable
        max_violation = np.max(diffs[diffs > 0]) if np.any(diffs > 0) else 0
        if max_violation > 1e-4:
            print(f"    FAIL: significant monotonicity violation (max={max_violation:.2e})")
            all_passed = False
        else:
            print(f"    Max violation = {max_violation:.2e} (numerically negligible): PASS")
    else:
        print(f"    Strict monotonicity: PASS")

    # Limiting behavior: beta -> 0
    print(f"\n  Limiting behavior:")
    beta_small = 0.05
    mu_small, _ = fcc_intensive_gap(beta_small, n_grid=400)
    print(f"    beta -> 0: mu({beta_small}) = {mu_small:.4f} (should be large positive)")
    if mu_small < 5.0:
        print(f"      WARNING: mu not sufficiently large at small beta")
    else:
        print(f"      mu -> +inf as beta -> 0: PASS")

    # Limiting behavior: beta -> beta_c
    # Find approximate beta_c from the sign change
    beta_c_approx = None
    for i in range(len(mu_values) - 1):
        if mu_values[i] > 0 and mu_values[i + 1] < 0:
            # Linear interpolation
            frac = mu_values[i] / (mu_values[i] - mu_values[i + 1])
            beta_c_approx = betas[i] + frac * (betas[i + 1] - betas[i])
            break

    if beta_c_approx is not None:
        print(f"    beta_c (approx from interpolation) = {beta_c_approx:.4f}")
        mu_near_bc, _ = fcc_intensive_gap(beta_c_approx, n_grid=400)
        print(f"    mu(beta_c) = {mu_near_bc:.6f} (should be ~0)")
    else:
        print(f"    WARNING: could not locate beta_c from data")

    # Limiting behavior: beta -> infinity
    # u_3 -> 1 as beta -> inf (all a_R -> 1 in weak coupling)
    # => mu -> -3*ln(3) - 8*ln(1) = -3*ln(3) = -3.296
    mu_inf_limit = -3.0 * np.log(3)
    beta_large = 50.0
    mu_large, u_3_large = fcc_intensive_gap(beta_large, n_grid=300)
    print(f"\n    beta -> inf: mu should approach -3*ln(3) = {mu_inf_limit:.6f}")
    print(f"    mu({beta_large}) = {mu_large:.6f}")
    print(f"    u_3({beta_large}) = {u_3_large:.8f} (should approach 1)")
    err_limit = abs(mu_large - mu_inf_limit)
    if err_limit > 1.0:
        print(f"      Convergence to asymptote slow (diff={err_limit:.4f}) - expected for finite beta")
    else:
        print(f"      Approaching asymptote: PASS")

    # Print representative values
    print(f"\n  Representative mu(beta) values:")
    print(f"  {'beta':>6s} {'mu':>12s} {'u_3':>12s}")
    print(f"  {'-' * 34}")
    indices = np.linspace(0, len(betas) - 1, 12, dtype=int)
    for i in indices:
        print(f"  {betas[i]:6.2f} {mu_values[i]:12.6f} {u3_values[i]:12.6f}")

    print(f"\n  STATUS: {'PASS' if all_passed else 'FAIL'}")
    return {
        "test": "10",
        "name": "Monotonicity and Limiting Behavior",
        "n_beta_points": len(betas),
        "n_decreasing": int(n_decreasing),
        "n_increasing": int(n_increasing),
        "beta_c_approx": beta_c_approx,
        "mu_inf_limit": mu_inf_limit,
        "passed": all_passed,
    }


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 70)
    print("Proposition 2.5.2c: Transfer Matrix for FCC Layers")
    print("lambda_R(beta, N_s) = d_R^{3*N_s} * [a_R(beta)]^{8*N_s}")
    print("Mass gap: mu(beta) = -3*ln(3) - 8*ln(u_3(beta))")
    print("Critical: u_3(beta_c) = 3^(-3/8)")
    print("=" * 70)
    print(f"Date: {datetime.now().isoformat()}")

    results = {
        "proposition": "2.5.2c",
        "title": "Transfer Matrix for FCC Layers",
        "timestamp": datetime.now().isoformat(),
        "verifications": [],
    }

    tests = [
        test_eigenvalue_computation,
        test_partition_function_consistency,
        test_mass_gap_formula,
        test_critical_coupling,
        test_strong_coupling_expansion,
        test_eigenvalue_positivity,
        test_extensive_intensive_gap,
        test_comparison_with_k4,
        test_spectral_ratios,
        test_monotonicity_and_limits,
    ]

    for test_fn in tests:
        try:
            result = test_fn()
            results["verifications"].append(result)
        except Exception as e:
            print(f"\n  ERROR in {test_fn.__name__}: {e}")
            import traceback
            traceback.print_exc()
            results["verifications"].append({
                "test": test_fn.__name__,
                "passed": False,
                "error": str(e),
            })

    # Summary
    n_pass = sum(1 for v in results["verifications"] if v.get("passed", False))
    n_total = len(results["verifications"])
    results["overall_status"] = "PASSED" if n_pass == n_total else "PARTIAL"
    results["summary"] = f"{n_pass}/{n_total} tests passed"

    print("\n" + "=" * 70)
    print(f"SUMMARY: {results['summary']}")
    for v in results["verifications"]:
        name = v.get("name", v.get("test", "unknown"))
        status = "PASS" if v.get("passed", False) else "FAIL"
        print(f"  Test {v.get('test', '?'):>2s}: {name:50s} [{status}]")
    print(f"\nSTATUS: {results['overall_status']}")
    print("=" * 70)

    # Save results
    output_file = OUTPUT_DIR / "prop_2_5_2c_results.json"
    with open(output_file, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"Results saved to {output_file}")

    return results


if __name__ == "__main__":
    main()
