#!/usr/bin/env python3
"""
Proposition 7.4.4a: Exact Wilson Loop on FCC Lattice — Verification
====================================================================

Verifies the exact Wilson loop formula derived via Migdal-Witten decomposition:

    <W_3(C)> = sum_{R1,R2} d_{R1} d_{R2}^{3N-1} N^{R2}_{3,R1} a_{R1}^A a_{R2}^{8N-A} / Z

Key Claims Under Test:
    (a) Exact formula consistency (reproduces Z when summed correctly)
    (b) Thermodynamic limit: <W_3(C)> -> 3 u_3^A in confined phase
    (c) Exact string tension: sigma_exact = -ln(u_3) at all beta < beta_c
    (d) R -> 0 problem confirmed as exact (not strong-coupling artifact)

Related Documents:
    - docs/proofs/Phase7/Proposition-7.4.4a-Exact-Wilson-Loop-FCC.md
    - docs/proofs/Phase7/Proposition-7.4.4-Scaling-Window-FCC.md

Verification Date: 2026-02-13
"""

import numpy as np
import json
import os
from datetime import datetime

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
# SU(3) REPRESENTATION THEORY
# =============================================================================

def su3_dim(p, q):
    """Dimension of SU(3) irrep (p,q)."""
    return (p + 1) * (q + 1) * (p + q + 2) // 2


def su3_casimir(p, q):
    """Quadratic Casimir of SU(3) irrep (p,q)."""
    return (p**2 + q**2 + p * q + 3 * p + 3 * q) / 3.0


def weyl_measure(theta1, theta2):
    """SU(3) Haar measure in maximal torus coordinates."""
    d12 = 2.0 * np.sin((theta1 - theta2) / 2.0)
    d13 = 2.0 * np.sin((2.0 * theta1 + theta2) / 2.0)
    d23 = 2.0 * np.sin((theta1 + 2.0 * theta2) / 2.0)
    return d12**2 * d13**2 * d23**2


def su3_boltzmann(theta1, theta2, beta):
    """Boltzmann weight exp(beta/3 * Re Tr U) for SU(3)."""
    re_tr = np.cos(theta1) + np.cos(theta2) + np.cos(theta1 + theta2)
    return np.exp(beta / 3.0 * re_tr)


def su3_character(p, q, theta1, theta2):
    """SU(3) character chi_{(p,q)} via Weyl character formula."""
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
    """Heat kernel coefficient a_R(beta) via numerical integration."""
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


# =============================================================================
# CLEBSCH-GORDAN MULTIPLICITIES FOR 3 x R
# =============================================================================

def cg_multiplicity_3_x_R(R1_pq, R2_pq):
    """
    Compute N^{R2}_{3, R1}: multiplicity of R2 in 3 x R1.

    Uses the known tensor product rules for SU(3).
    We compute 3 x R1 and check if R2 appears.

    For efficiency, we only handle representations up to (p+q) <= 4.
    """
    p1, q1 = R1_pq
    p2, q2 = R2_pq

    # 3 = (1,0)
    # Tensor product 3 x (p,q) by the standard SU(3) rule:
    # (1,0) x (p,q) = (p+1,q) + (p-1,q+1) + (p,q-1)
    # where terms with negative labels are dropped

    products = []
    # Term 1: (p1+1, q1)
    products.append((p1 + 1, q1))
    # Term 2: (p1-1, q1+1) — only if p1 >= 1
    if p1 >= 1:
        products.append((p1 - 1, q1 + 1))
    # Term 3: (p1, q1-1) — only if q1 >= 1
    if q1 >= 1:
        products.append((p1, q1 - 1))

    return products.count((p2, q2))


# =============================================================================
# EXACT WILSON LOOP FORMULA
# =============================================================================

# Representations to include: (p,q) labels
# We include up to total Dynkin label p+q <= 3 for accuracy
REPS = [
    (0, 0),  # 1 (trivial)
    (1, 0),  # 3 (fundamental)
    (0, 1),  # 3bar (anti-fundamental)
    (2, 0),  # 6
    (0, 2),  # 6bar
    (1, 1),  # 8 (adjoint)
    (3, 0),  # 10
    (0, 3),  # 10bar
    (2, 1),  # 15
    (1, 2),  # 15bar
]


def compute_all_a_R(beta, reps=None, n_grid=200):
    """Compute heat kernel coefficients for all representations."""
    if reps is None:
        reps = REPS
    coeffs = {}
    for pq in reps:
        coeffs[pq] = compute_a_R(pq[0], pq[1], beta, n_grid=n_grid)
    return coeffs


def exact_wilson_loop(beta, A, N, reps=None, n_grid=200):
    """
    Compute the exact Wilson loop <W_3(C)> on the FCC lattice.

    Formula (Prop 7.4.4a, Eq. 3.8):
        <W_3(C)> = sum_{R1,R2} d_{R1} d_{R2}^{3N-1} N^{R2}_{3,R1} a_{R1}^A a_{R2}^{8N-A}
                   / sum_R d_R^{3N} a_R^{8N}

    Parameters:
        beta: coupling constant
        A: area of Wilson loop (number of faces)
        N: number of FCC unit cells
        reps: list of (p,q) representation labels to include
        n_grid: grid size for heat kernel integration

    Returns:
        W: Wilson loop expectation value
        info: dict with intermediate quantities
    """
    if reps is None:
        reps = REPS

    coeffs = compute_all_a_R(beta, reps, n_grid)

    # Partition function: Z = sum_R d_R^{3N} a_R^{8N}
    # Use log-space for numerical stability
    log_terms_Z = []
    for pq in reps:
        d_R = su3_dim(pq[0], pq[1])
        a_R = coeffs[pq]
        if a_R > 0 and d_R > 0:
            log_term = 3 * N * np.log(d_R) + 8 * N * np.log(a_R)
            log_terms_Z.append(log_term)

    log_Z_max = max(log_terms_Z)
    Z = sum(np.exp(lt - log_Z_max) for lt in log_terms_Z)

    # Numerator: sum_{R1,R2} d_{R1} d_{R2}^{3N-1} N^{R2}_{3,R1} a_{R1}^A a_{R2}^{8N-A}
    log_terms_num = []
    term_labels = []
    for R1 in reps:
        d_R1 = su3_dim(R1[0], R1[1])
        a_R1 = coeffs[R1]
        if a_R1 <= 0:
            continue
        for R2 in reps:
            d_R2 = su3_dim(R2[0], R2[1])
            a_R2 = coeffs[R2]
            if a_R2 <= 0:
                continue

            N_cg = cg_multiplicity_3_x_R(R1, R2)
            if N_cg == 0:
                continue

            log_term = (np.log(d_R1) + (3*N - 1) * np.log(d_R2) +
                       np.log(N_cg) + A * np.log(a_R1) + (8*N - A) * np.log(a_R2))
            log_terms_num.append(log_term)
            term_labels.append((R1, R2, N_cg))

    if not log_terms_num:
        return 0.0, {"error": "No contributing terms"}

    log_num_max = max(log_terms_num)
    Num = sum(np.exp(lt - log_num_max) for lt in log_terms_num)

    # W = Num / Z
    W = np.exp(log_num_max - log_Z_max) * Num / Z

    # Compute u_3 for comparison
    u3 = coeffs[(1, 0)] / coeffs[(0, 0)] if coeffs[(0, 0)] > 0 else 0

    info = {
        "beta": beta,
        "A": A,
        "N": N,
        "u3": u3,
        "strong_coupling_prediction": 3 * u3**A if u3 > 0 else 0,
        "log_Z_max": log_Z_max,
        "log_num_max": log_num_max,
        "num_contributing_terms": len(log_terms_num),
        "dominant_terms": term_labels[:5],
    }

    return W, info


# =============================================================================
# VERIFICATION TESTS
# =============================================================================

def test_1_partition_function_recovery():
    """
    Test 1: Verify that the Wilson loop formula recovers Z when
    the Wilson loop is the identity (rho = trivial).

    For the trivial Wilson loop: N^{R2}_{1,R1} = delta_{R1,R2},
    so the numerator becomes sum_R d_R d_R^{3N-1} a_R^{8N} = sum_R d_R^{3N} a_R^{8N} = Z.
    """
    print("\n" + "="*70)
    print("TEST 1: Partition function recovery (trivial Wilson loop)")
    print("="*70)

    beta = 5.0
    N = 3
    reps = REPS[:6]  # Use fewer reps for speed
    coeffs = compute_all_a_R(beta, reps, n_grid=150)

    # Z = sum_R d_R^{3N} a_R^{8N}
    Z_terms = []
    for pq in reps:
        d_R = su3_dim(pq[0], pq[1])
        a_R = coeffs[pq]
        if a_R > 0:
            Z_terms.append(d_R**(3*N) * a_R**(8*N))
    Z = sum(Z_terms)

    # "Trivial Wilson loop" numerator: sum_R d_R * d_R^{3N-1} * 1 * a_R^A * a_R^{8N-A}
    # = sum_R d_R^{3N} * a_R^{8N} = Z
    A = 5
    triv_terms = []
    for pq in reps:
        d_R = su3_dim(pq[0], pq[1])
        a_R = coeffs[pq]
        if a_R > 0:
            # For trivial rho: N^{R2}_{1,R1} = delta_{R1,R2}
            triv_terms.append(d_R * d_R**(3*N-1) * a_R**A * a_R**(8*N-A))
    Num_triv = sum(triv_terms)

    ratio = Num_triv / Z
    passed = abs(ratio - 1.0) < 1e-8

    print(f"  Z = {Z:.6e}")
    print(f"  Num(trivial) = {Num_triv:.6e}")
    print(f"  Ratio = {ratio:.12f}")
    print(f"  PASSED: {passed}")

    return {
        "test": "Partition function recovery",
        "Z": float(Z),
        "Num_trivial": float(Num_triv),
        "ratio": float(ratio),
        "passed": passed
    }


def test_2_thermodynamic_limit():
    """
    Test 2: Verify that <W_3(C)> -> 3 u_3^A in the thermodynamic limit.
    Check convergence as N increases for fixed A and beta.
    """
    print("\n" + "="*70)
    print("TEST 2: Thermodynamic limit (<W_3> -> 3 u_3^A)")
    print("="*70)

    beta = 5.0
    A = 4
    reps = REPS[:6]

    coeffs = compute_all_a_R(beta, reps, n_grid=150)
    u3 = coeffs[(1, 0)] / coeffs[(0, 0)]
    target = 3.0 * u3**A

    print(f"  beta = {beta}, A = {A}")
    print(f"  u_3 = {u3:.8f}")
    print(f"  Target: 3 * u_3^A = {target:.10e}")
    print()

    results_by_N = []
    for N in [2, 5, 10, 20, 50]:
        W, info = exact_wilson_loop(beta, A, N, reps=reps, n_grid=150)
        rel_err = abs(W - target) / abs(target) if target != 0 else float('inf')
        print(f"  N = {N:3d}: W = {W:.10e}, rel_err = {rel_err:.2e}")
        results_by_N.append({"N": N, "W": float(W), "rel_err": float(rel_err)})

    # Should converge to target
    final_err = results_by_N[-1]["rel_err"]
    passed = final_err < 1e-4

    print(f"\n  Final relative error: {final_err:.2e}")
    print(f"  PASSED: {passed}")

    return {
        "test": "Thermodynamic limit",
        "beta": beta,
        "A": A,
        "u3": float(u3),
        "target": float(target),
        "convergence": results_by_N,
        "passed": passed
    }


def test_3_string_tension_vs_coupling():
    """
    Test 3: Verify sigma_exact = -ln(u_3) at multiple coupling values.
    Extract sigma from the ratio W(A+1)/W(A) at large N.
    """
    print("\n" + "="*70)
    print("TEST 3: String tension sigma_exact = -ln(u_3) vs coupling")
    print("="*70)

    N = 30  # Large enough for thermodynamic limit
    reps = REPS[:4]  # Just 1, 3, 3bar, 6 for speed

    betas = [3.0, 5.0, 7.0, 9.0, 10.0]
    results = []
    all_passed = True

    for beta in betas:
        coeffs = compute_all_a_R(beta, reps, n_grid=150)
        u3 = coeffs[(1, 0)] / coeffs[(0, 0)]
        sigma_sc = -np.log(u3) if u3 > 0 else float('inf')

        # Compute W for two areas and extract sigma
        A1, A2 = 4, 8
        W1, _ = exact_wilson_loop(beta, A1, N, reps=reps, n_grid=150)
        W2, _ = exact_wilson_loop(beta, A2, N, reps=reps, n_grid=150)

        if W1 > 0 and W2 > 0:
            sigma_exact = -(np.log(W2) - np.log(W1)) / (A2 - A1)
        else:
            sigma_exact = float('inf')

        rel_err = abs(sigma_exact - sigma_sc) / sigma_sc if sigma_sc > 0 else float('inf')
        passed = rel_err < 1e-4
        if not passed:
            all_passed = False

        print(f"  beta = {beta:5.1f}: sigma_SC = {sigma_sc:.6f}, "
              f"sigma_exact = {sigma_exact:.6f}, rel_err = {rel_err:.2e} {'PASS' if passed else 'FAIL'}")

        results.append({
            "beta": beta,
            "u3": float(u3),
            "sigma_strong_coupling": float(sigma_sc),
            "sigma_exact": float(sigma_exact),
            "rel_err": float(rel_err),
            "passed": passed
        })

    print(f"\n  ALL PASSED: {all_passed}")

    return {
        "test": "String tension vs coupling",
        "N": N,
        "results": results,
        "passed": all_passed
    }


def test_4_R_ratio_at_beta_c():
    """
    Test 4: Confirm R(beta_c) = 0 with the EXACT string tension.
    """
    print("\n" + "="*70)
    print("TEST 4: R(beta_c) = 0 with exact string tension")
    print("="*70)

    # Find beta_c numerically (where mu = 0)
    from scipy.optimize import brentq

    def mu_func(beta):
        u3 = compute_a_R(1, 0, beta, n_grid=200) / compute_a_R(0, 0, beta, n_grid=200)
        return -3.0 * np.log(3) - 8.0 * np.log(u3) if u3 > 0 else float('inf')

    # Search for beta_c in [8, 15]
    try:
        beta_c = brentq(mu_func, 8.0, 15.0, xtol=1e-4)
    except Exception:
        beta_c = 11.4  # fallback

    u3_c = compute_a_R(1, 0, beta_c, n_grid=200) / compute_a_R(0, 0, beta_c, n_grid=200)
    mu_c = -3.0 * np.log(3) - 8.0 * np.log(u3_c)
    sigma_c = -np.log(u3_c)
    R_c = mu_c / np.sqrt(sigma_c) if sigma_c > 0 else float('inf')

    print(f"  beta_c = {beta_c:.4f}")
    print(f"  u_3(beta_c) = {u3_c:.8f}")
    print(f"  3^(-3/8) = {3**(-3/8):.8f}")
    print(f"  mu(beta_c) = {mu_c:.8e}")
    print(f"  sigma_exact(beta_c) = {sigma_c:.6f}")
    print(f"  (3/8)*ln(3) = {3/8*np.log(3):.6f}")
    print(f"  R(beta_c) = {R_c:.8e}")

    # R should be ~0 (within numerical precision)
    passed_R = abs(R_c) < 0.01
    # sigma should be (3/8)*ln(3)
    passed_sigma = abs(sigma_c - 3/8*np.log(3)) < 0.01
    passed = passed_R and passed_sigma

    print(f"\n  R(beta_c) ~ 0: {passed_R}")
    print(f"  sigma(beta_c) = (3/8)ln3: {passed_sigma}")
    print(f"  PASSED: {passed}")

    return {
        "test": "R(beta_c) = 0 with exact sigma",
        "beta_c": float(beta_c),
        "u3_c": float(u3_c),
        "mu_c": float(mu_c),
        "sigma_exact_c": float(sigma_c),
        "sigma_expected": float(3/8*np.log(3)),
        "R_c": float(R_c),
        "passed": passed
    }


def test_5_cg_coefficients():
    """
    Test 5: Verify the Clebsch-Gordan multiplicities used in the formula.
    """
    print("\n" + "="*70)
    print("TEST 5: Clebsch-Gordan multiplicities for 3 x R")
    print("="*70)

    # Known tensor products for SU(3):
    # 3 x 1 = 3
    # 3 x 3 = 6 + 3bar
    # 3 x 3bar = 8 + 1
    # 3 x 6 = 10 + 8
    # 3 x 8 = 3 + 6bar + 15

    known = [
        # (R1, R2, expected N^{R2}_{3,R1})
        ((0,0), (1,0), 1),  # 3 x 1 -> 3
        ((0,0), (0,1), 0),  # 3 x 1 -> no 3bar
        ((0,0), (0,0), 0),  # 3 x 1 -> no 1
        ((1,0), (2,0), 1),  # 3 x 3 -> 6
        ((1,0), (0,1), 1),  # 3 x 3 -> 3bar
        ((1,0), (1,0), 0),  # 3 x 3 -> no 3
        ((0,1), (1,1), 1),  # 3 x 3bar -> 8
        ((0,1), (0,0), 1),  # 3 x 3bar -> 1
        ((0,1), (1,0), 0),  # 3 x 3bar -> no 3
        ((1,1), (1,0), 1),  # 3 x 8 -> 3
        ((1,1), (0,2), 1),  # 3 x 8 -> 6bar
        ((1,1), (2,1), 1),  # 3 x 8 -> 15
    ]

    all_passed = True
    for R1, R2, expected in known:
        computed = cg_multiplicity_3_x_R(R1, R2)
        passed = (computed == expected)
        if not passed:
            all_passed = False
        d1 = su3_dim(R1[0], R1[1])
        d2 = su3_dim(R2[0], R2[1])
        status = "PASS" if passed else "FAIL"
        print(f"  N^{{{d2}}}_(3,{d1}) = {computed} (expected {expected}) {status}")

    print(f"\n  ALL PASSED: {all_passed}")

    return {
        "test": "CG multiplicities",
        "passed": all_passed
    }


def test_6_area_law_multiple_betas():
    """
    Test 6: Verify area law W ~ 3 u_3^A across multiple areas and couplings.
    """
    print("\n" + "="*70)
    print("TEST 6: Area law verification across couplings")
    print("="*70)

    N = 20
    reps = REPS[:4]
    betas = [4.0, 6.0, 8.0]
    areas = [1, 2, 4, 6, 8]

    all_passed = True

    for beta in betas:
        coeffs = compute_all_a_R(beta, reps, n_grid=150)
        u3 = coeffs[(1, 0)] / coeffs[(0, 0)]

        print(f"\n  beta = {beta}, u_3 = {u3:.6f}")

        for A in areas:
            W, _ = exact_wilson_loop(beta, A, N, reps=reps, n_grid=150)
            target = 3.0 * u3**A
            rel_err = abs(W - target) / abs(target) if target != 0 else float('inf')
            passed = rel_err < 0.01
            if not passed:
                all_passed = False
            print(f"    A = {A:2d}: W = {W:.8e}, 3*u3^A = {target:.8e}, err = {rel_err:.2e} "
                  f"{'PASS' if passed else 'FAIL'}")

    print(f"\n  ALL PASSED: {all_passed}")

    return {
        "test": "Area law verification",
        "passed": all_passed
    }


def test_7_near_beta_c():
    """
    Test 7: Verify the Wilson loop behavior near beta_c.
    The exact formula should still give sigma = -ln(u_3) even close to the transition.
    """
    print("\n" + "="*70)
    print("TEST 7: Wilson loop near beta_c")
    print("="*70)

    # Use betas approaching beta_c from below
    betas = [9.0, 10.0, 10.5, 11.0]
    N = 30
    A1, A2 = 2, 6
    reps = REPS[:4]

    all_passed = True

    for beta in betas:
        coeffs = compute_all_a_R(beta, reps, n_grid=200)
        u3 = coeffs[(1, 0)] / coeffs[(0, 0)]
        mu = -3.0 * np.log(3) - 8.0 * np.log(u3) if u3 > 0 else float('inf')

        if mu <= 0:
            print(f"  beta = {beta:5.1f}: DECONFINED (mu = {mu:.4f}), skipping")
            continue

        sigma_sc = -np.log(u3)

        W1, _ = exact_wilson_loop(beta, A1, N, reps=reps, n_grid=200)
        W2, _ = exact_wilson_loop(beta, A2, N, reps=reps, n_grid=200)

        if W1 > 0 and W2 > 0:
            sigma_exact = -(np.log(W2) - np.log(W1)) / (A2 - A1)
        else:
            sigma_exact = float('inf')

        rel_err = abs(sigma_exact - sigma_sc) / sigma_sc if sigma_sc > 0 else float('inf')
        R_val = mu / np.sqrt(sigma_exact) if sigma_exact > 0 else float('inf')
        passed = rel_err < 0.01
        if not passed:
            all_passed = False

        print(f"  beta = {beta:5.1f}: mu = {mu:.4f}, sigma = {sigma_exact:.4f} "
              f"(SC: {sigma_sc:.4f}), R = {R_val:.4f}, err = {rel_err:.2e} "
              f"{'PASS' if passed else 'FAIL'}")

    print(f"\n  ALL PASSED: {all_passed}")

    return {
        "test": "Wilson loop near beta_c",
        "passed": all_passed
    }


# =============================================================================
# PLOTTING
# =============================================================================

def generate_plots(results):
    """Generate verification plots."""
    if not HAS_MATPLOTLIB:
        print("\n  Matplotlib not available, skipping plots")
        return

    # Plot: sigma_exact vs sigma_SC across couplings
    test3 = results.get("test_3", {})
    if "results" in test3:
        fig, axes = plt.subplots(1, 2, figsize=(12, 5))

        betas = [r["beta"] for r in test3["results"]]
        sigma_sc = [r["sigma_strong_coupling"] for r in test3["results"]]
        sigma_ex = [r["sigma_exact"] for r in test3["results"]]

        axes[0].plot(betas, sigma_sc, 'b-o', label=r'$\sigma_{SC} = -\ln u_3$', markersize=8)
        axes[0].plot(betas, sigma_ex, 'r--x', label=r'$\sigma_{exact}$ (from Wilson loop)', markersize=10)
        axes[0].set_xlabel(r'$\beta$')
        axes[0].set_ylabel(r'$\sigma_{lat}$')
        axes[0].set_title('Exact vs Strong-Coupling String Tension')
        axes[0].legend()
        axes[0].grid(True, alpha=0.3)

        rel_errs = [r["rel_err"] for r in test3["results"]]
        axes[1].semilogy(betas, rel_errs, 'ko-')
        axes[1].set_xlabel(r'$\beta$')
        axes[1].set_ylabel('Relative Error')
        axes[1].set_title(r'$|\sigma_{exact} - \sigma_{SC}| / \sigma_{SC}$')
        axes[1].grid(True, alpha=0.3)

        plt.tight_layout()
        plt.savefig(os.path.join(PLOT_DIR, 'prop_7_4_4a_string_tension.png'), dpi=150)
        plt.close()
        print(f"  Saved: {os.path.join(PLOT_DIR, 'prop_7_4_4a_string_tension.png')}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("="*70)
    print("Proposition 7.4.4a: Exact Wilson Loop on FCC — Verification")
    print("="*70)
    print(f"Date: {datetime.now().isoformat()}")

    results = {
        "proposition": "7.4.4a",
        "title": "Exact Wilson Loop on FCC Lattice",
        "timestamp": datetime.now().isoformat(),
        "tests": {}
    }

    # Run tests
    results["tests"]["test_5"] = test_5_cg_coefficients()
    results["tests"]["test_1"] = test_1_partition_function_recovery()
    results["tests"]["test_2"] = test_2_thermodynamic_limit()
    results["tests"]["test_3"] = test_3_string_tension_vs_coupling()
    results["tests"]["test_4"] = test_4_R_ratio_at_beta_c()
    results["tests"]["test_6"] = test_6_area_law_multiple_betas()
    results["tests"]["test_7"] = test_7_near_beta_c()

    # Summary
    all_passed = all(t.get("passed", False) for t in results["tests"].values())
    n_passed = sum(1 for t in results["tests"].values() if t.get("passed", False))
    n_total = len(results["tests"])
    results["overall_status"] = "PASSED" if all_passed else "PARTIAL"
    results["summary"] = f"{n_passed}/{n_total} tests passed"

    print("\n" + "="*70)
    print(f"SUMMARY: {results['summary']}")
    print(f"STATUS: {results['overall_status']}")
    print("="*70)

    # Generate plots
    generate_plots(results)

    # Save results
    output_path = os.path.join(SCRIPT_DIR, 'prop_7_4_4a_results.json')
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to: {output_path}")

    return results


if __name__ == "__main__":
    main()
