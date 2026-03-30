#!/usr/bin/env python3
"""
Lemma 5.4.1a: Maximum Curvature Bound — Adversarial Physics Verification
=========================================================================

Comprehensive adversarial verification of all claims in Lemma 5.4.1a,
including the FCC discrete Laplacian spectral radius, form factor,
Kretschmann bound, minimum trapped surface area, and Lorentz invariance.

Related Documents:
- Proof: docs/proofs/Phase5/Lemma-5.4.1a-Maximum-Curvature-Bound.md
- Verification record: docs/proofs/verification-records/Lemma-5.4.1a-Multi-Agent-Verification-2026-02-27.md

Key Findings:
- TRUE spectral radius = 16/a^2, NOT 24/a^2 as claimed
- TRUE form factor minimum = -1/3, NOT -1 as claimed
- Discrete Laplacian = 2x continuum Laplacian
- Minimum closed surface area = 2*sqrt(3)*a^2, NOT sqrt(3)*a^2

Verification Date: 2026-02-27
"""

import numpy as np
from scipy.optimize import minimize, differential_evolution
import json
import os
from datetime import datetime

# ==============================================================================
# PHYSICAL CONSTANTS
# ==============================================================================

ELL_P = 1.616255e-35  # Planck length (m)
LN3 = np.log(3)
SQRT3 = np.sqrt(3)

# Lattice spacing from Prop 0.0.17r
A_SQUARED_OVER_LP2 = 8 * LN3 / SQRT3  # ≈ 5.073
A_OVER_LP = np.sqrt(A_SQUARED_OVER_LP2)  # ≈ 2.253

# ==============================================================================
# FCC LATTICE GEOMETRY
# ==============================================================================

def get_fcc_nn_vectors(a=1.0):
    """Return the 12 FCC nearest-neighbor vectors.

    FCC nn vectors: (a/sqrt(2))(±1, ±1, 0) and permutations.
    Three groups of 4: xy-plane, xz-plane, yz-plane.
    """
    scale = a / np.sqrt(2)
    deltas = []
    # Group 1: xy-plane (±1, ±1, 0)
    for s1 in [1, -1]:
        for s2 in [1, -1]:
            deltas.append(np.array([s1, s2, 0.0]) * scale)
    # Group 2: xz-plane (±1, 0, ±1)
    for s1 in [1, -1]:
        for s2 in [1, -1]:
            deltas.append(np.array([s1, 0.0, s2]) * scale)
    # Group 3: yz-plane (0, ±1, ±1)
    for s1 in [1, -1]:
        for s2 in [1, -1]:
            deltas.append(np.array([0.0, s1, s2]) * scale)
    return deltas


# ==============================================================================
# EIGENVALUE AND FORM FACTOR FUNCTIONS
# ==============================================================================

def eigenvalue_direct(k, deltas, a=1.0):
    """Compute λ(k) by direct summation over all 12 nn vectors."""
    return sum(np.cos(np.dot(k, d)) - 1 for d in deltas) / a**2


def eigenvalue_factored(k, a=1.0):
    """Compute λ(k) using the analytic factorization.

    The 12 cosine sum factors as:
    sum cos(k·δ_j) = 4[cos(u)cos(v) + cos(u)cos(w) + cos(v)cos(w)]
    where u = k_x·a/√2, v = k_y·a/√2, w = k_z·a/√2.
    """
    scale = a / np.sqrt(2)
    u, v, w = k[0] * scale, k[1] * scale, k[2] * scale
    cu, cv, cw = np.cos(u), np.cos(v), np.cos(w)
    f = cu * cv + cu * cw + cv * cw
    return (4 * f - 12) / a**2


def form_factor(k, deltas):
    """Compute lattice form factor F(k) = (1/12) Σ cos(k·δ_j)."""
    return sum(np.cos(np.dot(k, d)) for d in deltas) / 12.0


def form_factor_factored(k, a=1.0):
    """Compute F(k) using analytic factorization: F = (1/3)(cos u cos v + ...)."""
    scale = a / np.sqrt(2)
    u, v, w = k[0] * scale, k[1] * scale, k[2] * scale
    cu, cv, cw = np.cos(u), np.cos(v), np.cos(w)
    return (cu * cv + cu * cw + cv * cw) / 3.0


# ==============================================================================
# TEST FUNCTIONS
# ==============================================================================

def test_nn_vectors(deltas, a=1.0):
    """Test 1: Verify FCC nearest-neighbor vectors."""
    n_vectors = len(deltas)
    unique = len(set(tuple(np.round(d, 10)) for d in deltas))
    lengths = [np.linalg.norm(d) for d in deltas]
    all_correct_length = all(abs(l - a) < 1e-10 for l in lengths)

    # Check coordination number
    passed = (n_vectors == 12 and unique == 12 and all_correct_length)
    return {
        "name": "FCC nearest-neighbor vectors",
        "n_vectors": n_vectors,
        "n_unique": unique,
        "all_correct_length": bool(all_correct_length),
        "passed": bool(passed),
        "notes": "z=12 confirmed" if passed else "VECTOR ERROR"
    }


def test_factorization_identity(deltas, a=1.0, n_tests=10000):
    """Test 2: Verify cosine sum factorization identity."""
    np.random.seed(42)
    max_err = 0.0
    for _ in range(n_tests):
        k = np.random.uniform(-10, 10, 3)
        direct = eigenvalue_direct(k, deltas, a)
        factored = eigenvalue_factored(k, a)
        err = abs(direct - factored)
        max_err = max(max_err, err)

    passed = max_err < 1e-12
    return {
        "name": "Cosine sum factorization identity",
        "n_tests": n_tests,
        "max_error": float(max_err),
        "passed": bool(passed),
        "notes": "Σcos(k·δ_j) = 4[cos(u)cos(v) + cos(u)cos(w) + cos(v)cos(w)]"
    }


def test_spectral_radius_analytic():
    """Test 3: Prove spectral radius = 16/a² via analytic corner analysis.

    λ(k) = (4f - 12)/a² where f = xy + xz + yz, x,y,z ∈ [-1,1].
    Extrema of f occur at corners of the cube [-1,1]³.
    """
    corners = []
    for x in [-1, 1]:
        for y in [-1, 1]:
            for z in [-1, 1]:
                f = x * y + x * z + y * z
                corners.append({"xyz": (x, y, z), "f": f, "lambda_a2": 4 * f - 12})

    f_values = [c["f"] for c in corners]
    f_min = min(f_values)
    f_max = max(f_values)
    lambda_min = 4 * f_min - 12  # Most negative eigenvalue
    spectral_radius = abs(lambda_min)

    passed = (abs(spectral_radius - 16.0) < 1e-10)
    return {
        "name": "Spectral radius (analytic corner analysis)",
        "f_min": float(f_min),
        "f_max": float(f_max),
        "lambda_min_times_a2": float(lambda_min),
        "spectral_radius_times_a2": float(spectral_radius),
        "paper_claims": 24.0,
        "correct_value": 16.0,
        "passed": bool(passed),
        "corner_details": corners,
        "notes": "f_min = -1, NOT -3. At most 8/12 cosines can equal -1."
    }


def test_spectral_radius_brute_force(deltas, a=1.0, N=150):
    """Test 4: Brute-force grid search over momentum space."""
    max_abs = 0.0
    best_k = None

    for i1 in range(N):
        for i2 in range(N):
            for i3 in range(N):
                # Sample k-vectors spanning the BZ
                K = np.array([i1, i2, i3]) * 2 * np.pi / N
                k = K * np.sqrt(2) / a
                lam = eigenvalue_direct(k, deltas, a)
                if abs(lam) > max_abs:
                    max_abs = abs(lam)
                    best_k = k.copy()

    matches_16 = abs(max_abs - 16.0) < 0.2
    matches_24 = abs(max_abs - 24.0) < 0.2
    return {
        "name": "Spectral radius (brute-force grid, N={})".format(N),
        "max_abs_lambda_a2": float(max_abs),
        "matches_paper_24": bool(matches_24),
        "matches_correct_16": bool(matches_16),
        "passed": bool(matches_16 and not matches_24),
        "notes": f"Grid search with {N}³ = {N**3} points"
    }


def test_spectral_radius_scipy(deltas, a=1.0, n_starts=500):
    """Test 5: Scipy global optimization for spectral radius."""
    best_min = 0.0
    np.random.seed(123)

    for _ in range(n_starts):
        k0 = np.random.uniform(-np.pi * np.sqrt(2) / a,
                                 np.pi * np.sqrt(2) / a, 3)
        res = minimize(lambda k: eigenvalue_direct(k, deltas, a),
                       k0, method='Nelder-Mead',
                       options={'xatol': 1e-12, 'fatol': 1e-12})
        if res.fun < best_min:
            best_min = res.fun

    spectral_radius = abs(best_min)
    matches_16 = abs(spectral_radius - 16.0) < 0.1
    return {
        "name": "Spectral radius (scipy optimization)",
        "n_starts": n_starts,
        "spectral_radius_a2": float(spectral_radius),
        "matches_correct_16": bool(matches_16),
        "passed": bool(matches_16),
        "notes": f"Nelder-Mead with {n_starts} random starts"
    }


def test_high_symmetry_points(deltas, a=1.0):
    """Test 6: Eigenvalues and form factor at FCC BZ high-symmetry points."""
    factor = np.pi * np.sqrt(2) / a  # = 2π/a_conv

    points = {
        "Gamma": np.array([0.0, 0.0, 0.0]),
        "X":     np.array([1.0, 0.0, 0.0]) * factor,
        "W":     np.array([1.0, 0.5, 0.0]) * factor,
        "L":     np.array([0.5, 0.5, 0.5]) * factor,
        "K":     np.array([0.75, 0.75, 0.0]) * factor,
        "U":     np.array([1.0, 0.25, 0.25]) * factor,
    }

    results = {}
    for name, k in points.items():
        lam = eigenvalue_direct(k, deltas, a)
        F = form_factor(k, deltas)
        results[name] = {
            "lambda_a2": float(lam),
            "abs_lambda_a2": float(abs(lam)),
            "form_factor": float(F)
        }

    # Check: max |λ| should be at X (or W), giving 16/a²
    max_abs = max(v["abs_lambda_a2"] for v in results.values())
    max_at_X = abs(results["X"]["abs_lambda_a2"] - 16.0) < 0.1
    max_at_W = abs(results["W"]["abs_lambda_a2"] - 16.0) < 0.1

    return {
        "name": "High-symmetry BZ points",
        "points": results,
        "max_abs_lambda_a2": float(max_abs),
        "spectral_radius_at_X_or_W": bool(max_at_X or max_at_W),
        "passed": bool(abs(max_abs - 16.0) < 0.1),
        "notes": "X and W both give |λ| = 16/a²"
    }


def test_form_factor_range(deltas, a=1.0, N=100):
    """Test 7: Verify form factor range is [-1/3, 1], not [-1, 1]."""
    F_min = 1.0
    F_max = -1.0

    for i1 in range(N):
        for i2 in range(N):
            for i3 in range(N):
                K = np.array([i1, i2, i3]) * 2 * np.pi / N
                k = K * np.sqrt(2) / a
                F_val = form_factor(k, deltas)
                F_min = min(F_min, F_val)
                F_max = max(F_max, F_val)

    F0 = form_factor(np.array([0, 0, 0]), deltas)

    correct_F0 = abs(F0 - 1.0) < 1e-10
    correct_Fmin = abs(F_min - (-1.0 / 3.0)) < 0.01
    paper_Fmin = abs(F_min - (-1.0)) < 0.05

    return {
        "name": "Form factor range",
        "F_at_zero": float(F0),
        "F_min": float(F_min),
        "F_max": float(F_max),
        "paper_claims_F_min": -1.0,
        "correct_F_min": -1.0 / 3.0,
        "F0_correct": bool(correct_F0),
        "Fmin_matches_correct": bool(correct_Fmin),
        "Fmin_matches_paper": bool(paper_Fmin),
        "passed": bool(correct_F0 and correct_Fmin and not paper_Fmin),
        "notes": "F_min = -1/3, NOT -1. Paper is wrong."
    }


def test_continuum_limit(deltas, a=1.0):
    """Test 8: Moment matrix and continuum limit normalization."""
    M = np.zeros((3, 3))
    for d in deltas:
        M += np.outer(d, d)

    expected_diag = 4 * a**2
    is_diagonal = np.allclose(M - np.diag(np.diag(M)), 0, atol=1e-12)
    diag_correct = np.allclose(np.diag(M), expected_diag, rtol=1e-10)

    # The discrete Laplacian eigenvalue in small-k limit:
    # λ(k) ≈ -(1/(2a²)) Σ_j (k·δ_j)² = -(1/(2a²)) k^T M k = -(4a²/(2a²)) k² = -2k²
    # But continuum Laplacian gives -k². So discrete = 2× continuum.
    normalization_factor = np.diag(M)[0] / (2 * a**2)

    return {
        "name": "Continuum limit normalization",
        "moment_matrix_diagonal": bool(is_diagonal),
        "M_diag_value": float(np.diag(M)[0]),
        "M_diag_expected": float(expected_diag),
        "diag_correct": bool(diag_correct),
        "normalization_factor": float(normalization_factor),
        "laplacian_is_2x_continuum": bool(abs(normalization_factor - 2.0) < 1e-10),
        "passed": bool(is_diagonal and diag_correct),
        "notes": "Discrete Laplacian = 2× continuum Laplacian. "
                 "Properly normalized R_max = (spectral_radius)/2."
    }


def test_kretschmann_schwarzschild(a_lp=A_OVER_LP):
    """Test 9: Kretschmann scalar from Schwarzschild at r = a."""
    # K = 48G²M²/r⁶ in SI, or K = 48M²/r⁶ in natural units (G=1)
    # At r = a, M_max = a/2 (Schwarzschild condition r_s = 2M = a → M = a/2)
    # K = 48 × (a/2)² / a⁶ = 48 × a²/4 / a⁶ = 12/a⁴

    K_schwarzschild = 12.0  # in units of 1/a⁴
    K_claimed = 320.0       # paper's claimed upper bound
    ratio = K_claimed / K_schwarzschild

    # In units of 1/ℓ_P⁴
    K_schwarz_lp4 = K_schwarzschild / A_SQUARED_OVER_LP2**2
    K_claimed_lp4 = K_claimed / A_SQUARED_OVER_LP2**2

    return {
        "name": "Kretschmann scalar (Schwarzschild derivation)",
        "K_schwarzschild_a4": float(K_schwarzschild),
        "K_paper_upper_bound_a4": float(K_claimed),
        "ratio_paper_to_schwarzschild": float(ratio),
        "K_schwarzschild_lp4": float(K_schwarz_lp4),
        "K_paper_lp4": float(K_claimed_lp4),
        "passed": True,  # Schwarzschild algebra is correct
        "notes": f"Schwarzschild K = 12/a⁴ is correct. "
                 f"Paper's jump to 320/a⁴ (factor {ratio:.1f}×) is unjustified."
    }


def test_minimum_trapped_surface():
    """Test 10: Minimum trapped surface area consistency."""
    a_sq = A_SQUARED_OVER_LP2  # a² in ℓ_P²

    # FCC nn distance = a, so triangle side = √2 a (in FCC, nn vectors have length a,
    # but the edge of the tetrahedron connecting two nn sites has length √2 a... wait.
    # Actually, in the FCC lattice, the nn distance IS a (the length of each δ_j).
    # The edge length of the tetrahedron formed by 4 nn sites:
    # Take 4 nn vectors, e.g. (1,1,0), (1,-1,0), (1,0,1), (1,0,-1) × a/√2
    # Distance between first two: |(0,2,0)|×a/√2 = 2a/√2 = √2 a
    # So tetrahedron edge = √2 a (this is the distance between two nn vectors)

    # The paper says triangle side = √2 a
    triangle_side = np.sqrt(2)  # in units of a
    triangle_area = SQRT3 / 4 * triangle_side**2  # = √3/2 (in units of a²)

    # Minimum closed surface = tetrahedron = 4 equilateral triangles
    tetrahedron_area = 4 * triangle_area  # = 2√3 a²

    # Paper's claimed minimum
    paper_A_min = SQRT3  # √3 a² (in units of a²)

    # Convert to ℓ_P²
    tetrahedron_lp2 = tetrahedron_area * a_sq
    paper_lp2 = paper_A_min * a_sq

    # BH entropy minimum: A ≥ 4ln(3) ℓ_P² for 1 bit
    entropy_min = 4 * LN3  # ≈ 4.39 ℓ_P²

    inconsistent = paper_A_min < tetrahedron_area

    return {
        "name": "Minimum trapped surface area",
        "triangle_area_a2": float(triangle_area),
        "tetrahedron_area_a2": float(tetrahedron_area),
        "paper_A_min_a2": float(paper_A_min),
        "tetrahedron_area_lp2": float(tetrahedron_lp2),
        "paper_A_min_lp2": float(paper_lp2),
        "entropy_minimum_lp2": float(entropy_min),
        "internally_inconsistent": bool(inconsistent),
        "A_min_exceeds_entropy_bound": bool(paper_lp2 > entropy_min),
        "passed": not bool(inconsistent),
        "notes": f"Paper claims A_min = √3 a² = {paper_lp2:.2f} ℓ_P² but derives "
                 f"minimum closed surface = 2√3 a² = {tetrahedron_lp2:.2f} ℓ_P². "
                 f"The claimed minimum is LESS than the derived geometric minimum."
    }


def test_anisotropy(deltas, a=1.0):
    """Test 11: Lorentz invariance — anisotropy at O(k⁴)."""
    # The O(k⁴) tensor is C_{abcd} = (1/24) Σ_j δ_j^a δ_j^b δ_j^c δ_j^d
    # For cubic symmetry, only C_{aaaa} and C_{aabb} are nonzero.
    C4 = np.zeros((3, 3, 3, 3))
    for d in deltas:
        for a_idx in range(3):
            for b_idx in range(3):
                for c_idx in range(3):
                    for d_idx in range(3):
                        C4[a_idx, b_idx, c_idx, d_idx] += (
                            d[a_idx] * d[b_idx] * d[c_idx] * d[d_idx]
                        )
    C4 /= 24.0  # Normalization from Taylor expansion

    # For an isotropic lattice, C_{abcd} ∝ δ_{ab}δ_{cd} + δ_{ac}δ_{bd} + δ_{ad}δ_{bc}
    # The anisotropy is measured by the deviation
    C_aaaa = C4[0, 0, 0, 0]  # = C_xxxx
    C_aabb = C4[0, 0, 1, 1]  # = C_xxyy

    # For isotropic: C_aaaa = 3 C_aabb
    # Anisotropy parameter: η = C_aaaa / C_aabb - 3
    if abs(C_aabb) > 1e-15:
        eta = C_aaaa / C_aabb - 3
    else:
        eta = float('inf')

    # Check dispersion along different directions
    k_mag = 0.1 / a  # Small k for expansion
    directions = {
        "[100]": np.array([1, 0, 0]),
        "[110]": np.array([1, 1, 0]) / np.sqrt(2),
        "[111]": np.array([1, 1, 1]) / np.sqrt(3),
    }
    dispersion = {}
    for name, n_hat in directions.items():
        k = k_mag * n_hat
        lam = eigenvalue_direct(k, deltas, a)
        # Compare to isotropic: λ = -2k² (from moment matrix)
        lam_iso = -2 * k_mag**2
        dispersion[name] = {
            "lambda": float(lam),
            "lambda_isotropic": float(lam_iso),
            "relative_deviation": float(abs(lam - lam_iso) / abs(lam_iso))
        }

    return {
        "name": "Anisotropy / Lorentz invariance",
        "C_aaaa": float(C_aaaa),
        "C_aabb": float(C_aabb),
        "anisotropy_eta": float(eta),
        "is_isotropic_at_O_k2": bool(abs(eta) < 1e-6) if abs(C_aabb) > 1e-15 else False,
        "dispersion_by_direction": dispersion,
        "passed": True,  # Informational test
        "notes": "FCC lattice IS isotropic at O(k²). "
                 f"Anisotropy η = {eta:.4f} enters at O(k⁴). "
                 "At E ~ TeV, corrections ~ (E/E_P)² ~ 10⁻³⁰."
    }


def test_r_max_corrected():
    """Test 12: Compute corrected R_max values."""
    a_sq = A_SQUARED_OVER_LP2

    R_paper = 24 / a_sq
    R_corrected_spectral = 16 / a_sq
    R_corrected_normalized = 8 / a_sq

    # LQG comparison
    gamma_old = 0.274
    gamma_new = 0.2375
    R_lqg_old = 1 / gamma_old**2
    R_lqg_new = 1 / gamma_new**2

    return {
        "name": "R_max corrected values",
        "a_squared_lp2": float(a_sq),
        "a_over_lp": float(np.sqrt(a_sq)),
        "R_max_paper_lp2": float(R_paper),
        "R_max_corrected_spectral_lp2": float(R_corrected_spectral),
        "R_max_corrected_normalized_lp2": float(R_corrected_normalized),
        "R_lqg_gamma_0274": float(R_lqg_old),
        "R_lqg_gamma_02375": float(R_lqg_new),
        "passed": True,  # Informational
        "notes": f"Paper: {R_paper:.3f}/ℓ_P², "
                 f"Corrected (spectral only): {R_corrected_spectral:.3f}/ℓ_P², "
                 f"Corrected (+ normalization): {R_corrected_normalized:.3f}/ℓ_P²"
    }


def test_all_cosines_impossible():
    """Test 13: Prove that all 12 cosines CANNOT simultaneously equal -1."""
    # If all cos(k·δ_j) = -1, need k·δ_j = (2n_j + 1)π for all j.
    # Take the xy-group: δ = (a/√2)(±1, ±1, 0)
    # k·δ₁ = (a/√2)(k_x + k_y) = (2n₁+1)π
    # k·δ₂ = (a/√2)(k_x - k_y) = (2n₂+1)π
    # k·δ₃ = (a/√2)(-k_x + k_y) = (2n₃+1)π
    # k·δ₄ = (a/√2)(-k_x - k_y) = (2n₄+1)π
    #
    # From δ₁ + δ₄: 0 = (2n₁+1+2n₄+1)π → n₁ + n₄ = -1
    # From δ₁: k_x + k_y = (2n₁+1)π√2/a (always odd multiple of π√2/a)
    # From δ₂: k_x - k_y = (2n₂+1)π√2/a
    # Adding: 2k_x = (2n₁+2n₂+2)π√2/a → k_x = (n₁+n₂+1)π√2/a
    # Similarly from xz-group: k_x + k_z = (2m₁+1)π√2/a, k_x - k_z = (2m₂+1)π√2/a
    # Adding: k_x = (m₁+m₂+1)π√2/a
    # These must be compatible, and they are (same form).
    # But now check: from xy-group, k_y = k_x - (2n₂+1)π√2/a = [(n₁+n₂+1) - (2n₂+1)]π√2/a
    #   = (n₁ - n₂)π√2/a
    # From yz-group: δ = (a/√2)(0, ±1, ±1)
    # k·δ = (a/√2)(k_y ± k_z) must be odd π.
    # k_y + k_z = (n₁-n₂)π√2/a + k_z ... this gets complicated.
    # Let's just verify numerically.

    a = 1.0
    deltas = get_fcc_nn_vectors(a)

    # Try to find k where all 12 cos(k·δ_j) = -1
    # Objective: maximize number of cos terms that equal -1
    def count_minus_ones(k, tol=0.01):
        return sum(1 for d in deltas if abs(np.cos(np.dot(k, d)) + 1) < tol)

    # Exhaustive search
    max_count = 0
    best_k = None
    N = 200
    for i1 in range(N):
        for i2 in range(N):
            for i3 in range(N):
                k = np.array([i1, i2, i3]) * 2 * np.pi * np.sqrt(2) / (N * a)
                count = count_minus_ones(k)
                if count > max_count:
                    max_count = count
                    best_k = k.copy()

    return {
        "name": "All 12 cosines = -1 impossibility",
        "max_simultaneous_minus_ones": int(max_count),
        "out_of": 12,
        "all_12_possible": bool(max_count == 12),
        "passed": bool(max_count < 12),
        "notes": f"Maximum {max_count}/12 cosines can simultaneously equal -1. "
                 f"Paper incorrectly claims all 12 can."
    }


# ==============================================================================
# PLOTTING
# ==============================================================================

def generate_plots(deltas, a=1.0):
    """Generate verification plots."""
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
    except ImportError:
        print("  matplotlib not available, skipping plots")
        return []

    plots_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                             "plots")
    os.makedirs(plots_dir, exist_ok=True)
    plot_files = []

    # ---- Plot 1: Eigenvalue along high-symmetry path ----
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))

    factor = np.pi * np.sqrt(2) / a

    # High-symmetry path: Γ → X → W → L → Γ → K
    segments = [
        ("Γ", "X", np.array([0, 0, 0]), np.array([1, 0, 0]) * factor),
        ("X", "W", np.array([1, 0, 0]) * factor, np.array([1, 0.5, 0]) * factor),
        ("W", "L", np.array([1, 0.5, 0]) * factor, np.array([0.5, 0.5, 0.5]) * factor),
        ("L", "Γ", np.array([0.5, 0.5, 0.5]) * factor, np.array([0, 0, 0])),
        ("Γ", "K", np.array([0, 0, 0]), np.array([0.75, 0.75, 0]) * factor),
    ]

    all_t = []
    all_lam = []
    all_F = []
    tick_positions = [0]
    tick_labels = ["Γ"]
    cumulative_t = 0

    for name1, name2, k_start, k_end in segments:
        n_pts = 100
        for i in range(n_pts):
            frac = i / n_pts
            k = k_start + frac * (k_end - k_start)
            lam = eigenvalue_direct(k, deltas, a)
            F = form_factor(k, deltas)
            all_t.append(cumulative_t + frac)
            all_lam.append(lam)
            all_F.append(F)
        cumulative_t += 1
        tick_positions.append(cumulative_t)
        tick_labels.append(name2)

    # Plot eigenvalue
    ax1.plot(all_t, all_lam, 'b-', linewidth=1.5)
    ax1.axhline(y=-24, color='r', linestyle='--', linewidth=1, alpha=0.7, label='Paper claim: -24/a²')
    ax1.axhline(y=-16, color='g', linestyle='--', linewidth=1, alpha=0.7, label='True bound: -16/a²')
    ax1.axhline(y=0, color='k', linestyle='-', linewidth=0.5, alpha=0.3)
    for tp in tick_positions:
        ax1.axvline(x=tp, color='k', linestyle='-', linewidth=0.3, alpha=0.3)
    ax1.set_xticks(tick_positions)
    ax1.set_xticklabels(tick_labels)
    ax1.set_ylabel('λ(k) × a²')
    ax1.set_title('FCC Discrete Laplacian Eigenvalue Along High-Symmetry Path')
    ax1.legend(loc='lower left')
    ax1.set_ylim(-28, 4)

    # Plot form factor
    ax2.plot(all_t, all_F, 'b-', linewidth=1.5)
    ax2.axhline(y=-1, color='r', linestyle='--', linewidth=1, alpha=0.7, label='Paper claim: F_min = -1')
    ax2.axhline(y=-1/3, color='g', linestyle='--', linewidth=1, alpha=0.7, label='True F_min = -1/3')
    ax2.axhline(y=0, color='k', linestyle='-', linewidth=0.5, alpha=0.3)
    for tp in tick_positions:
        ax2.axvline(x=tp, color='k', linestyle='-', linewidth=0.3, alpha=0.3)
    ax2.set_xticks(tick_positions)
    ax2.set_xticklabels(tick_labels)
    ax2.set_ylabel('F(k)')
    ax2.set_title('FCC Lattice Form Factor Along High-Symmetry Path')
    ax2.legend(loc='lower left')
    ax2.set_ylim(-1.2, 1.2)

    plt.tight_layout()
    path1 = os.path.join(plots_dir, "lemma_5_4_1a_eigenvalue_form_factor.png")
    plt.savefig(path1, dpi=150, bbox_inches='tight')
    plt.close()
    plot_files.append(path1)

    # ---- Plot 2: 2D slice of |λ(k)| showing the maximum ----
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.5))

    N = 200
    for idx, (k_fixed_label, k_fixed_idx) in enumerate([("k_z=0", 2), ("k_y=0", 1), ("k_x=0", 0)]):
        k_range = np.linspace(-np.pi * np.sqrt(2) / a, np.pi * np.sqrt(2) / a, N)
        lam_grid = np.zeros((N, N))

        for i, ki in enumerate(k_range):
            for j, kj in enumerate(k_range):
                k = np.zeros(3)
                if k_fixed_idx == 2:
                    k[0], k[1] = ki, kj
                elif k_fixed_idx == 1:
                    k[0], k[2] = ki, kj
                else:
                    k[1], k[2] = ki, kj
                lam_grid[j, i] = abs(eigenvalue_direct(k, deltas, a))

        ax = axes[idx]
        im = ax.pcolormesh(k_range * a / np.sqrt(2) / np.pi,
                           k_range * a / np.sqrt(2) / np.pi,
                           lam_grid, cmap='hot', vmin=0, vmax=24)
        ax.set_title(f'{k_fixed_label} plane')
        ax.set_aspect('equal')
        if k_fixed_idx == 2:
            ax.set_xlabel('k_x a/(√2 π)')
            ax.set_ylabel('k_y a/(√2 π)')
        elif k_fixed_idx == 1:
            ax.set_xlabel('k_x a/(√2 π)')
            ax.set_ylabel('k_z a/(√2 π)')
        else:
            ax.set_xlabel('k_y a/(√2 π)')
            ax.set_ylabel('k_z a/(√2 π)')
        # Mark the max value
        max_val = np.max(lam_grid)
        ax.text(0.02, 0.98, f'max = {max_val:.1f}/a²',
                transform=ax.transAxes, fontsize=9,
                verticalalignment='top', color='white',
                bbox=dict(boxstyle='round', facecolor='black', alpha=0.5))

    fig.colorbar(im, ax=axes, label='|λ(k)| × a²', shrink=0.8)
    fig.suptitle('|λ(k)| on FCC Lattice — Maximum is 16/a² (NOT 24/a²)', fontsize=12, fontweight='bold')
    plt.tight_layout()
    path2 = os.path.join(plots_dir, "lemma_5_4_1a_eigenvalue_2d_slices.png")
    plt.savefig(path2, dpi=150, bbox_inches='tight')
    plt.close()
    plot_files.append(path2)

    # ---- Plot 3: Comparison bar chart ----
    fig, ax = plt.subplots(figsize=(8, 5))

    labels = ['Paper\n(24/a²)', 'Corrected\n(spectral)\n(16/a²)',
              'Corrected\n(+norm)\n(8/a²)', 'LQG\n(γ=0.274)', 'LQG\n(γ=0.2375)']
    values = [24 / A_SQUARED_OVER_LP2, 16 / A_SQUARED_OVER_LP2,
              8 / A_SQUARED_OVER_LP2, 1 / 0.274**2, 1 / 0.2375**2]
    colors = ['red', 'green', 'blue', 'orange', 'darkorange']

    bars = ax.bar(labels, values, color=colors, alpha=0.7, edgecolor='black')

    for bar, val in zip(bars, values):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.2,
                f'{val:.2f}', ha='center', va='bottom', fontsize=10, fontweight='bold')

    ax.set_ylabel('R_max (in units of 1/ℓ_P²)')
    ax.set_title('Maximum Curvature Bound: Paper vs Corrected vs LQG')
    ax.axhline(y=1, color='gray', linestyle=':', linewidth=0.5, alpha=0.5)

    plt.tight_layout()
    path3 = os.path.join(plots_dir, "lemma_5_4_1a_rmax_comparison.png")
    plt.savefig(path3, dpi=150, bbox_inches='tight')
    plt.close()
    plot_files.append(path3)

    # ---- Plot 4: Trapped surface area comparison ----
    fig, ax = plt.subplots(figsize=(7, 5))

    a_sq = A_SQUARED_OVER_LP2
    areas = {
        'Single\ntriangle': SQRT3 / 2 * a_sq,
        'Paper\nA_min': SQRT3 * a_sq,
        'Min closed\nsurface\n(tetrahedron)': 2 * SQRT3 * a_sq,
        'Entropy\nminimum\n(4 ln 3)': 4 * LN3,
    }

    colors_trap = ['lightblue', 'red', 'green', 'orange']
    bars = ax.bar(areas.keys(), areas.values(), color=colors_trap, alpha=0.7, edgecolor='black')

    for bar, val in zip(bars, areas.values()):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.2,
                f'{val:.2f}', ha='center', va='bottom', fontsize=10, fontweight='bold')

    ax.set_ylabel('Area (in units of ℓ_P²)')
    ax.set_title('Minimum Trapped Surface Area: Internal Inconsistency')
    ax.axhline(y=SQRT3 * a_sq, color='red', linestyle='--', linewidth=1, alpha=0.5)
    ax.axhline(y=2 * SQRT3 * a_sq, color='green', linestyle='--', linewidth=1, alpha=0.5)

    # Annotate the problem
    ax.annotate('Paper claim < min closed surface!',
                xy=(1, SQRT3 * a_sq), xytext=(1.5, 14),
                arrowprops=dict(arrowstyle='->', color='red'),
                fontsize=10, color='red', fontweight='bold')

    plt.tight_layout()
    path4 = os.path.join(plots_dir, "lemma_5_4_1a_trapped_surface.png")
    plt.savefig(path4, dpi=150, bbox_inches='tight')
    plt.close()
    plot_files.append(path4)

    return plot_files


# ==============================================================================
# MAIN EXECUTION
# ==============================================================================

def main():
    a = 1.0
    deltas = get_fcc_nn_vectors(a)

    results = {
        "theorem": "Lemma 5.4.1a",
        "title": "Maximum Curvature Bound from FCC Lattice",
        "timestamp": datetime.now().isoformat(),
        "verifications": []
    }

    print("=" * 72)
    print("LEMMA 5.4.1a: ADVERSARIAL PHYSICS VERIFICATION")
    print("Maximum Curvature Bound from FCC Lattice")
    print("=" * 72)

    # Run all tests
    tests = [
        ("Test 1", test_nn_vectors, (deltas, a)),
        ("Test 2", test_factorization_identity, (deltas, a)),
        ("Test 3", test_spectral_radius_analytic, ()),
        ("Test 4", test_spectral_radius_brute_force, (deltas, a, 150)),
        ("Test 5", test_spectral_radius_scipy, (deltas, a, 500)),
        ("Test 6", test_high_symmetry_points, (deltas, a)),
        ("Test 7", test_form_factor_range, (deltas, a, 100)),
        ("Test 8", test_continuum_limit, (deltas, a)),
        ("Test 9", test_kretschmann_schwarzschild, ()),
        ("Test 10", test_minimum_trapped_surface, ()),
        ("Test 11", test_anisotropy, (deltas, a)),
        ("Test 12", test_r_max_corrected, ()),
        ("Test 13", test_all_cosines_impossible, ()),
    ]

    for label, func, args in tests:
        print(f"\n{'─' * 72}")
        print(f"  {label}: {func.__doc__.strip().split(chr(10))[0]}")
        print(f"{'─' * 72}")
        result = func(*args)
        results["verifications"].append(result)

        status = "✅ PASS" if result.get("passed", True) else "❌ FAIL"
        print(f"  Status: {status}")
        print(f"  Notes: {result.get('notes', 'N/A')}")

        # Print key values
        for key, val in result.items():
            if key in ("name", "passed", "notes", "corner_details",
                       "dispersion_by_direction", "points"):
                continue
            if isinstance(val, (int, float)):
                print(f"    {key}: {val}")
            elif isinstance(val, bool):
                print(f"    {key}: {val}")

    # Summary
    n_passed = sum(1 for v in results["verifications"] if v.get("passed", True))
    n_total = len(results["verifications"])
    n_failed = n_total - n_passed

    results["summary"] = {
        "total_tests": n_total,
        "passed": n_passed,
        "failed": n_failed,
        "critical_findings": [
            "Spectral radius is 16/a², NOT 24/a² (paper is wrong by factor 3/2)",
            "Form factor minimum is -1/3, NOT -1 (paper is wrong)",
            "Minimum trapped surface area is internally inconsistent",
            "Discrete Laplacian = 2× continuum Laplacian (systematic factor of 2)"
        ],
        "qualitative_conclusion_valid": True,
        "quantitative_corrections_needed": True,
        "overall_status": "CORRECTIONS NEEDED"
    }

    print(f"\n{'=' * 72}")
    print("SUMMARY")
    print(f"{'=' * 72}")
    print(f"  Tests: {n_passed}/{n_total} passed, {n_failed} failed")
    print(f"\n  CRITICAL FINDINGS:")
    for finding in results["summary"]["critical_findings"]:
        print(f"    ⚠️  {finding}")
    print(f"\n  Qualitative conclusion (R_max ~ O(1/ℓ_P²)): VALID")
    print(f"  Quantitative corrections needed: YES")
    print(f"{'=' * 72}")

    # Generate plots
    print("\nGenerating plots...")
    plot_files = generate_plots(deltas, a)
    results["plots"] = plot_files
    for pf in plot_files:
        print(f"  Saved: {pf}")

    # Save results
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_path = os.path.join(script_dir, "lemma_5_4_1a_adversarial_results.json")

    def make_serializable(obj):
        if isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        if isinstance(obj, np.floating):
            return float(obj)
        if isinstance(obj, np.integer):
            return int(obj)
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        if isinstance(obj, dict):
            return {k: make_serializable(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [make_serializable(v) for v in obj]
        return obj

    with open(output_path, 'w') as f:
        json.dump(make_serializable(results), f, indent=2)
    print(f"\nResults saved to: {output_path}")


if __name__ == "__main__":
    main()
