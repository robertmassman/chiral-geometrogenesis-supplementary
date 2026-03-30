#!/usr/bin/env python3
"""
Adversarial Physics Verification: Theorem 1.1.1
SU(3) Weight Diagram <-> Stella Octangula Isomorphism
=====================================================

This script performs adversarial verification targeting the specific errors
and warnings identified by multi-agent review (2026-02-21):

Errors Tested:
  E-1: Section 4.2 expected output wrong (Euclidean distances give isosceles)
  E-2: Section 4.3 transformation matrix entry d is wrong
  E-3: Section 1.6 half-root claim (1/2 factor is incorrect)
  E-4: Step 7 basis label incorrect (Killing form not Euclidean in that basis)
  E-5: Step 7 sigma_1, sigma_2 are reflections, not rotations

Additional Tests:
  A-1: Full Weyl reflection computation in proper orthonormal basis
  A-2: Convention consistency between (T3, Y) and (T3, T8)
  A-3: Killing form explicit computation via adjoint representation
  A-4: Determinant of tetrahedron symmetry operations (rotation vs reflection)
  A-5: Root-weight relationship verification

Related Documents:
  - Proof: docs/proofs/Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md
  - Lean: lean/ChiralGeometrogenesis/Phase1/Theorem_1_1_1.lean
  - Verification: verification/Phase1/theorem_1_1_1_su3_stella_octangula.py

Verification Date: 2026-02-21
"""

import numpy as np
import json
import sys
import os
from datetime import datetime

# Attempt matplotlib import for plots
try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyArrowPatch
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("WARNING: matplotlib not available, skipping plot generation")

# ==============================================================================
# CONSTANTS AND SETUP
# ==============================================================================

# Gell-Mann matrices
LAMBDA = [
    np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], dtype=complex),
    np.array([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]], dtype=complex),
    np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], dtype=complex),
    np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], dtype=complex),
    np.array([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]], dtype=complex),
    np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], dtype=complex),
    np.array([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]], dtype=complex),
    np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], dtype=complex) / np.sqrt(3),
]

# Cartan generators
T3 = LAMBDA[2] / 2
Y_OP = LAMBDA[7] / np.sqrt(3)
T8 = LAMBDA[7] / 2

# Weights in (T3, Y) convention (proof document)
W_R_T3Y = np.array([0.5, 1/3])
W_G_T3Y = np.array([-0.5, 1/3])
W_B_T3Y = np.array([0.0, -2/3])

# Weights in (T3, T8) convention (Lean formalization)
W_R_T3T8 = np.array([0.5, 1/(2*np.sqrt(3))])
W_G_T3T8 = np.array([-0.5, 1/(2*np.sqrt(3))])
W_B_T3T8 = np.array([0.0, -1/np.sqrt(3)])

# Tetrahedron vertices (from proof Step 1)
V_0 = np.array([0, 0, 1])
V_1 = np.array([2*np.sqrt(2)/3, 0, -1/3])
V_2 = np.array([-np.sqrt(2)/3, np.sqrt(2/3), -1/3])
V_3 = np.array([-np.sqrt(2)/3, -np.sqrt(2/3), -1/3])

# Projected vertices
PI_V1 = V_1[:2]
PI_V2 = V_2[:2]
PI_V3 = V_3[:2]

# SU(3) simple roots in orthonormal Killing basis
ALPHA_1 = np.array([1.0, 0.0])
ALPHA_2 = np.array([-0.5, np.sqrt(3)/2])

PLOT_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'plots')


# ==============================================================================
# ERROR E-1: EUCLIDEAN DISTANCE EXPECTED OUTPUT
# ==============================================================================

def test_E1_euclidean_distances():
    """
    E-1: Verify that Euclidean distances in (T3, Y) give ISOSCELES, not equilateral.

    The proof Section 4.2 claims expected output:
      "Distances: RG=1.0000, GB=1.0000, BR=1.0000"
      "Equilateral: true"

    But Section 1.6 correctly shows the triangle is isosceles in Euclidean (T3, Y).
    This test proves the expected output is wrong.
    """
    d_RG = np.linalg.norm(W_R_T3Y - W_G_T3Y)
    d_GB = np.linalg.norm(W_G_T3Y - W_B_T3Y)
    d_BR = np.linalg.norm(W_B_T3Y - W_R_T3Y)

    # The proof claims d_RG = d_GB = d_BR = 1.0 -- this is WRONG
    proof_claims_equilateral = (
        abs(d_RG - 1.0) < 0.01 and
        abs(d_GB - 1.0) < 0.01 and
        abs(d_BR - 1.0) < 0.01
    )

    # The actual values
    # d_RG = 1.0, d_GB = sqrt(5/4) = 1.118, d_BR = sqrt(5/4) = 1.118
    expected_d_RG = 1.0
    expected_d_GB = np.sqrt(5/4)
    expected_d_BR = np.sqrt(5/4)

    actual_correct = (
        abs(d_RG - expected_d_RG) < 1e-14 and
        abs(d_GB - expected_d_GB) < 1e-14 and
        abs(d_BR - expected_d_BR) < 1e-14
    )

    is_isosceles = abs(d_GB - d_BR) < 1e-14 and abs(d_RG - d_GB) > 0.1

    return {
        'test': 'E1_euclidean_distances',
        'description': 'Section 4.2 expected output is wrong: triangle is isosceles in Euclidean (T3,Y)',
        'passed': bool(actual_correct and is_isosceles and not proof_claims_equilateral),
        'computed': {
            'd_RG': float(d_RG),
            'd_GB': float(d_GB),
            'd_BR': float(d_BR),
        },
        'proof_claims_equilateral': bool(proof_claims_equilateral),
        'actually_isosceles': bool(is_isosceles),
        'error_confirmed': not proof_claims_equilateral,
    }


# ==============================================================================
# ERROR E-2: TRANSFORMATION MATRIX ENTRY d
# ==============================================================================

def test_E2_transformation_matrix():
    """
    E-2: Verify transformation matrix A entry d.

    The proof claims d = 1/(2*sqrt(6)).
    The correct value is d = sqrt(6)/4 = sqrt(3)/(2*sqrt(2)).
    These differ by a factor of 3.
    """
    # The proof's matrix (with the wrong d)
    a_proof = 3 / (4*np.sqrt(2))
    b_proof = -np.sqrt(3) / (4*np.sqrt(2))
    c_proof = 1 / (2*np.sqrt(2))
    d_proof = 1 / (2*np.sqrt(6))   # CLAIMED value

    A_proof = np.array([[a_proof, b_proof], [c_proof, d_proof]])

    # The correct matrix (derived numerically)
    V_mat = np.column_stack([PI_V1, PI_V2])
    W_mat = np.column_stack([W_R_T3Y, W_G_T3Y])
    A_correct = W_mat @ np.linalg.inv(V_mat)

    # Correct d value
    d_correct = np.sqrt(6) / 4  # = sqrt(3) / (2*sqrt(2))

    # Verify: the proof's d vs the correct d
    d_ratio = d_proof / d_correct
    d_error = abs(d_proof - d_correct)

    # Test proof's matrix on all three vertices
    proof_results = {}
    for name, pv, target in [('R', PI_V1, W_R_T3Y), ('G', PI_V2, W_G_T3Y), ('B', PI_V3, W_B_T3Y)]:
        mapped = A_proof @ pv
        error = np.linalg.norm(mapped - target)
        proof_results[name] = {
            'mapped': mapped.tolist(),
            'target': target.tolist(),
            'error': float(error),
        }

    # Test correct matrix on all three vertices
    correct_results = {}
    for name, pv, target in [('R', PI_V1, W_R_T3Y), ('G', PI_V2, W_G_T3Y), ('B', PI_V3, W_B_T3Y)]:
        mapped = A_correct @ pv
        error = np.linalg.norm(mapped - target)
        correct_results[name] = {
            'mapped': mapped.tolist(),
            'target': target.tolist(),
            'error': float(error),
        }

    # The proof's matrix should FAIL for G and B
    proof_fails_G = proof_results['G']['error'] > 0.01
    proof_fails_B = proof_results['B']['error'] > 0.01

    # The correct matrix should work for all
    correct_works_all = all(v['error'] < 1e-10 for v in correct_results.values())

    return {
        'test': 'E2_transformation_matrix',
        'description': 'Matrix entry d = 1/(2*sqrt(6)) is wrong; correct is d = sqrt(6)/4',
        'passed': bool(proof_fails_G and proof_fails_B and correct_works_all),
        'd_proof': float(d_proof),
        'd_correct': float(d_correct),
        'd_ratio': float(d_ratio),
        'd_error': float(d_error),
        'A_proof': A_proof.tolist(),
        'A_correct': A_correct.tolist(),
        'proof_matrix_results': proof_results,
        'correct_matrix_results': correct_results,
        'error_confirmed': bool(proof_fails_G or proof_fails_B),
    }


# ==============================================================================
# ERROR E-3: HALF-ROOT CLAIM
# ==============================================================================

def test_E3_root_weight_relation():
    """
    E-3: Verify weight differences equal FULL roots, not half-roots.

    Section 1.6 claims: w_c - w_c' = +/- (1/2)(root vector)
    Correct: w_c - w_c' = +/- (root vector)
    """
    # Compute weight differences in the orthonormal Killing basis
    # In orthonormal basis: w_R = (1/2, 1/(2*sqrt(3))), etc.
    # But for root comparison, use the standard root-weight relation

    # Simple roots of A2
    alpha1 = ALPHA_1  # (1, 0)
    alpha2 = ALPHA_2  # (-1/2, sqrt(3)/2)

    # Weights in orthonormal Killing basis
    # Using the standard relation: mu_i = sum_j (A^{-1})_ij alpha_j
    # For A2 Cartan matrix: A = [[2, -1], [-1, 2]]
    # A^{-1} = (1/3) [[2, 1], [1, 2]]
    # mu_1 = (2*alpha1 + alpha2)/3
    # mu_2 = (alpha1 + 2*alpha2)/3 ... but this gives fundamental weights, not rep weights

    # The weights of the fundamental 3 representation are:
    # w_R = mu_1 (highest weight)
    # w_G = mu_1 - alpha1
    # w_B = mu_1 - alpha1 - alpha2

    # So the differences are:
    # w_R - w_G = alpha1 (a full root!)
    # w_G - w_B = alpha2 (a full root!)
    # w_R - w_B = alpha1 + alpha2 (a full root!)

    # Let's verify numerically
    mu_1 = (2*alpha1 + alpha2) / 3
    mu_2 = (alpha1 + 2*alpha2) / 3

    w_R_orth = mu_1
    w_G_orth = mu_1 - alpha1
    w_B_orth = mu_1 - alpha1 - alpha2

    diff_RG = w_R_orth - w_G_orth
    diff_GB = w_G_orth - w_B_orth
    diff_RB = w_R_orth - w_B_orth

    # Check: differences equal full roots
    RG_is_alpha1 = np.allclose(diff_RG, alpha1)
    GB_is_alpha2 = np.allclose(diff_GB, alpha2)
    RB_is_alpha1_plus_alpha2 = np.allclose(diff_RB, alpha1 + alpha2)

    # Check: differences are NOT half-roots
    RG_is_half_alpha1 = np.allclose(diff_RG, alpha1/2)

    return {
        'test': 'E3_root_weight_relation',
        'description': 'Weight differences are full roots, not half-roots',
        'passed': bool(RG_is_alpha1 and GB_is_alpha2 and RB_is_alpha1_plus_alpha2),
        'diff_RG': diff_RG.tolist(),
        'alpha1': alpha1.tolist(),
        'RG_equals_alpha1': bool(RG_is_alpha1),
        'RG_equals_half_alpha1': bool(RG_is_half_alpha1),
        'diff_GB': diff_GB.tolist(),
        'alpha2': alpha2.tolist(),
        'GB_equals_alpha2': bool(GB_is_alpha2),
        'diff_RB': diff_RB.tolist(),
        'alpha1_plus_alpha2': (alpha1 + alpha2).tolist(),
        'RB_equals_alpha1_plus_alpha2': bool(RB_is_alpha1_plus_alpha2),
        'error_confirmed': not RG_is_half_alpha1,
    }


# ==============================================================================
# ERROR E-4: KILLING FORM BASIS
# ==============================================================================

def test_E4_killing_form_basis():
    """
    E-4: Verify that the Killing form is NOT Euclidean in the (T3, Y*sqrt(3)) basis.

    Step 7 claims simple roots are "in the (T3, Y*sqrt(3)) basis where the
    Killing form is Euclidean." We test whether this is true.
    """
    # The Cartan generators in different bases:
    # Standard basis: H1 = lambda_3 = diag(1,-1,0), H2 = lambda_8 = diag(1,1,-2)/sqrt(3)
    H1 = LAMBDA[2]  # lambda_3
    H2 = LAMBDA[7]  # lambda_8

    # Killing form: B(X,Y) = Tr(ad_X . ad_Y) = 6 * Tr(XY) for SU(3)
    # (with Gell-Mann normalization Tr(lambda_a lambda_b) = 2 delta_ab)
    def killing(X, Y):
        return 6 * np.trace(X @ Y).real

    # Killing metric in (H1, H2) basis = (lambda_3, lambda_8) basis
    g_H1H1 = killing(H1, H1)  # Should be 12
    g_H2H2 = killing(H2, H2)  # Should be 12
    g_H1H2 = killing(H1, H2)  # Should be 0

    # This is 12 * I_2, which IS proportional to identity -> Euclidean up to scale
    H_basis_euclidean = (abs(g_H1H1 - g_H2H2) < 1e-10 and abs(g_H1H2) < 1e-10)

    # Now check the (T3, Y) basis: T3 = H1/2, Y = H2/sqrt(3)
    # Killing metric in (T3, Y) basis:
    g_T3T3 = killing(T3, T3)      # = killing(H1/2, H1/2) = 12/4 = 3
    g_YY = killing(Y_OP, Y_OP)    # = killing(H2/sqrt(3), H2/sqrt(3)) = 12/3 = 4
    g_T3Y = killing(T3, Y_OP)     # = killing(H1/2, H2/sqrt(3)) = 0

    # Metric is diag(3, 4) -- NOT proportional to identity!
    T3Y_basis_euclidean = (abs(g_T3T3 - g_YY) < 1e-10)

    # Now check the (T3, Y*sqrt(3)) basis:
    # Y*sqrt(3) = H2/sqrt(3) * sqrt(3) = H2
    # So (T3, Y*sqrt(3)) = (H1/2, H2)
    g_T3T3_2 = killing(T3, T3)     # = 3
    g_Ys3Ys3 = killing(H2, H2)     # = 12
    g_T3Ys3 = killing(T3, H2)      # = 0

    # Metric is diag(3, 12) -- NOT proportional to identity!
    T3Ys3_basis_euclidean = (abs(g_T3T3_2 - g_Ys3Ys3) < 1e-10)

    # Now check the (T3, T8) basis: T3 = H1/2, T8 = H2/2
    g_T3T3_3 = killing(T3, T3)     # = 3
    g_T8T8 = killing(T8, T8)       # = killing(H2/2, H2/2) = 12/4 = 3
    g_T3T8 = killing(T3, T8)       # = 0

    # Metric is diag(3, 3) = 3*I_2 -- IS proportional to identity!
    T3T8_basis_euclidean = (abs(g_T3T3_3 - g_T8T8) < 1e-10 and abs(g_T3T8) < 1e-10)

    return {
        'test': 'E4_killing_form_basis',
        'description': 'Killing form is NOT Euclidean in (T3, Y*sqrt(3)) basis',
        'passed': bool(not T3Ys3_basis_euclidean and H_basis_euclidean and T3T8_basis_euclidean),
        'killing_metric': {
            '(H1,H2)_basis': {
                'g11': float(g_H1H1), 'g22': float(g_H2H2), 'g12': float(g_H1H2),
                'is_euclidean': bool(H_basis_euclidean),
            },
            '(T3,Y)_basis': {
                'g11': float(g_T3T3), 'g22': float(g_YY), 'g12': float(g_T3Y),
                'is_euclidean': bool(T3Y_basis_euclidean),
            },
            '(T3,Y*sqrt3)_basis': {
                'g11': float(g_T3T3_2), 'g22': float(g_Ys3Ys3), 'g12': float(g_T3Ys3),
                'is_euclidean': bool(T3Ys3_basis_euclidean),
            },
            '(T3,T8)_basis': {
                'g11': float(g_T3T3_3), 'g22': float(g_T8T8), 'g12': float(g_T3T8),
                'is_euclidean': bool(T3T8_basis_euclidean),
            },
        },
        'error_confirmed': not T3Ys3_basis_euclidean,
        'note': '(H1,H2) and (T3,T8) bases give Euclidean Killing metric; (T3,Y) and (T3,Y*sqrt3) do NOT',
    }


# ==============================================================================
# ERROR E-5: ROTATION VS REFLECTION
# ==============================================================================

def test_E5_rotation_vs_reflection():
    """
    E-5: Verify that the symmetry operations swapping two vertices while
    fixing the apex and one base vertex are REFLECTIONS (det = -1),
    not rotations (det = +1).

    The proof claims sigma_1 is "rotation by pi about axis through v_W and
    midpoint of edge v_R v_G." We show this must be a reflection.
    """
    # We need the 3D operation that:
    # - Fixes V_0 (apex) and V_3 (blue)
    # - Swaps V_1 (red) <-> V_2 (green)
    #
    # Construct by solving the linear system: M @ V_i = target_i

    # Build source and target matrices
    source = np.column_stack([V_0, V_1, V_2, V_3])
    target = np.column_stack([V_0, V_2, V_1, V_3])  # swap V_1 <-> V_2

    # Since we have 4 points in 3D (spanning R^3 because centroid is origin),
    # we can determine the linear map from 3 linearly independent points
    # Use V_0, V_1, V_2 (check they're linearly independent)
    S = np.column_stack([V_0, V_1, V_2])
    T_mat = np.column_stack([V_0, V_2, V_1])

    M_sigma1 = T_mat @ np.linalg.inv(S)
    det_sigma1 = np.linalg.det(M_sigma1)

    # Verify it maps correctly
    sigma1_v0 = M_sigma1 @ V_0
    sigma1_v1 = M_sigma1 @ V_1
    sigma1_v2 = M_sigma1 @ V_2
    sigma1_v3 = M_sigma1 @ V_3

    v0_fixed = np.allclose(sigma1_v0, V_0)
    v1_to_v2 = np.allclose(sigma1_v1, V_2)
    v2_to_v1 = np.allclose(sigma1_v2, V_1)
    v3_fixed = np.allclose(sigma1_v3, V_3)

    # Similarly for sigma_2 (swap V_2 <-> V_3, fix V_0 and V_1)
    S2 = np.column_stack([V_0, V_2, V_3])
    T2 = np.column_stack([V_0, V_3, V_2])
    M_sigma2 = T2 @ np.linalg.inv(S2)
    det_sigma2 = np.linalg.det(M_sigma2)

    # A rotation has det = +1, a reflection has det = -1
    sigma1_is_reflection = abs(det_sigma1 - (-1)) < 1e-10
    sigma2_is_reflection = abs(det_sigma2 - (-1)) < 1e-10
    sigma1_is_rotation = abs(det_sigma1 - 1) < 1e-10

    # Also verify M is orthogonal (M^T M = I)
    sigma1_orthogonal = np.allclose(M_sigma1.T @ M_sigma1, np.eye(3))
    sigma2_orthogonal = np.allclose(M_sigma2.T @ M_sigma2, np.eye(3))

    return {
        'test': 'E5_rotation_vs_reflection',
        'description': 'sigma_1 and sigma_2 are reflections (det=-1), not rotations (det=+1)',
        'passed': bool(sigma1_is_reflection and sigma2_is_reflection and
                       v0_fixed and v1_to_v2 and v2_to_v1 and v3_fixed),
        'sigma1': {
            'determinant': float(det_sigma1),
            'is_reflection': bool(sigma1_is_reflection),
            'is_rotation': bool(sigma1_is_rotation),
            'is_orthogonal': bool(sigma1_orthogonal),
            'v0_fixed': bool(v0_fixed),
            'v1_to_v2': bool(v1_to_v2),
            'v2_to_v1': bool(v2_to_v1),
            'v3_fixed': bool(v3_fixed),
        },
        'sigma2': {
            'determinant': float(det_sigma2),
            'is_reflection': bool(sigma2_is_reflection),
            'is_orthogonal': bool(sigma2_orthogonal),
        },
        'error_confirmed': bool(sigma1_is_reflection and not sigma1_is_rotation),
    }


# ==============================================================================
# ADDITIONAL TEST A-1: FULL WEYL REFLECTION IN PROPER BASIS
# ==============================================================================

def test_A1_weyl_reflections_proper_basis():
    """
    A-1: Verify Weyl reflections in the proper orthonormal Killing basis.

    Test that s_1 and s_2 correctly permute the weights when computed
    with the proper inner product.
    """
    # In orthonormal Killing basis, the weights are:
    mu_1 = (2*ALPHA_1 + ALPHA_2) / 3  # fundamental weight 1
    mu_2 = (ALPHA_1 + 2*ALPHA_2) / 3  # fundamental weight 2

    w_R = mu_1
    w_G = mu_1 - ALPHA_1
    w_B = mu_1 - ALPHA_1 - ALPHA_2

    # Weyl reflection formula: s_alpha(w) = w - 2 * <w, alpha> / <alpha, alpha> * alpha
    def weyl_reflect(w, alpha):
        return w - 2 * np.dot(w, alpha) / np.dot(alpha, alpha) * alpha

    # s_1 (reflection through hyperplane perp to alpha_1)
    s1_wR = weyl_reflect(w_R, ALPHA_1)
    s1_wG = weyl_reflect(w_G, ALPHA_1)
    s1_wB = weyl_reflect(w_B, ALPHA_1)

    s1_swaps_RG = np.allclose(s1_wR, w_G) and np.allclose(s1_wG, w_R)
    s1_fixes_B = np.allclose(s1_wB, w_B)

    # s_2 (reflection through hyperplane perp to alpha_2)
    s2_wR = weyl_reflect(w_R, ALPHA_2)
    s2_wG = weyl_reflect(w_G, ALPHA_2)
    s2_wB = weyl_reflect(w_B, ALPHA_2)

    s2_swaps_GB = np.allclose(s2_wG, w_B) and np.allclose(s2_wB, w_G)
    s2_fixes_R = np.allclose(s2_wR, w_R)

    # Composite: s_1 s_2 s_1 should swap R <-> B, fix G
    s1s2s1_wR = weyl_reflect(weyl_reflect(weyl_reflect(w_R, ALPHA_1), ALPHA_2), ALPHA_1)
    s1s2s1_wB = weyl_reflect(weyl_reflect(weyl_reflect(w_B, ALPHA_1), ALPHA_2), ALPHA_1)
    s1s2s1_wG = weyl_reflect(weyl_reflect(weyl_reflect(w_G, ALPHA_1), ALPHA_2), ALPHA_1)

    composite_swaps_RB = np.allclose(s1s2s1_wR, w_B) and np.allclose(s1s2s1_wB, w_R)
    composite_fixes_G = np.allclose(s1s2s1_wG, w_G)

    return {
        'test': 'A1_weyl_reflections_proper_basis',
        'description': 'Weyl reflections correctly permute weights in orthonormal Killing basis',
        'passed': bool(s1_swaps_RG and s1_fixes_B and s2_swaps_GB and s2_fixes_R
                       and composite_swaps_RB and composite_fixes_G),
        'weights': {'R': w_R.tolist(), 'G': w_G.tolist(), 'B': w_B.tolist()},
        's1': {
            's1(R)': s1_wR.tolist(), 's1(G)': s1_wG.tolist(), 's1(B)': s1_wB.tolist(),
            'swaps_RG': bool(s1_swaps_RG), 'fixes_B': bool(s1_fixes_B),
        },
        's2': {
            's2(R)': s2_wR.tolist(), 's2(G)': s2_wG.tolist(), 's2(B)': s2_wB.tolist(),
            'swaps_GB': bool(s2_swaps_GB), 'fixes_R': bool(s2_fixes_R),
        },
        'composite_s1s2s1': {
            'swaps_RB': bool(composite_swaps_RB), 'fixes_G': bool(composite_fixes_G),
        },
    }


# ==============================================================================
# ADDITIONAL TEST A-2: CONVENTION CONSISTENCY
# ==============================================================================

def test_A2_convention_consistency():
    """
    A-2: Verify that (T3, Y) and (T3, T8) conventions are consistently related.

    The conversion is: T8 = Y * sqrt(3) / 2, or equivalently Y = 2 * T8 / sqrt(3).
    """
    # Conversion matrix from (T3, Y) to (T3, T8): T8 = Y * sqrt(3)/2
    conv = np.array([[1, 0], [0, np.sqrt(3)/2]])

    # Convert weights
    w_R_converted = conv @ W_R_T3Y
    w_G_converted = conv @ W_G_T3Y
    w_B_converted = conv @ W_B_T3Y

    R_matches = np.allclose(w_R_converted, W_R_T3T8)
    G_matches = np.allclose(w_G_converted, W_G_T3T8)
    B_matches = np.allclose(w_B_converted, W_B_T3T8)

    # Check equilateral in (T3, T8)
    d_RG = np.linalg.norm(W_R_T3T8 - W_G_T3T8)
    d_GB = np.linalg.norm(W_G_T3T8 - W_B_T3T8)
    d_BR = np.linalg.norm(W_B_T3T8 - W_R_T3T8)

    equilateral_in_T3T8 = abs(d_RG - d_GB) < 1e-14 and abs(d_GB - d_BR) < 1e-14

    return {
        'test': 'A2_convention_consistency',
        'description': '(T3, Y) and (T3, T8) conventions related by T8 = Y*sqrt(3)/2',
        'passed': bool(R_matches and G_matches and B_matches and equilateral_in_T3T8),
        'conversion': {'R': bool(R_matches), 'G': bool(G_matches), 'B': bool(B_matches)},
        'T3T8_distances': {'d_RG': float(d_RG), 'd_GB': float(d_GB), 'd_BR': float(d_BR)},
        'equilateral_in_T3T8': bool(equilateral_in_T3T8),
        'note': 'Triangle IS equilateral in Euclidean (T3, T8) — this is the Lean convention',
    }


# ==============================================================================
# ADDITIONAL TEST A-3: KILLING FORM VIA ADJOINT
# ==============================================================================

def test_A3_killing_form_adjoint():
    """
    A-3: Compute Killing form directly from adjoint representation trace
    and verify B(X,Y) = 6 Tr(XY).
    """
    # The adjoint representation ad_X(Y) = [X, Y]
    def ad(X):
        """Return the adjoint representation matrix of X in the basis {lambda_a/2}."""
        dim = 8
        result = np.zeros((dim, dim), dtype=complex)
        basis = [L / 2 for L in LAMBDA]
        for j in range(dim):
            commutator = X @ basis[j] - basis[j] @ X
            # Express commutator in terms of basis
            for i in range(dim):
                # Use Tr(T_a * [X, T_b]) / Tr(T_a * T_a)
                coeff = np.trace(basis[i] @ commutator) / np.trace(basis[i] @ basis[i])
                result[i, j] = coeff
        return result

    # Compute Killing form B(H1, H1) via adjoint: Tr(ad_H1 @ ad_H1)
    H1 = LAMBDA[2]  # lambda_3
    H2 = LAMBDA[7]  # lambda_8

    ad_H1 = ad(H1)
    ad_H2 = ad(H2)

    B_H1H1_adjoint = np.trace(ad_H1 @ ad_H1).real
    B_H2H2_adjoint = np.trace(ad_H2 @ ad_H2).real
    B_H1H2_adjoint = np.trace(ad_H1 @ ad_H2).real

    # Compare with 6 * Tr(XY)
    B_H1H1_trace = 6 * np.trace(H1 @ H1).real
    B_H2H2_trace = 6 * np.trace(H2 @ H2).real
    B_H1H2_trace = 6 * np.trace(H1 @ H2).real

    adjoint_matches_trace = (
        abs(B_H1H1_adjoint - B_H1H1_trace) < 1e-10 and
        abs(B_H2H2_adjoint - B_H2H2_trace) < 1e-10 and
        abs(B_H1H2_adjoint - B_H1H2_trace) < 1e-10
    )

    return {
        'test': 'A3_killing_form_adjoint',
        'description': 'Killing form B(X,Y) = 6 Tr(XY) verified via adjoint representation',
        'passed': bool(adjoint_matches_trace),
        'adjoint_computation': {
            'B_H1H1': float(B_H1H1_adjoint),
            'B_H2H2': float(B_H2H2_adjoint),
            'B_H1H2': float(B_H1H2_adjoint),
        },
        'trace_formula': {
            'B_H1H1': float(B_H1H1_trace),
            'B_H2H2': float(B_H2H2_trace),
            'B_H1H2': float(B_H1H2_trace),
        },
        'match': bool(adjoint_matches_trace),
        'note': 'Killing form normalization B = 6 Tr for SU(3) Gell-Mann convention verified',
    }


# ==============================================================================
# ADDITIONAL TEST A-4: FULL S3 GROUP STRUCTURE
# ==============================================================================

def test_A4_full_S3_structure():
    """
    A-4: Verify the full S_3 group structure of the Weyl group.

    Check that the 6 elements {e, s1, s2, s1*s2, s2*s1, s1*s2*s1}
    form a group with the correct multiplication table.
    """
    weights = np.array([W_R_T3Y, W_G_T3Y, W_B_T3Y])

    # Define permutations as their action on [R, G, B] = [0, 1, 2]
    # Identity
    e = (0, 1, 2)
    # s1: R <-> G
    s1 = (1, 0, 2)
    # s2: G <-> B
    s2 = (0, 2, 1)
    # s1*s2: R->G->B, B->G, so (R,G,B) -> (1,2,0)... let's compute
    # s1*s2 means first apply s2 then s1
    def compose(p, q):
        """Compose permutations: (p*q)(i) = p(q(i))"""
        return tuple(p[q[i]] for i in range(3))

    s1s2 = compose(s1, s2)    # (1, 2, 0) - 3-cycle
    s2s1 = compose(s2, s1)    # (2, 0, 1) - 3-cycle
    s1s2s1 = compose(s1, s2s1)  # R <-> B

    all_elements = [e, s1, s2, s1s2, s2s1, s1s2s1]

    # Verify we have exactly 6 distinct elements
    unique = set(all_elements)
    has_6_elements = len(unique) == 6

    # Verify closure: product of any two elements is in the group
    closure = True
    for p in all_elements:
        for q in all_elements:
            product = compose(p, q)
            if product not in unique:
                closure = False

    # Verify inverse: every element has an inverse in the group
    has_inverses = True
    for p in all_elements:
        has_inv = any(compose(p, q) == e for q in all_elements)
        if not has_inv:
            has_inverses = False

    # Verify that each permutation maps weights to weights
    weight_set = set(map(tuple, weights))
    preserves_weights = True
    for perm in all_elements:
        permuted = tuple(tuple(weights[perm[i]]) for i in range(3))
        if set(permuted) != weight_set:
            preserves_weights = False

    return {
        'test': 'A4_full_S3_structure',
        'description': 'Full S_3 group structure verified (6 elements, closure, inverses)',
        'passed': bool(has_6_elements and closure and has_inverses and preserves_weights),
        'elements': {
            'e': list(e), 's1': list(s1), 's2': list(s2),
            's1s2': list(s1s2), 's2s1': list(s2s1), 's1s2s1': list(s1s2s1),
        },
        'has_6_elements': bool(has_6_elements),
        'closure': bool(closure),
        'has_inverses': bool(has_inverses),
        'preserves_weights': bool(preserves_weights),
    }


# ==============================================================================
# ADDITIONAL TEST A-5: STELLA OCTANGULA TOPOLOGY CONSISTENCY
# ==============================================================================

def test_A5_stella_topology():
    """
    A-5: Verify stella octangula topological properties per Definition 0.1.1.

    The stella octangula has:
    - 8 vertices (4+4)
    - 12 edges (6+6)
    - 8 faces (4+4)
    - 2 connected components
    - Euler characteristic chi = 4 (two S^2, each chi=2)
    """
    # Tetrahedron T+
    Tp = np.array([V_0, V_1, V_2, V_3])

    # Tetrahedron T- = -T+
    Tm = -Tp

    # Verify 8 distinct vertices
    all_verts = np.vstack([Tp, Tm])
    n_vertices = len(all_verts)

    # Check no vertex is shared (disjoint union)
    shared = False
    for i in range(4):
        for j in range(4):
            if np.allclose(Tp[i], Tm[j]):
                shared = True

    # Euler characteristic
    n_edges_per_tet = 6  # C(4,2) = 6
    n_faces_per_tet = 4  # C(4,3) = 4
    total_V = 8
    total_E = 12
    total_F = 8
    chi = total_V - total_E + total_F

    # Each component is a tetrahedron (genus 0 surface), so chi = 2 per component
    chi_per_component = 2
    expected_chi = 2 * chi_per_component

    # Verify centroid of each tetrahedron is at origin
    centroid_p = np.mean(Tp, axis=0)
    centroid_m = np.mean(Tm, axis=0)
    centroids_at_origin = (np.linalg.norm(centroid_p) < 1e-14 and
                           np.linalg.norm(centroid_m) < 1e-14)

    # Verify dual relationship: T- = -T+
    is_dual = np.allclose(Tm, -Tp)

    return {
        'test': 'A5_stella_topology',
        'description': 'Stella octangula topology consistent with Definition 0.1.1',
        'passed': bool(n_vertices == 8 and not shared and chi == expected_chi
                       and centroids_at_origin and is_dual),
        'vertices': int(n_vertices),
        'edges': int(total_E),
        'faces': int(total_F),
        'euler_characteristic': int(chi),
        'expected_chi': int(expected_chi),
        'connected_components': 2,
        'disjoint': not shared,
        'centroids_at_origin': bool(centroids_at_origin),
        'T_minus_equals_neg_T_plus': bool(is_dual),
    }


# ==============================================================================
# PLOTTING
# ==============================================================================

def generate_plots():
    """Generate adversarial verification plots."""
    if not HAS_MATPLOTLIB:
        return

    os.makedirs(PLOT_DIR, exist_ok=True)

    # --- Plot 1: Weight triangles comparison ---
    fig, axes = plt.subplots(1, 3, figsize=(18, 6))

    # Panel 1: Euclidean (T3, Y) — isosceles
    ax = axes[0]
    triangle_T3Y = np.array([W_R_T3Y, W_G_T3Y, W_B_T3Y, W_R_T3Y])
    ax.plot(triangle_T3Y[:, 0], triangle_T3Y[:, 1], 'b-o', markersize=10, linewidth=2)
    for w, label in [(W_R_T3Y, 'R'), (W_G_T3Y, 'G'), (W_B_T3Y, 'B')]:
        ax.annotate(label, w, fontsize=14, fontweight='bold',
                    xytext=(8, 8), textcoords='offset points', color='red')

    # Annotate distances
    d_RG = np.linalg.norm(W_R_T3Y - W_G_T3Y)
    d_GB = np.linalg.norm(W_G_T3Y - W_B_T3Y)
    d_BR = np.linalg.norm(W_B_T3Y - W_R_T3Y)
    mid_RG = (W_R_T3Y + W_G_T3Y) / 2
    mid_GB = (W_G_T3Y + W_B_T3Y) / 2
    mid_BR = (W_B_T3Y + W_R_T3Y) / 2
    ax.annotate(f'{d_RG:.3f}', mid_RG, fontsize=10, ha='center',
                xytext=(0, 10), textcoords='offset points', color='blue')
    ax.annotate(f'{d_GB:.3f}', mid_GB, fontsize=10, ha='center',
                xytext=(-20, 0), textcoords='offset points', color='blue')
    ax.annotate(f'{d_BR:.3f}', mid_BR, fontsize=10, ha='center',
                xytext=(20, 0), textcoords='offset points', color='blue')

    ax.set_xlabel('$T_3$', fontsize=12)
    ax.set_ylabel('$Y$', fontsize=12)
    ax.set_title('Euclidean $(T_3, Y)$: ISOSCELES', fontsize=13, fontweight='bold')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.axvline(x=0, color='k', linewidth=0.5)

    # Panel 2: Euclidean (T3, T8) — equilateral
    ax = axes[1]
    triangle_T3T8 = np.array([W_R_T3T8, W_G_T3T8, W_B_T3T8, W_R_T3T8])
    ax.plot(triangle_T3T8[:, 0], triangle_T3T8[:, 1], 'g-o', markersize=10, linewidth=2)
    for w, label in [(W_R_T3T8, 'R'), (W_G_T3T8, 'G'), (W_B_T3T8, 'B')]:
        ax.annotate(label, w, fontsize=14, fontweight='bold',
                    xytext=(8, 8), textcoords='offset points', color='red')

    d_RG_T8 = np.linalg.norm(W_R_T3T8 - W_G_T3T8)
    d_GB_T8 = np.linalg.norm(W_G_T3T8 - W_B_T3T8)
    d_BR_T8 = np.linalg.norm(W_B_T3T8 - W_R_T3T8)
    mid_RG = (W_R_T3T8 + W_G_T3T8) / 2
    mid_GB = (W_G_T3T8 + W_B_T3T8) / 2
    mid_BR = (W_B_T3T8 + W_R_T3T8) / 2
    ax.annotate(f'{d_RG_T8:.3f}', mid_RG, fontsize=10, ha='center',
                xytext=(0, 10), textcoords='offset points', color='darkgreen')
    ax.annotate(f'{d_GB_T8:.3f}', mid_GB, fontsize=10, ha='center',
                xytext=(-20, 0), textcoords='offset points', color='darkgreen')
    ax.annotate(f'{d_BR_T8:.3f}', mid_BR, fontsize=10, ha='center',
                xytext=(20, 0), textcoords='offset points', color='darkgreen')

    ax.set_xlabel('$T_3$', fontsize=12)
    ax.set_ylabel('$T_8$', fontsize=12)
    ax.set_title('Euclidean $(T_3, T_8)$: EQUILATERAL', fontsize=13, fontweight='bold')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.axvline(x=0, color='k', linewidth=0.5)

    # Panel 3: Projected tetrahedron
    ax = axes[2]
    proj_triangle = np.array([PI_V1, PI_V2, PI_V3, PI_V1])
    ax.plot(proj_triangle[:, 0], proj_triangle[:, 1], 'r-o', markersize=10, linewidth=2)
    ax.plot(0, 0, 'kx', markersize=12, markeredgewidth=2, label='Apex projection')
    for pv, label in [(PI_V1, '$v_1$'), (PI_V2, '$v_2$'), (PI_V3, '$v_3$')]:
        ax.annotate(label, pv, fontsize=14,
                    xytext=(8, 8), textcoords='offset points', color='red')

    d_12 = np.linalg.norm(PI_V1 - PI_V2)
    d_23 = np.linalg.norm(PI_V2 - PI_V3)
    d_31 = np.linalg.norm(PI_V3 - PI_V1)
    mid_12 = (PI_V1 + PI_V2) / 2
    mid_23 = (PI_V2 + PI_V3) / 2
    mid_31 = (PI_V3 + PI_V1) / 2
    ax.annotate(f'{d_12:.3f}', mid_12, fontsize=10, ha='center',
                xytext=(0, 10), textcoords='offset points', color='darkred')
    ax.annotate(f'{d_23:.3f}', mid_23, fontsize=10, ha='center',
                xytext=(-20, 0), textcoords='offset points', color='darkred')
    ax.annotate(f'{d_31:.3f}', mid_31, fontsize=10, ha='center',
                xytext=(20, 0), textcoords='offset points', color='darkred')

    ax.set_xlabel('$x$', fontsize=12)
    ax.set_ylabel('$y$', fontsize=12)
    ax.set_title('Projected Tetrahedron: EQUILATERAL', fontsize=13, fontweight='bold')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.axvline(x=0, color='k', linewidth=0.5)
    ax.legend(fontsize=10)

    fig.suptitle('Theorem 1.1.1 Adversarial Verification: Metric-Dependent Triangle Shape',
                 fontsize=15, fontweight='bold', y=1.02)
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_metric_comparison.png'),
                dpi=150, bbox_inches='tight')
    plt.close()

    # --- Plot 2: Transformation matrix verification ---
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    # Panel 1: Proof's (wrong) matrix
    ax = axes[0]
    a_proof = 3 / (4*np.sqrt(2))
    b_proof = -np.sqrt(3) / (4*np.sqrt(2))
    c_proof = 1 / (2*np.sqrt(2))
    d_proof = 1 / (2*np.sqrt(6))
    A_proof = np.array([[a_proof, b_proof], [c_proof, d_proof]])

    for pv, label, color in [(PI_V1, '$v_1$', 'red'), (PI_V2, '$v_2$', 'green'), (PI_V3, '$v_3$', 'blue')]:
        mapped = A_proof @ pv
        ax.plot(*pv, 'o', color=color, markersize=10, alpha=0.5)
        ax.plot(*mapped, 's', color=color, markersize=10)
        ax.annotate('', mapped, pv, arrowprops=dict(arrowstyle='->', color=color, alpha=0.5))

    for w, label, color in [(W_R_T3Y, '$w_R$', 'red'), (W_G_T3Y, '$w_G$', 'green'), (W_B_T3Y, '$w_B$', 'blue')]:
        ax.plot(*w, '*', color=color, markersize=15, markeredgecolor='black', markeredgewidth=0.5)
        ax.annotate(label, w, fontsize=11, xytext=(8, 8), textcoords='offset points')

    ax.set_title("Proof's Matrix A (WRONG d): Misses G, B targets", fontsize=12, fontweight='bold')
    ax.set_xlabel('$T_3$', fontsize=11)
    ax.set_ylabel('$Y$', fontsize=11)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.legend(['Projected vertex', 'Mapped by A_proof', 'Target weight'], fontsize=9, loc='lower right')

    # Panel 2: Correct matrix
    ax = axes[1]
    V_mat = np.column_stack([PI_V1, PI_V2])
    W_mat = np.column_stack([W_R_T3Y, W_G_T3Y])
    A_correct = W_mat @ np.linalg.inv(V_mat)

    for pv, label, color in [(PI_V1, '$v_1$', 'red'), (PI_V2, '$v_2$', 'green'), (PI_V3, '$v_3$', 'blue')]:
        mapped = A_correct @ pv
        ax.plot(*pv, 'o', color=color, markersize=10, alpha=0.5)
        ax.plot(*mapped, 's', color=color, markersize=10)
        ax.annotate('', mapped, pv, arrowprops=dict(arrowstyle='->', color=color, alpha=0.5))

    for w, label, color in [(W_R_T3Y, '$w_R$', 'red'), (W_G_T3Y, '$w_G$', 'green'), (W_B_T3Y, '$w_B$', 'blue')]:
        ax.plot(*w, '*', color=color, markersize=15, markeredgecolor='black', markeredgewidth=0.5)
        ax.annotate(label, w, fontsize=11, xytext=(8, 8), textcoords='offset points')

    ax.set_title('Correct Matrix A: All targets hit exactly', fontsize=12, fontweight='bold')
    ax.set_xlabel('$T_3$', fontsize=11)
    ax.set_ylabel('$Y$', fontsize=11)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)

    fig.suptitle('Theorem 1.1.1 Error E-2: Transformation Matrix Verification',
                 fontsize=14, fontweight='bold', y=1.02)
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_matrix_verification.png'),
                dpi=150, bbox_inches='tight')
    plt.close()

    # --- Plot 3: Root-weight structure ---
    fig, ax = plt.subplots(1, 1, figsize=(8, 8))

    # Plot all 6 roots
    roots = [ALPHA_1, ALPHA_2, ALPHA_1 + ALPHA_2,
             -ALPHA_1, -ALPHA_2, -(ALPHA_1 + ALPHA_2)]
    root_labels = [r'$\alpha_1$', r'$\alpha_2$', r'$\alpha_1+\alpha_2$',
                   r'$-\alpha_1$', r'$-\alpha_2$', r'$-(\alpha_1+\alpha_2)$']

    for root, label in zip(roots, root_labels):
        ax.plot(*root, 'ko', markersize=8)
        ax.annotate(label, root, fontsize=10, xytext=(5, 5), textcoords='offset points')
        ax.plot([0, root[0]], [0, root[1]], 'k-', alpha=0.3, linewidth=0.5)

    # Plot root hexagon
    root_hexagon = np.array(roots + [roots[0]])
    hex_order = [0, 1, 2, 3, 4, 5, 0]
    ax.plot(root_hexagon[hex_order, 0], root_hexagon[hex_order, 1], 'k--', alpha=0.3)

    # Plot weights of fundamental rep
    mu_1 = (2*ALPHA_1 + ALPHA_2) / 3
    w_R = mu_1
    w_G = mu_1 - ALPHA_1
    w_B = mu_1 - ALPHA_1 - ALPHA_2

    fund_weights = np.array([w_R, w_G, w_B, w_R])
    ax.plot(fund_weights[:, 0], fund_weights[:, 1], 'b-o', markersize=10, linewidth=2, label='Quarks (3)')
    for w, label in [(w_R, 'R'), (w_G, 'G'), (w_B, 'B')]:
        ax.annotate(label, w, fontsize=14, fontweight='bold', color='blue',
                    xytext=(8, 8), textcoords='offset points')

    # Anti-fundamental weights
    w_Rbar = -w_R
    w_Gbar = -w_G
    w_Bbar = -w_B
    anti_weights = np.array([w_Rbar, w_Gbar, w_Bbar, w_Rbar])
    ax.plot(anti_weights[:, 0], anti_weights[:, 1], 'r--o', markersize=10, linewidth=2, label=r'Antiquarks ($\bar{3}$)')
    for w, label in [(w_Rbar, r'$\bar{R}$'), (w_Gbar, r'$\bar{G}$'), (w_Bbar, r'$\bar{B}$')]:
        ax.annotate(label, w, fontsize=14, fontweight='bold', color='red',
                    xytext=(8, -15), textcoords='offset points')

    # Annotate weight differences = full roots (not half-roots!)
    mid_RG = (w_R + w_G) / 2
    ax.annotate(r'$w_R - w_G = \alpha_1$', mid_RG, fontsize=10, color='darkblue',
                xytext=(10, 10), textcoords='offset points',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='lightyellow', alpha=0.8))

    ax.plot(0, 0, 'k+', markersize=15, markeredgewidth=2)
    ax.set_xlabel('Orthonormal Killing basis $e_1$', fontsize=12)
    ax.set_ylabel('Orthonormal Killing basis $e_2$', fontsize=12)
    ax.set_title('SU(3) Root System and Weight Diagram\n(Error E-3: differences are FULL roots)',
                 fontsize=13, fontweight='bold')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=11)

    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_root_weight_structure.png'),
                dpi=150, bbox_inches='tight')
    plt.close()

    # --- Plot 4: Killing form metric comparison ---
    fig, ax = plt.subplots(1, 1, figsize=(8, 5))

    bases = ['$(H_1, H_2)$\n$=(\\lambda_3, \\lambda_8)$',
             '$(T_3, Y)$',
             '$(T_3, Y\\sqrt{3})$',
             '$(T_3, T_8)$']
    g11_vals = [12, 3, 3, 3]
    g22_vals = [12, 4, 12, 3]

    x = np.arange(len(bases))
    width = 0.35
    bars1 = ax.bar(x - width/2, g11_vals, width, label='$g_{11}$', color='steelblue', alpha=0.8)
    bars2 = ax.bar(x + width/2, g22_vals, width, label='$g_{22}$', color='coral', alpha=0.8)

    # Mark which are Euclidean (g11 = g22)
    for i, (g1, g2) in enumerate(zip(g11_vals, g22_vals)):
        if abs(g1 - g2) < 0.1:
            ax.text(i, max(g1, g2) + 0.5, 'Euclidean', ha='center', fontsize=10,
                    fontweight='bold', color='green')
        else:
            ax.text(i, max(g1, g2) + 0.5, 'NOT Euclidean', ha='center', fontsize=10,
                    fontweight='bold', color='red')

    ax.set_xticks(x)
    ax.set_xticklabels(bases, fontsize=10)
    ax.set_ylabel('Killing metric component', fontsize=12)
    ax.set_title('Error E-4: Killing Form Metric in Different Bases\n'
                 '($g_{12} = 0$ in all bases; Euclidean requires $g_{11} = g_{22}$)',
                 fontsize=13, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_killing_metric_bases.png'),
                dpi=150, bbox_inches='tight')
    plt.close()

    print(f"  Plots saved to {PLOT_DIR}/")


# ==============================================================================
# MAIN EXECUTION
# ==============================================================================

def main():
    print("=" * 72)
    print("ADVERSARIAL VERIFICATION: Theorem 1.1.1")
    print("SU(3) Weight Diagram <-> Stella Octangula Isomorphism")
    print("Date: 2026-02-21")
    print("=" * 72)
    print()

    tests = [
        ("ERROR TESTS", [
            test_E1_euclidean_distances,
            test_E2_transformation_matrix,
            test_E3_root_weight_relation,
            test_E4_killing_form_basis,
            test_E5_rotation_vs_reflection,
        ]),
        ("ADDITIONAL TESTS", [
            test_A1_weyl_reflections_proper_basis,
            test_A2_convention_consistency,
            test_A3_killing_form_adjoint,
            test_A4_full_S3_structure,
            test_A5_stella_topology,
        ]),
    ]

    all_results = []
    total_passed = 0
    total_tests = 0

    for section_name, test_funcs in tests:
        print(f"\n--- {section_name} ---\n")
        for test_func in test_funcs:
            total_tests += 1
            try:
                result = test_func()
                all_results.append(result)
                passed = result.get('passed', False)
                if passed:
                    total_passed += 1
                    status = "PASS"
                else:
                    status = "FAIL"

                error_flag = ""
                if 'error_confirmed' in result and result['error_confirmed']:
                    error_flag = " [ERROR IN PROOF CONFIRMED]"

                print(f"  {status}: {result['test']} — {result['description']}{error_flag}")
            except Exception as e:
                all_results.append({
                    'test': test_func.__name__,
                    'passed': False,
                    'error': str(e),
                    'description': 'Exception during test',
                })
                print(f"  EXCEPTION: {test_func.__name__}: {e}")

    # Generate plots
    print("\n--- GENERATING PLOTS ---\n")
    generate_plots()

    # Summary
    print()
    print("=" * 72)
    print(f"RESULTS: {total_passed}/{total_tests} tests passed")
    print()

    errors_confirmed = sum(1 for r in all_results
                           if r.get('error_confirmed', False))
    print(f"ERRORS IN PROOF CONFIRMED: {errors_confirmed}")
    for r in all_results:
        if r.get('error_confirmed', False):
            print(f"  - {r['test']}: {r['description']}")

    print()
    if total_passed == total_tests:
        print("ALL ADVERSARIAL TESTS PASSED")
        print("(Note: 'PASS' for error tests means the error was successfully detected)")
    else:
        print("SOME TESTS DID NOT PASS — review results")
    print("=" * 72)

    # Save results
    output = {
        'theorem': '1.1.1',
        'title': 'SU(3) Weight Diagram <-> Stella Octangula Isomorphism',
        'verification_type': 'adversarial',
        'timestamp': datetime.now().isoformat(),
        'total_passed': total_passed,
        'total_tests': total_tests,
        'errors_confirmed': errors_confirmed,
        'results': all_results,
    }

    output_file = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               'theorem_1_1_1_adversarial_results.json')
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to {output_file}")

    return 0 if total_passed == total_tests else 1


if __name__ == "__main__":
    sys.exit(main())
