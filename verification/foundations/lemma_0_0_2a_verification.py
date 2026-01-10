#!/usr/bin/env python3
"""
Lemma 0.0.2a Verification Script
Confinement and Physical Dimension Constraint

This script verifies the mathematical claims in Lemma 0.0.2a:
- D_space >= N - 1 for SU(N) with confinement
- N points in general position require N-1 dimensions
- Compatibility table for various SU(N) groups

Author: Multi-Agent Verification System
Date: 2026-01-02
"""

import numpy as np
import json
from datetime import datetime
from scipy.spatial import ConvexHull, Delaunay
from scipy.linalg import svd
import matplotlib.pyplot as plt
import os

# Ensure plots directory exists
PLOTS_DIR = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots"
os.makedirs(PLOTS_DIR, exist_ok=True)

# ============================================================================
# TEST 1: N Points in General Position Require N-1 Dimensions
# ============================================================================

def test_affine_independence():
    """
    Verify that N affinely independent points require exactly N-1 dimensions.

    Mathematical fact: An (N-1)-simplex has N vertices and exists in (N-1) dimensions.
    """
    results = []

    # Test cases: simplices of various dimensions
    test_cases = [
        # (N vertices, expected dimension)
        (2, 1),   # Line segment (1-simplex)
        (3, 2),   # Triangle (2-simplex)
        (4, 3),   # Tetrahedron (3-simplex)
        (5, 4),   # 4-simplex
        (6, 5),   # 5-simplex
    ]

    for N, expected_dim in test_cases:
        # Generate regular N-1 simplex vertices
        vertices = generate_regular_simplex(N)

        # Compute the affine dimension (rank of centered point matrix)
        centered = vertices - vertices.mean(axis=0)
        rank = np.linalg.matrix_rank(centered, tol=1e-10)

        # The affine dimension is the rank of the centered matrix
        # For N points in general position, this should be N-1
        affine_dim = rank

        success = affine_dim == expected_dim
        results.append({
            'N': N,
            'expected_dimension': expected_dim,
            'computed_dimension': affine_dim,
            'status': 'PASS' if success else 'FAIL'
        })
        print(f"N={N} vertices: expected dim={expected_dim}, computed dim={affine_dim} - {'PASS' if success else 'FAIL'}")

    return results


def generate_regular_simplex(N):
    """
    Generate vertices of a regular (N-1)-simplex in (N-1)-dimensional space.

    For an N-1 simplex:
    - Place N vertices such that all pairwise distances are equal
    - The vertices lie in (N-1)-dimensional space
    """
    if N == 2:
        return np.array([[0.0], [1.0]])

    # Standard construction: vertices are unit vectors in N-dimensional space
    # projected onto the hyperplane perpendicular to (1,1,...,1)
    vertices = np.eye(N)

    # Center at origin (subtract centroid)
    centroid = vertices.mean(axis=0)
    vertices_centered = vertices - centroid

    # Project to (N-1)-dimensional space using SVD
    U, S, Vh = svd(vertices_centered)

    # Take first N-1 components (the non-trivial directions)
    vertices_reduced = vertices_centered @ Vh.T[:, :N-1]

    return vertices_reduced


# ============================================================================
# TEST 2: SU(N) Compatibility Table
# ============================================================================

def test_su_n_compatibility():
    """
    Verify the compatibility table from Section 4.1 of Lemma 0.0.2a.

    For D_space = 3 (our universe), check which SU(N) groups are compatible.
    Constraint: D_space >= N - 1
    """
    D_space = 3  # Our universe has 3 spatial dimensions

    results = []

    gauge_groups = [
        ('SU(2)', 2, 1),   # (name, N, rank)
        ('SU(3)', 3, 2),
        ('SU(4)', 4, 3),
        ('SU(5)', 5, 4),
        ('SU(6)', 6, 5),
        ('SU(10)', 10, 9),
    ]

    for name, N, rank in gauge_groups:
        constraint = N - 1  # D_space >= N - 1
        compatible = D_space >= constraint
        margin = D_space - constraint

        # Note: The lemma claims this as a lower bound, not a selection criterion
        results.append({
            'gauge_group': name,
            'N': N,
            'rank': rank,
            'constraint_D_min': constraint,
            'D_space': D_space,
            'compatible': compatible,
            'margin': margin,
            'status': 'PASS' if compatible else 'EXCLUDED'
        })

        status = 'COMPATIBLE' if compatible else 'EXCLUDED'
        print(f"{name}: D >= {constraint}, D_space = {D_space} - {status} (margin: {margin})")

    return results


# ============================================================================
# TEST 3: Verify SU(3) Weight Space Structure
# ============================================================================

def test_su3_weight_space():
    """
    Verify that SU(3) fundamental weights form an equilateral triangle (2-simplex).

    The 3 color charges (R, G, B) should map to 3 points in 2D weight space
    forming an equilateral triangle.
    """
    # SU(3) fundamental weights in (T3, T8) basis
    # These are the eigenvalues of the Cartan generators acting on |R>, |G>, |B>
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    weights = np.array([w_R, w_G, w_B])

    # Verify weights sum to zero (color singlet condition)
    weight_sum = weights.sum(axis=0)
    sum_is_zero = np.allclose(weight_sum, [0, 0], atol=1e-10)

    # Compute pairwise distances
    d_RG = np.linalg.norm(w_R - w_G)
    d_GB = np.linalg.norm(w_G - w_B)
    d_BR = np.linalg.norm(w_B - w_R)

    # Check equilateral (all distances equal)
    is_equilateral = np.allclose([d_RG, d_GB, d_BR], [d_RG, d_RG, d_RG], atol=1e-10)

    # Compute the affine dimension
    centered = weights - weights.mean(axis=0)
    rank = np.linalg.matrix_rank(centered, tol=1e-10)

    results = {
        'weights': {
            'R': w_R.tolist(),
            'G': w_G.tolist(),
            'B': w_B.tolist()
        },
        'weight_sum': weight_sum.tolist(),
        'sum_is_zero': sum_is_zero,
        'distances': {
            'd_RG': d_RG,
            'd_GB': d_GB,
            'd_BR': d_BR
        },
        'is_equilateral': is_equilateral,
        'affine_dimension': rank,
        'expected_dimension': 2,  # 3 points -> 2D (triangle)
        'dimension_check': rank == 2,
        'all_checks_pass': sum_is_zero and is_equilateral and (rank == 2)
    }

    print(f"\nSU(3) Weight Space Verification:")
    print(f"  Weights sum to zero: {sum_is_zero}")
    print(f"  Equilateral triangle: {is_equilateral}")
    print(f"  Distances: d_RG={d_RG:.6f}, d_GB={d_GB:.6f}, d_BR={d_BR:.6f}")
    print(f"  Affine dimension: {rank} (expected: 2)")
    print(f"  Status: {'PASS' if results['all_checks_pass'] else 'FAIL'}")

    return results


# ============================================================================
# TEST 4: Verify D = N + 1 Formula (Reference to Theorem 0.0.2b)
# ============================================================================

def test_d_equals_n_plus_1():
    """
    Verify the D = N + 1 formula for SU(N) gauge theories.

    Formula: D = (N-1)_angular + 1_radial + 1_temporal = N + 1

    This is verified for the observed case:
    - SU(3) -> N = 3 -> D = 4 (3 spatial + 1 temporal)
    """
    results = []

    # The formula D = N + 1
    # For SU(N): D_total = N + 1, so D_space = N (spatial dimensions = N)

    # Our universe: SU(3) with D = 4
    N_observed = 3
    D_observed = 4

    D_predicted = N_observed + 1
    formula_matches = D_predicted == D_observed

    results.append({
        'test': 'SU(3) in D=4',
        'N': N_observed,
        'D_predicted': D_predicted,
        'D_observed': D_observed,
        'formula_matches': formula_matches,
        'status': 'PASS' if formula_matches else 'FAIL'
    })

    # Check that the formula D_space >= N - 1 is satisfied
    # D_space = D - 1 = N (from D = N + 1)
    # Constraint: D_space >= N - 1 means N >= N - 1, always true for N >= 1
    D_space = N_observed  # From D = N + 1, D_space = N
    constraint = N_observed - 1
    satisfies_constraint = D_space >= constraint

    results.append({
        'test': 'Lemma 0.0.2a constraint',
        'D_space': D_space,
        'constraint_D_min': constraint,
        'satisfies': satisfies_constraint,
        'status': 'PASS' if satisfies_constraint else 'FAIL'
    })

    print(f"\nD = N + 1 Formula Verification:")
    print(f"  SU(3): N={N_observed}, D_predicted={D_predicted}, D_observed={D_observed} - {'PASS' if formula_matches else 'FAIL'}")
    print(f"  Constraint D_space >= N-1: {D_space} >= {constraint} - {'PASS' if satisfies_constraint else 'FAIL'}")

    return results


# ============================================================================
# TEST 5: Visualization of Weight Space and Dimension Constraint
# ============================================================================

def create_verification_plots():
    """
    Create visualization plots for the verification.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    # Plot 1: SU(3) weight space (equilateral triangle)
    ax1 = axes[0]

    # Fundamental weights
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    # Plot triangle
    triangle = np.array([w_R, w_G, w_B, w_R])  # Close the triangle
    ax1.plot(triangle[:, 0], triangle[:, 1], 'b-', linewidth=2, label='Weight triangle')

    # Plot vertices with colors
    colors_rgb = {'R': 'red', 'G': 'green', 'B': 'blue'}
    for label, w, color in [('R', w_R, 'red'), ('G', w_G, 'green'), ('B', w_B, 'blue')]:
        ax1.scatter([w[0]], [w[1]], c=color, s=200, zorder=5, edgecolors='black', linewidth=2)
        ax1.annotate(label, w + np.array([0.03, 0.03]), fontsize=14, fontweight='bold')

    # Plot origin
    ax1.scatter([0], [0], c='black', s=100, marker='x', zorder=5, label='Origin')

    ax1.set_xlabel('$T_3$ (Isospin)', fontsize=12)
    ax1.set_ylabel('$T_8 / \\sqrt{3}$ (Hypercharge)', fontsize=12)
    ax1.set_title('SU(3) Fundamental Weights\n(N=3 colors form 2-simplex in 2D)', fontsize=14)
    ax1.set_aspect('equal')
    ax1.grid(True, alpha=0.3)
    ax1.legend(loc='upper right')

    # Plot 2: Compatibility diagram
    ax2 = axes[1]

    N_values = np.arange(2, 8)
    D_constraint = N_values - 1  # D_space >= N - 1
    D_space_actual = 3  # Our universe

    ax2.fill_between(N_values, D_constraint, 10, alpha=0.3, color='green', label='Compatible region')
    ax2.fill_between(N_values, 0, D_constraint, alpha=0.3, color='red', label='Excluded region')
    ax2.plot(N_values, D_constraint, 'k-', linewidth=2, label='$D_{space} = N - 1$')
    ax2.axhline(y=D_space_actual, color='blue', linestyle='--', linewidth=2, label=f'Our universe: $D_{{space}}$ = {D_space_actual}')

    # Mark specific SU(N) groups
    su_groups = [(2, 'SU(2)'), (3, 'SU(3)'), (4, 'SU(4)'), (5, 'SU(5)'), (6, 'SU(6)')]
    for N, label in su_groups:
        y_pos = D_space_actual
        color = 'green' if D_space_actual >= N - 1 else 'red'
        marker = 'o' if D_space_actual >= N - 1 else 'x'
        ax2.scatter([N], [y_pos], c=color, s=150, marker=marker, zorder=5, edgecolors='black', linewidth=2)
        ax2.annotate(label, (N + 0.1, y_pos + 0.2), fontsize=10, fontweight='bold')

    ax2.set_xlabel('N (number of colors in SU(N))', fontsize=12)
    ax2.set_ylabel('$D_{space}$ (spatial dimensions)', fontsize=12)
    ax2.set_title('Lemma 0.0.2a: Dimension-Color Compatibility\n$D_{space} \\geq N - 1$ for SU(N) with confinement', fontsize=14)
    ax2.set_xlim(1.5, 7.5)
    ax2.set_ylim(0, 7)
    ax2.legend(loc='upper left')
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()

    # Save plot
    plot_path = os.path.join(PLOTS_DIR, 'lemma_0_0_2a_verification.png')
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to: {plot_path}")

    plt.close()

    return plot_path


# ============================================================================
# TEST 6: Counter-Example Analysis (SU(5) GUT)
# ============================================================================

def test_su5_counterexample():
    """
    Analyze the SU(5) GUT case as a potential counter-example.

    The lemma claims D_space >= N - 1 = 4 for SU(5), which would exclude it from D_space = 3.
    However, SU(5) GUT is a mathematically consistent theory in 4D spacetime.

    This test documents the issue and the framework's response.
    """
    N = 5  # SU(5)
    D_space = 3  # Our universe
    constraint = N - 1  # = 4

    # The lemma would say SU(5) is excluded
    compatible_per_lemma = D_space >= constraint

    # But SU(5) GUT is mathematically consistent in D = 4
    su5_gut_is_consistent = True  # This is a fact from literature

    # Resolution: The lemma's constraint is a framework-specific requirement,
    # not a universal physical law. It applies when color charges are
    # geometrically realized as polyhedral vertices.

    results = {
        'gauge_group': 'SU(5)',
        'N': N,
        'constraint_D_min': constraint,
        'D_space': D_space,
        'compatible_per_lemma': compatible_per_lemma,
        'su5_gut_is_consistent': su5_gut_is_consistent,
        'resolution': 'Lemma constraint applies to geometric realization, not general QFT',
        'notes': [
            'SU(5) GUT is excluded experimentally by proton decay bounds, not dimensional incompatibility',
            'The lemma constraint is specific to the Chiral Geometrogenesis geometric framework',
            'Standard QFT allows any SU(N) in any D >= 4'
        ]
    }

    print(f"\nSU(5) Counter-Example Analysis:")
    print(f"  Lemma says SU(5) requires D_space >= {constraint}")
    print(f"  Our universe has D_space = {D_space}")
    print(f"  Compatible per lemma: {compatible_per_lemma}")
    print(f"  SU(5) GUT is mathematically consistent: {su5_gut_is_consistent}")
    print(f"  Resolution: Constraint is framework-specific, not universal")

    return results


# ============================================================================
# MAIN VERIFICATION
# ============================================================================

def run_all_tests():
    """
    Run all verification tests and compile results.
    """
    print("=" * 70)
    print("LEMMA 0.0.2a VERIFICATION: Confinement and Physical Dimension Constraint")
    print("=" * 70)

    all_results = {
        'lemma': 'Lemma 0.0.2a',
        'title': 'Confinement and Physical Dimension Constraint',
        'verification_date': datetime.now().isoformat(),
        'tests': {}
    }

    # Test 1: Affine independence
    print("\n" + "-" * 50)
    print("TEST 1: N Points in General Position Require N-1 Dimensions")
    print("-" * 50)
    all_results['tests']['affine_independence'] = test_affine_independence()

    # Test 2: SU(N) compatibility
    print("\n" + "-" * 50)
    print("TEST 2: SU(N) Compatibility Table")
    print("-" * 50)
    all_results['tests']['su_n_compatibility'] = test_su_n_compatibility()

    # Test 3: SU(3) weight space
    print("\n" + "-" * 50)
    print("TEST 3: SU(3) Weight Space Structure")
    print("-" * 50)
    all_results['tests']['su3_weight_space'] = test_su3_weight_space()

    # Test 4: D = N + 1 formula
    print("\n" + "-" * 50)
    print("TEST 4: D = N + 1 Formula")
    print("-" * 50)
    all_results['tests']['d_equals_n_plus_1'] = test_d_equals_n_plus_1()

    # Test 5: Create plots
    print("\n" + "-" * 50)
    print("TEST 5: Verification Plots")
    print("-" * 50)
    plot_path = create_verification_plots()
    all_results['tests']['visualization'] = {'plot_path': plot_path}

    # Test 6: SU(5) counter-example
    print("\n" + "-" * 50)
    print("TEST 6: SU(5) Counter-Example Analysis")
    print("-" * 50)
    all_results['tests']['su5_counterexample'] = test_su5_counterexample()

    # Summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)

    # Count pass/fail
    total_tests = 0
    passed_tests = 0

    for test_name, test_results in all_results['tests'].items():
        if isinstance(test_results, list):
            for r in test_results:
                if 'status' in r:
                    total_tests += 1
                    if r['status'] == 'PASS':
                        passed_tests += 1
        elif isinstance(test_results, dict):
            if 'status' in test_results:
                total_tests += 1
                if test_results['status'] == 'PASS':
                    passed_tests += 1
            elif 'all_checks_pass' in test_results:
                total_tests += 1
                if test_results['all_checks_pass']:
                    passed_tests += 1

    all_results['summary'] = {
        'total_tests': total_tests,
        'passed_tests': passed_tests,
        'pass_rate': f"{passed_tests}/{total_tests}",
        'overall_status': 'PARTIAL - See verification report for details'
    }

    print(f"\nTotal tests: {total_tests}")
    print(f"Passed: {passed_tests}")
    print(f"Pass rate: {passed_tests}/{total_tests}")
    print(f"\nOVERALL STATUS: PARTIAL")
    print("  - Mathematical claims (N points -> N-1 dimensions) are CORRECT")
    print("  - Physical interpretation (confinement -> discrete charges) needs refinement")
    print("  - Framework-specific constraint, not universal physical law")

    # Save results
    results_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/foundations/lemma_0_0_2a_verification_results.json"
    with open(results_path, 'w') as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"\nResults saved to: {results_path}")

    return all_results


if __name__ == '__main__':
    results = run_all_tests()
