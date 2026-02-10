#!/usr/bin/env python3
"""
Numerical Verification of Theorem 0.2.1: Total Field from Superposition

This script verifies the mathematical claims in Theorem 0.2.1:
1. Superposition formula: χ_total = Σ_c a_c(x) e^{iφ_c}
2. Energy density positive: ρ(x) = a_0² Σ_c P_c(x)² > 0
3. Center is a node: χ_total(0) = 0 but ρ(0) ≠ 0
4. Alternative form for |χ_total|²
5. Non-zero gradient at center
6. Energy density at special points (center and vertices)
7. Finite total energy integral
8. Real and imaginary parts of χ_total

Dependencies: numpy, scipy
"""

import numpy as np
from scipy.integrate import quad
import json
import sys

# =============================================================================
# Parameters
# =============================================================================

# Regularization parameter (physical value from Def 0.1.1 §12.6)
EPSILON = 0.50

# Normalization constant (set to 1 for verification)
A0 = 1.0

# Phase values from Definition 0.1.2
PHI_R = 0.0
PHI_G = 2 * np.pi / 3
PHI_B = 4 * np.pi / 3

# =============================================================================
# Vertex Positions (from Definition 0.1.1 / 0.1.3)
# =============================================================================

X_R = np.array([1, 1, 1]) / np.sqrt(3)
X_G = np.array([1, -1, -1]) / np.sqrt(3)
X_B = np.array([-1, 1, -1]) / np.sqrt(3)
X_W = np.array([-1, -1, 1]) / np.sqrt(3)

VERTICES = {'R': X_R, 'G': X_G, 'B': X_B, 'W': X_W}
PHASES = {'R': PHI_R, 'G': PHI_G, 'B': PHI_B}

# =============================================================================
# Core Functions
# =============================================================================

def pressure(x, x_c, epsilon=EPSILON):
    """Pressure function P_c(x) = 1 / (|x - x_c|² + ε²)"""
    x = np.asarray(x)
    x_c = np.asarray(x_c)
    dist_sq = np.sum((x - x_c)**2)
    return 1.0 / (dist_sq + epsilon**2)


def amplitude(x, x_c, a0=A0, epsilon=EPSILON):
    """Field amplitude a_c(x) = a_0 * P_c(x)"""
    return a0 * pressure(x, x_c, epsilon)


def chiral_field(x, x_c, phi_c, a0=A0, epsilon=EPSILON):
    """Chiral field χ_c(x) = a_c(x) * exp(i*φ_c)"""
    return amplitude(x, x_c, a0, epsilon) * np.exp(1j * phi_c)


def total_chiral_field(x, epsilon=EPSILON):
    """Total chiral field χ_total(x) = Σ_c χ_c(x)"""
    chi_R = chiral_field(x, X_R, PHI_R, epsilon=epsilon)
    chi_G = chiral_field(x, X_G, PHI_G, epsilon=epsilon)
    chi_B = chiral_field(x, X_B, PHI_B, epsilon=epsilon)
    return chi_R + chi_G + chi_B


def energy_density(x, epsilon=EPSILON):
    """Energy density ρ(x) = a_0² Σ_c P_c(x)²"""
    p_r = pressure(x, X_R, epsilon)
    p_g = pressure(x, X_G, epsilon)
    p_b = pressure(x, X_B, epsilon)
    return A0**2 * (p_r**2 + p_g**2 + p_b**2)


def gradient_pressure(x, x_c, epsilon=EPSILON):
    """Gradient of pressure function: ∇P_c = -2(x - x_c) / (|x - x_c|² + ε²)²"""
    x = np.asarray(x)
    x_c = np.asarray(x_c)
    dist_sq = np.sum((x - x_c)**2)
    return -2.0 * (x - x_c) / (dist_sq + epsilon**2)**2


def gradient_chiral_field(x, epsilon=EPSILON):
    """Gradient of total chiral field: ∇χ_total = Σ_c e^{iφ_c} ∇a_c"""
    grad = np.zeros(3, dtype=complex)
    for c, phi in PHASES.items():
        x_c = VERTICES[c]
        grad += A0 * np.exp(1j * phi) * gradient_pressure(x, x_c, epsilon)
    return grad


# =============================================================================
# Test Functions
# =============================================================================

def test_superposition_formula():
    """
    Test 1: Verify superposition formula χ_total = Σ_c a_c(x) e^{iφ_c}
    Test at multiple points
    """
    test_points = [
        np.array([0.0, 0.0, 0.0]),  # center
        np.array([0.1, 0.2, 0.3]),  # arbitrary point
        0.5 * X_R,  # halfway to R
        0.3 * X_G + 0.2 * X_B,  # combination
    ]

    results = []
    all_match = True

    for pt in test_points:
        # Direct computation
        chi_direct = total_chiral_field(pt)

        # Component-by-component
        chi_R = chiral_field(pt, X_R, PHI_R)
        chi_G = chiral_field(pt, X_G, PHI_G)
        chi_B = chiral_field(pt, X_B, PHI_B)
        chi_sum = chi_R + chi_G + chi_B

        error = abs(chi_direct - chi_sum)
        matches = error < 1e-14

        if not matches:
            all_match = False

        results.append({
            'point': pt.tolist(),
            'chi_direct': {'real': float(chi_direct.real), 'imag': float(chi_direct.imag)},
            'chi_sum': {'real': float(chi_sum.real), 'imag': float(chi_sum.imag)},
            'error': float(error),
            'matches': bool(matches)
        })

    return {
        'test': 'superposition_formula',
        'passed': bool(all_match),
        'points': results
    }


def test_energy_density_positive():
    """
    Test 2: Energy density ρ(x) > 0 for all x
    """
    # Test at many random points
    np.random.seed(42)
    n_points = 100
    random_points = np.random.uniform(-1, 1, (n_points, 3))

    # Also include special points
    special_points = [
        np.array([0.0, 0.0, 0.0]),
        X_R, X_G, X_B, X_W,
        0.99 * X_R,  # near vertex
    ]

    all_positive = True
    min_rho = float('inf')
    max_rho = 0

    for pt in np.vstack([random_points, special_points]):
        rho = energy_density(pt)
        if rho <= 0:
            all_positive = False
        min_rho = min(min_rho, rho)
        max_rho = max(max_rho, rho)

    return {
        'test': 'energy_density_positive',
        'passed': bool(all_positive and min_rho > 0),
        'n_points_tested': n_points + len(special_points),
        'min_rho': float(min_rho),
        'max_rho': float(max_rho),
        'all_positive': bool(all_positive)
    }


def test_center_node():
    """
    Test 3: At center, χ_total(0) = 0 but ρ(0) ≠ 0
    """
    origin = np.array([0.0, 0.0, 0.0])

    chi = total_chiral_field(origin)
    rho = energy_density(origin)

    chi_zero = abs(chi) < 1e-14
    rho_nonzero = rho > 0

    # Expected values
    P0 = 1.0 / (1.0 + EPSILON**2)
    expected_rho = A0**2 * 3 * P0**2

    return {
        'test': 'center_node',
        'passed': bool(chi_zero and rho_nonzero),
        'chi_total(0)': {'real': float(chi.real), 'imag': float(chi.imag), 'magnitude': float(abs(chi))},
        'rho(0)': float(rho),
        'expected_rho(0)': float(expected_rho),
        'rho_error': float(abs(rho - expected_rho)),
        'chi_is_zero': bool(chi_zero),
        'rho_is_nonzero': bool(rho_nonzero)
    }


def test_alternative_form():
    """
    Test 4: Verify alternative form for |χ_total|²
    |χ_total|² = (a_0²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]
    """
    test_points = [
        np.array([0.0, 0.0, 0.0]),
        np.array([0.1, 0.2, 0.3]),
        0.5 * X_R,
        np.array([0.3, -0.2, 0.1]),
    ]

    results = []
    all_match = True

    for pt in test_points:
        # Direct computation
        chi = total_chiral_field(pt)
        chi_sq_direct = abs(chi)**2

        # Alternative form
        p_r = pressure(pt, X_R)
        p_g = pressure(pt, X_G)
        p_b = pressure(pt, X_B)

        chi_sq_alt = (A0**2 / 2) * (
            (p_r - p_g)**2 + (p_g - p_b)**2 + (p_b - p_r)**2
        )

        error = abs(chi_sq_direct - chi_sq_alt)
        matches = error < 1e-12

        if not matches:
            all_match = False

        results.append({
            'point': pt.tolist(),
            'chi_sq_direct': float(chi_sq_direct),
            'chi_sq_alternative': float(chi_sq_alt),
            'error': float(error),
            'matches': bool(matches)
        })

    return {
        'test': 'alternative_form',
        'passed': bool(all_match),
        'formula': '|χ|² = (a₀²/2)[(P_R-P_G)² + (P_G-P_B)² + (P_B-P_R)²]',
        'points': results
    }


def test_nonzero_gradient_at_center():
    """
    Test 5: Gradient of χ_total at center is non-zero
    """
    origin = np.array([0.0, 0.0, 0.0])

    grad = gradient_chiral_field(origin)
    grad_magnitude = np.sqrt(np.sum(np.abs(grad)**2))

    # Compute expected value from theorem
    P0 = 1.0 / (1.0 + EPSILON**2)

    # From §5.2: ∇χ|_0 = 2a_0 P_0² Σ_c x_c e^{iφ_c}
    expected_sum = X_R + X_G * np.exp(1j * PHI_G) + X_B * np.exp(1j * PHI_B)
    expected_grad = 2 * A0 * P0**2 * expected_sum

    # Compare magnitudes
    expected_magnitude = np.sqrt(np.sum(np.abs(expected_grad)**2))

    return {
        'test': 'nonzero_gradient_at_center',
        'passed': bool(grad_magnitude > 1e-10),
        'gradient': {
            'x': {'real': float(grad[0].real), 'imag': float(grad[0].imag)},
            'y': {'real': float(grad[1].real), 'imag': float(grad[1].imag)},
            'z': {'real': float(grad[2].real), 'imag': float(grad[2].imag)}
        },
        'magnitude': float(grad_magnitude),
        'expected_magnitude': float(expected_magnitude),
        'is_nonzero': bool(grad_magnitude > 1e-10)
    }


def test_energy_at_special_points():
    """
    Test 6: Energy density at center and vertices
    - At center: ρ(0) = 3a_0²/(1+ε²)²
    - At vertex: ρ(x_R) = a_0²[1/ε⁴ + 2/(8/3 + ε²)²]
    """
    origin = np.array([0.0, 0.0, 0.0])

    # Center
    rho_center = energy_density(origin)
    P0 = 1.0 / (1.0 + EPSILON**2)
    expected_center = A0**2 * 3 * P0**2

    # Vertex (R)
    rho_vertex = energy_density(X_R)
    P_R_at_R = 1.0 / EPSILON**2
    P_G_at_R = 1.0 / (8.0/3.0 + EPSILON**2)
    P_B_at_R = P_G_at_R  # Same distance
    expected_vertex = A0**2 * (P_R_at_R**2 + 2 * P_G_at_R**2)

    center_error = abs(rho_center - expected_center)
    vertex_error = abs(rho_vertex - expected_vertex)

    # Verify energy peaks at vertices
    vertex_greater_than_center = rho_vertex > rho_center

    return {
        'test': 'energy_at_special_points',
        'passed': bool(center_error < 1e-12 and vertex_error < 1e-12 and vertex_greater_than_center),
        'center': {
            'rho': float(rho_center),
            'expected': float(expected_center),
            'error': float(center_error)
        },
        'vertex_R': {
            'rho': float(rho_vertex),
            'expected': float(expected_vertex),
            'error': float(vertex_error)
        },
        'ratio_vertex_to_center': float(rho_vertex / rho_center),
        'vertex_greater_than_center': bool(vertex_greater_than_center)
    }


def test_energy_integral_convergence():
    """
    Test 7: Total energy integral is finite
    For single source: ∫ P²(r) 4πr² dr = π²/ε (as R→∞)
    """
    def integrand(r):
        return r**2 / (r**2 + EPSILON**2)**2

    R_max = 10.0  # Large enough

    # Numerical integration
    numerical, error = quad(integrand, 0, R_max)
    numerical_full = 4 * np.pi * numerical

    # Analytical result (from theorem §8.2)
    def analytical_integral(R, eps):
        return 0.5 * (np.arctan(R/eps) - R*eps/(R**2 + eps**2)) / eps

    analytical = analytical_integral(R_max, EPSILON)
    analytical_full = 4 * np.pi * analytical

    # Asymptotic value
    asymptotic = np.pi**2 / EPSILON

    rel_error = abs(numerical_full - analytical_full) / analytical_full

    return {
        'test': 'energy_integral_convergence',
        'passed': bool(rel_error < 1e-6 and np.isfinite(numerical_full)),
        'epsilon': float(EPSILON),
        'R_max': float(R_max),
        'numerical_integral': float(numerical_full),
        'analytical_integral': float(analytical_full),
        'asymptotic_value': float(asymptotic),
        'relative_error': float(rel_error),
        'is_finite': bool(np.isfinite(numerical_full))
    }


def test_real_imaginary_parts():
    """
    Test 8: Verify real and imaginary parts formula
    Re[χ] = a_0[P_R - (P_G + P_B)/2]
    Im[χ] = a_0 * (√3/2)(P_G - P_B)
    """
    test_points = [
        np.array([0.0, 0.0, 0.0]),
        np.array([0.1, 0.2, 0.3]),
        0.5 * X_R,
        np.array([0.3, -0.2, 0.1]),
    ]

    results = []
    all_match = True

    for pt in test_points:
        chi = total_chiral_field(pt)

        p_r = pressure(pt, X_R)
        p_g = pressure(pt, X_G)
        p_b = pressure(pt, X_B)

        # Expected from theorem
        expected_real = A0 * (p_r - 0.5 * (p_g + p_b))
        expected_imag = A0 * (np.sqrt(3) / 2) * (p_g - p_b)

        real_error = abs(chi.real - expected_real)
        imag_error = abs(chi.imag - expected_imag)

        matches = real_error < 1e-14 and imag_error < 1e-14
        if not matches:
            all_match = False

        results.append({
            'point': pt.tolist(),
            'chi_real': float(chi.real),
            'expected_real': float(expected_real),
            'real_error': float(real_error),
            'chi_imag': float(chi.imag),
            'expected_imag': float(expected_imag),
            'imag_error': float(imag_error),
            'matches': bool(matches)
        })

    return {
        'test': 'real_imaginary_parts',
        'passed': bool(all_match),
        'formula_real': 'Re[χ] = a₀[P_R - (P_G + P_B)/2]',
        'formula_imag': 'Im[χ] = a₀(√3/2)(P_G - P_B)',
        'points': results
    }


def test_cube_roots_identity():
    """
    Test 9: Verify cube roots of unity sum to zero
    1 + e^{i2π/3} + e^{i4π/3} = 0
    """
    omega = np.exp(2j * np.pi / 3)
    omega2 = np.exp(4j * np.pi / 3)

    cube_sum = 1 + omega + omega2
    magnitude = abs(cube_sum)

    # Also verify ω³ = 1
    omega_cubed = omega**3

    return {
        'test': 'cube_roots_identity',
        'passed': bool(magnitude < 1e-14 and abs(omega_cubed - 1) < 1e-14),
        'sum': {'real': float(cube_sum.real), 'imag': float(cube_sum.imag)},
        'sum_magnitude': float(magnitude),
        'omega': {'real': float(omega.real), 'imag': float(omega.imag)},
        'omega_squared': {'real': float(omega2.real), 'imag': float(omega2.imag)},
        'omega_cubed': {'real': float(omega_cubed.real), 'imag': float(omega_cubed.imag)},
        'omega_cubed_is_one': bool(abs(omega_cubed - 1) < 1e-14)
    }


def test_coherent_vs_incoherent_energy():
    """
    Test 10: Verify distinction between |χ_total|² and ρ = Σ|a_c|²
    At center: |χ_total|² = 0, but ρ > 0
    Off center: |χ_total|² ≠ ρ in general
    """
    origin = np.array([0.0, 0.0, 0.0])
    off_center = np.array([0.2, 0.1, 0.3])

    # At center
    chi_center = total_chiral_field(origin)
    chi_sq_center = abs(chi_center)**2
    rho_center = energy_density(origin)

    # Off center
    chi_off = total_chiral_field(off_center)
    chi_sq_off = abs(chi_off)**2
    rho_off = energy_density(off_center)

    # They should be different (chi_sq includes interference)
    diff_center = abs(chi_sq_center - rho_center)
    diff_off = abs(chi_sq_off - rho_off)

    return {
        'test': 'coherent_vs_incoherent_energy',
        'passed': bool(chi_sq_center < 1e-14 and rho_center > 0 and diff_off > 1e-10),
        'center': {
            'chi_sq': float(chi_sq_center),
            'rho': float(rho_center),
            'difference': float(diff_center),
            'note': 'At center: χ² = 0 (destructive interference), ρ > 0 (energy conserved)'
        },
        'off_center': {
            'point': off_center.tolist(),
            'chi_sq': float(chi_sq_off),
            'rho': float(rho_off),
            'difference': float(diff_off),
            'ratio_chi_sq_to_rho': float(chi_sq_off / rho_off) if rho_off > 0 else None
        }
    }


def test_gradient_formula():
    """
    Test 11: Verify gradient formula ∇χ = -2a₀ Σ_c [(x-x_c)e^{iφ_c}]/[(|x-x_c|²+ε²)²]
    """
    test_points = [
        np.array([0.0, 0.0, 0.0]),
        np.array([0.1, 0.2, 0.3]),
    ]

    results = []
    all_match = True
    h = 1e-7  # for numerical differentiation

    for pt in test_points:
        # Analytical gradient
        grad_analytical = gradient_chiral_field(pt)

        # Numerical gradient
        grad_numerical = np.zeros(3, dtype=complex)
        for i in range(3):
            pt_plus = pt.copy()
            pt_minus = pt.copy()
            pt_plus[i] += h
            pt_minus[i] -= h

            chi_plus = total_chiral_field(pt_plus)
            chi_minus = total_chiral_field(pt_minus)
            grad_numerical[i] = (chi_plus - chi_minus) / (2 * h)

        error = np.sqrt(np.sum(np.abs(grad_analytical - grad_numerical)**2))
        matches = error < 1e-5  # Numerical differentiation has limited precision

        if not matches:
            all_match = False

        results.append({
            'point': pt.tolist(),
            'analytical_magnitude': float(np.sqrt(np.sum(np.abs(grad_analytical)**2))),
            'numerical_magnitude': float(np.sqrt(np.sum(np.abs(grad_numerical)**2))),
            'error': float(error),
            'matches': bool(matches)
        })

    return {
        'test': 'gradient_formula',
        'passed': bool(all_match),
        'points': results
    }


def test_scaling_with_epsilon():
    """
    Test 12: Verify energy scaling E_total ~ 1/ε
    """
    epsilons = [0.1, 0.2, 0.5, 1.0]
    energies = []

    for eps in epsilons:
        # Compute integral for single source
        def integrand(r):
            return r**2 / (r**2 + eps**2)**2

        numerical, _ = quad(integrand, 0, 10.0)
        energies.append(4 * np.pi * numerical)

    # Check 1/ε scaling
    # E * ε should be approximately constant
    products = [E * eps for E, eps in zip(energies, epsilons)]
    mean_product = np.mean(products)
    max_deviation = max(abs(p - mean_product) / mean_product for p in products)

    return {
        'test': 'scaling_with_epsilon',
        'passed': bool(max_deviation < 0.1),  # Allow 10% deviation
        'epsilons': epsilons,
        'energies': [float(E) for E in energies],
        'products_E_times_epsilon': [float(p) for p in products],
        'mean_product': float(mean_product),
        'max_relative_deviation': float(max_deviation),
        'note': 'E_total ~ 1/ε (products should be constant)'
    }


# =============================================================================
# Main Verification
# =============================================================================

def run_all_tests():
    """Run all verification tests and return results."""
    tests = [
        test_superposition_formula,
        test_energy_density_positive,
        test_center_node,
        test_alternative_form,
        test_nonzero_gradient_at_center,
        test_energy_at_special_points,
        test_energy_integral_convergence,
        test_real_imaginary_parts,
        test_cube_roots_identity,
        test_coherent_vs_incoherent_energy,
        test_gradient_formula,
        test_scaling_with_epsilon,
    ]

    results = []
    passed_count = 0

    for test_func in tests:
        try:
            result = test_func()
            results.append(result)
            if result.get('passed', False):
                passed_count += 1
                status = "✓ PASSED"
            else:
                status = "✗ FAILED"
            print(f"  {status}: {result['test']}")
        except Exception as e:
            error_result = {
                'test': test_func.__name__,
                'passed': False,
                'error': str(e)
            }
            results.append(error_result)
            print(f"  ✗ ERROR: {test_func.__name__}: {e}")

    return {
        'theorem': '0.2.1',
        'title': 'Total Field from Superposition',
        'parameters': {
            'epsilon': float(EPSILON),
            'a0': float(A0)
        },
        'all_passed': passed_count == len(tests),
        'passed_count': passed_count,
        'total_count': len(tests),
        'results': results
    }


def main():
    print("=" * 70)
    print("Numerical Verification: Theorem 0.2.1")
    print("Total Field from Superposition")
    print("=" * 70)
    print(f"\nParameters:")
    print(f"  ε = {EPSILON}")
    print(f"  a_0 = {A0}")
    print()
    print("Running tests...")
    print()

    results = run_all_tests()

    print()
    print("=" * 70)
    if results['all_passed']:
        print("ALL TESTS PASSED - Theorem 0.2.1 numerically verified!")
    else:
        print(f"SOME TESTS FAILED: {results['passed_count']}/{results['total_count']} passed")
    print("=" * 70)

    # Save results to JSON
    output_file = 'theorem_0_2_1_results.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {output_file}")

    return 0 if results['all_passed'] else 1


if __name__ == "__main__":
    sys.exit(main())
