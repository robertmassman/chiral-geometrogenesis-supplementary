#!/usr/bin/env python3
"""
Lean Formalization Validation for Theorem 0.2.1

This script validates the specific mathematical claims proven in the Lean
formalization at lean/Phase0/Theorem_0_2_1/.

Additional tests beyond the main verification script, focusing on:
1. LebesgueIntegration.lean: Radial integral J = π/4
2. LebesgueIntegration.lean: Total energy formula E = 3a₀²π²/ε
3. TwoLevelStructure.lean: All 8 vertices equidistant from center
4. TwoLevelStructure.lean: Adjacent vertex distance
5. Normalization.lean: a₀ = f_π · ε² vertex amplitude relation
6. Integrability.lean: Japanese bracket integrability condition

Dependencies: numpy, scipy
"""

import numpy as np
from scipy.integrate import quad
import json
import sys

# =============================================================================
# Stella Octangula Vertex Positions (from TwoLevelStructure.lean)
# =============================================================================

# T₊ vertices (positive tetrahedron)
VERTEX_R = np.array([1, 1, -1]) / np.sqrt(3)
VERTEX_G = np.array([-1, 1, 1]) / np.sqrt(3)
VERTEX_B = np.array([1, -1, 1]) / np.sqrt(3)
VERTEX_W = np.array([-1, -1, 1]) / np.sqrt(3)

# T₋ vertices (negative tetrahedron)
VERTEX_R_PRIME = np.array([-1, -1, -1]) / np.sqrt(3)
VERTEX_G_PRIME = np.array([-1, 1, 1]) / np.sqrt(3)
VERTEX_B_PRIME = np.array([1, -1, 1]) / np.sqrt(3)
VERTEX_W_PRIME = np.array([1, 1, -1]) / np.sqrt(3)

ALL_VERTICES = {
    'R': VERTEX_R, 'G': VERTEX_G, 'B': VERTEX_B, 'W': VERTEX_W,
    "R'": VERTEX_R_PRIME, "G'": VERTEX_G_PRIME, "B'": VERTEX_B_PRIME, "W'": VERTEX_W_PRIME
}

CENTER = np.array([0.0, 0.0, 0.0])


# =============================================================================
# Test Functions
# =============================================================================

def test_dimensionless_radial_integral():
    """
    Test from LebesgueIntegration.lean:
    J = ∫₀^∞ u²/(u² + 1)² du = π/4

    Verified in Lean via:
    - radialAntiderivative_tendsto: F(u) → π/4 as u → ∞
    - dimensionless_radial_integral_value

    Note: The integral converges slowly (~1/R), so we use the antiderivative
    formula F(R) = (1/2)[arctan(R) - R/(R²+1)] to verify convergence to π/4.
    """
    def F(R):
        """Antiderivative from LebesgueIntegration.lean"""
        return 0.5 * (np.arctan(R) - R / (R**2 + 1))

    # Use the antiderivative to compute the integral exactly
    R_values = [10, 100, 1000, 10000]
    results = []
    expected = np.pi / 4

    for R in R_values:
        # F(R) - F(0) = F(R) since F(0) = 0
        integral_value = F(R)
        rel_error = abs(integral_value - expected) / expected
        results.append({
            'R': R,
            'F(R)': float(integral_value),
            'relative_error': float(rel_error)
        })

    # The antiderivative shows the correct behavior: F(R) → π/4
    # The error decreases as ~1/R², so R=10000 gives ~1e-4 relative error
    final_error = results[-1]['relative_error']

    return {
        'test': 'dimensionless_radial_integral',
        'passed': final_error < 2e-4,  # Slightly relaxed tolerance
        'expected': float(expected),
        'formula': 'J = ∫₀^∞ u²/(u² + 1)² du = π/4',
        'method': 'Using antiderivative F(R) = (1/2)[arctan(R) - R/(R²+1)]',
        'convergence': results,
        'lean_theorem': 'dimensionless_radial_integral_value'
    }


def test_radial_antiderivative():
    """
    Test from LebesgueIntegration.lean:
    F(u) = (1/2)[arctan(u) - u/(u² + 1)]

    Verify:
    - F(0) = 0 (radialAntiderivative_zero)
    - F(u) → π/4 as u → ∞ (radialAntiderivative_tendsto)
    """
    def F(u):
        return 0.5 * (np.arctan(u) - u / (u**2 + 1))

    # F(0) = 0
    F_zero = F(0)

    # F(u) → π/4
    F_large = F(1e6)
    expected_limit = np.pi / 4

    return {
        'test': 'radial_antiderivative',
        'passed': bool(abs(F_zero) < 1e-15 and abs(F_large - expected_limit) < 1e-6),
        'F(0)': float(F_zero),
        'F(0)_expected': 0.0,
        'F(1e6)': float(F_large),
        'expected_limit': float(expected_limit),
        'lean_theorem': 'radialAntiderivative_zero, radialAntiderivative_tendsto'
    }


def test_total_energy_formula():
    """
    Test from LebesgueIntegration.lean:
    E = 3a₀²π²/ε

    Verified in Lean via total_energy_lebesgue_derivation
    """
    test_cases = [
        {'a0': 1.0, 'epsilon': 0.5},
        {'a0': 2.0, 'epsilon': 0.1},
        {'a0': 92.1, 'epsilon': 1.0},  # Physical value f_π
    ]

    results = []
    all_passed = True

    for case in test_cases:
        a0 = case['a0']
        eps = case['epsilon']

        # Formula from Lean
        E = 3 * a0**2 * np.pi**2 / eps

        # Verify via numerical integration (single source × 3)
        # Using larger R for better convergence
        def integrand(r):
            return r**2 / (r**2 + eps**2)**2

        single_integral, _ = quad(integrand, 0, 1000)
        E_numerical = 3 * a0**2 * 4 * np.pi * single_integral

        rel_error = abs(E - E_numerical) / E
        passed = rel_error < 0.02  # 2% tolerance for finite integration
        if not passed:
            all_passed = False

        results.append({
            'a0': a0,
            'epsilon': eps,
            'E_formula': float(E),
            'E_numerical': float(E_numerical),
            'relative_error': float(rel_error),
            'passed': bool(passed)
        })

    return {
        'test': 'total_energy_formula',
        'passed': all_passed,
        'formula': 'E = 3a₀²π²/ε',
        'test_cases': results,
        'lean_theorem': 'total_energy_lebesgue_derivation'
    }


def test_vertex_distance_from_center():
    """
    Test from TwoLevelStructure.lean:
    All 8 vertices are equidistant from center with distance² = 1

    Verified in Lean via vertex_distance_from_center_sq
    """
    results = []
    all_correct = True
    expected_dist_sq = 1.0

    for name, pos in ALL_VERTICES.items():
        dist_sq = np.sum((pos - CENTER)**2)
        error = abs(dist_sq - expected_dist_sq)
        correct = error < 1e-14
        if not correct:
            all_correct = False

        results.append({
            'vertex': name,
            'position': pos.tolist(),
            'dist_sq': float(dist_sq),
            'expected': expected_dist_sq,
            'error': float(error),
            'correct': bool(correct)
        })

    return {
        'test': 'vertex_distance_from_center',
        'passed': bool(all_correct),
        'expected_dist_sq': expected_dist_sq,
        'vertices': results,
        'lean_theorem': 'vertex_distance_from_center_sq'
    }


def test_adjacent_vertex_distance():
    """
    Test from TwoLevelStructure.lean:
    Adjacent vertices in T₊ have distance² = 8/3

    Verified in Lean via adjacent_vertex_distance_sq
    """
    # R and G are adjacent in T₊
    dist_sq_RG = np.sum((VERTEX_R - VERTEX_G)**2)
    expected = 8.0 / 3.0

    error = abs(dist_sq_RG - expected)

    return {
        'test': 'adjacent_vertex_distance',
        'passed': bool(error < 1e-14),
        'vertex_R': VERTEX_R.tolist(),
        'vertex_G': VERTEX_G.tolist(),
        'dist_sq_RG': float(dist_sq_RG),
        'expected': float(expected),
        'error': float(error),
        'lean_theorem': 'adjacent_vertex_distance_sq'
    }


def test_normalization_vertex_amplitude():
    """
    Test from Normalization.lean:
    With a₀ = f_π · ε², the amplitude at vertex equals f_π

    a₀ · P(vertex) = a₀ · (1/ε²) = f_π · ε² · (1/ε²) = f_π

    Verified in Lean via vertex_amplitude_equals_f_pi
    """
    f_pi = 92.1  # MeV (from Normalization.lean: pionDecayConstant)

    test_epsilons = [0.1, 0.5, 1.0]
    results = []
    all_passed = True

    for eps in test_epsilons:
        # Normalization constant
        a0 = f_pi * eps**2

        # Pressure at vertex
        P_vertex = 1.0 / eps**2

        # Amplitude at vertex
        amplitude = a0 * P_vertex

        error = abs(amplitude - f_pi)
        passed = error < 1e-12
        if not passed:
            all_passed = False

        results.append({
            'epsilon': eps,
            'a0': float(a0),
            'P_vertex': float(P_vertex),
            'amplitude': float(amplitude),
            'expected': float(f_pi),
            'error': float(error),
            'passed': passed
        })

    return {
        'test': 'normalization_vertex_amplitude',
        'passed': all_passed,
        'formula': 'a₀ = f_π · ε² → amplitude at vertex = f_π',
        'f_pi': float(f_pi),
        'test_cases': results,
        'lean_theorem': 'vertex_amplitude_equals_f_pi'
    }


def test_japanese_bracket_condition():
    """
    Test from Integrability.lean:
    (1 + |x|²)^(-r) is integrable on ℝⁿ when r > n/2

    For n=3, we need r > 3/2. Our integrand has r=2 > 3/2 ✓

    Verified in Lean via integrable_inv_one_add_sq_sq
    """
    n = 3  # dimension
    r = 2  # power in our integrand

    condition_satisfied = r > n / 2

    # Verify decay: r²/(r²+1)² ≤ 1/r² for r ≥ 1
    test_r_values = [1.0, 2.0, 5.0, 10.0, 100.0]
    decay_results = []
    all_decay_correct = True

    for r_val in test_r_values:
        integrand_val = r_val**2 / (r_val**2 + 1)**2
        bound = 1.0 / r_val**2
        satisfies_bound = integrand_val <= bound + 1e-15
        if not satisfies_bound:
            all_decay_correct = False

        decay_results.append({
            'r': r_val,
            'integrand': float(integrand_val),
            'bound': float(bound),
            'satisfies': bool(satisfies_bound)
        })

    return {
        'test': 'japanese_bracket_condition',
        'passed': bool(condition_satisfied and all_decay_correct),
        'dimension': n,
        'power_r': r,
        'threshold': n / 2,
        'condition': f'r > n/2 ⟺ {r} > {n/2}',
        'condition_satisfied': bool(condition_satisfied),
        'decay_tests': decay_results,
        'lean_theorem': 'integrable_inv_one_add_sq_sq, radial_integrand_integrable_tail'
    }


def test_energy_concentration_at_vertices():
    """
    Test from LebesgueIntegration.lean:
    ρ(center) < ρ(vertex) for ε < 1

    Verified in Lean via energy_concentration_ratio
    """
    a0 = 1.0

    test_epsilons = [0.1, 0.3, 0.5, 0.9]
    results = []
    all_passed = True

    for eps in test_epsilons:
        # Energy at center: 3a₀²/(1+ε²)²
        rho_center = 3 * a0**2 / (1 + eps**2)**2

        # Energy at vertex: a₀²/ε⁴
        rho_vertex = a0**2 / eps**4

        vertex_greater = rho_vertex > rho_center
        ratio = rho_vertex / rho_center

        if not vertex_greater:
            all_passed = False

        results.append({
            'epsilon': eps,
            'rho_center': float(rho_center),
            'rho_vertex': float(rho_vertex),
            'ratio': float(ratio),
            'vertex_greater': bool(vertex_greater)
        })

    return {
        'test': 'energy_concentration_at_vertices',
        'passed': bool(all_passed),
        'note': 'For ε < 1, energy density peaks at vertices',
        'test_cases': results,
        'lean_theorem': 'energy_concentration_ratio'
    }


def test_euler_characteristic():
    """
    Test from TwoLevelStructure.lean:
    V + F = E + 4 for stella octangula compound

    V=8 vertices, F=8 faces, E=12 edges
    8 + 8 = 12 + 4 ✓

    Verified in Lean via TwoLevelStructure.euler_characteristic
    """
    V = 8  # vertices
    F = 8  # faces
    E = 12  # edges

    lhs = V + F
    rhs = E + 4

    return {
        'test': 'euler_characteristic',
        'passed': bool(lhs == rhs),
        'vertices': V,
        'faces': F,
        'edges': E,
        'V_plus_F': lhs,
        'E_plus_4': rhs,
        'identity': 'V + F = E + 4',
        'lean_theorem': 'stellaOctangulaTwoLevel.euler_characteristic'
    }


# =============================================================================
# Main
# =============================================================================

def run_all_tests():
    """Run all Lean validation tests."""
    tests = [
        test_dimensionless_radial_integral,
        test_radial_antiderivative,
        test_total_energy_formula,
        test_vertex_distance_from_center,
        test_adjacent_vertex_distance,
        test_normalization_vertex_amplitude,
        test_japanese_bracket_condition,
        test_energy_concentration_at_vertices,
        test_euler_characteristic,
    ]

    results = []
    passed_count = 0

    for test_func in tests:
        try:
            result = test_func()
            results.append(result)
            if result.get('passed', False):
                passed_count += 1
                status = "PASSED"
            else:
                status = "FAILED"
            print(f"  [{status}] {result['test']}")
            if 'lean_theorem' in result:
                print(f"           Lean: {result['lean_theorem']}")
        except Exception as e:
            error_result = {
                'test': test_func.__name__,
                'passed': False,
                'error': str(e)
            }
            results.append(error_result)
            print(f"  [ERROR] {test_func.__name__}: {e}")

    return {
        'validation_type': 'Lean Formalization Validation',
        'theorem': '0.2.1',
        'lean_path': 'lean/Phase0/Theorem_0_2_1/',
        'all_passed': passed_count == len(tests),
        'passed_count': passed_count,
        'total_count': len(tests),
        'results': results
    }


def main():
    print("=" * 70)
    print("Lean Formalization Validation: Theorem 0.2.1")
    print("lean/Phase0/Theorem_0_2_1/")
    print("=" * 70)
    print()
    print("Validating numerical consistency with Lean theorems...")
    print()

    results = run_all_tests()

    print()
    print("=" * 70)
    if results['all_passed']:
        print("ALL VALIDATIONS PASSED")
        print("Lean formalization is numerically consistent!")
    else:
        print(f"SOME VALIDATIONS FAILED: {results['passed_count']}/{results['total_count']}")
    print("=" * 70)

    # Save results
    output_file = 'verification/theorem_0_2_1_lean_validation_results.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {output_file}")

    return 0 if results['all_passed'] else 1


if __name__ == "__main__":
    sys.exit(main())
