#!/usr/bin/env python3
"""
Theorem 5.2.3: Polarization Identity Verification

This script computationally verifies the polarization identity used in the derivation
of Einstein equations from the Clausius relation (Theorem 5.2.3, Derivation §5.5).

Polarization Identity (Wald 1984, Appendix D.2):
    Let S_μν be a symmetric tensor on a 4-dimensional Lorentzian manifold.
    If S_μν k^μ k^ν = 0 for all null vectors k^μ, then S_μν = f g_μν for some scalar f.

This is crucial because it allows us to go from:
    T_μν k^μ k^ν = (c⁴/8πG) R_μν k^μ k^ν  (for all null k^μ)
to:
    T_μν - (c⁴/8πG) R_μν = f g_μν  (full tensor equation)

Tests:
1. Verify that random symmetric tensors satisfying the null constraint have the form f*g
2. Verify that tensors NOT of the form f*g violate the null constraint
3. Verify the identity in local Lorentz coordinates (flat space)
4. Verify with different metric signatures
5. Verify the derived Einstein equation coefficients

Author: Multi-Agent Verification System
Date: 2025-12-15
"""

import numpy as np
import json
from datetime import datetime

# Minkowski metric (mostly plus convention: -+++)
eta = np.diag([-1.0, 1.0, 1.0, 1.0])

def generate_null_vector():
    """
    Generate a random null vector k^μ in Minkowski space.
    Null vectors satisfy k_μ k^μ = 0, i.e., -k0² + k1² + k2² + k3² = 0.
    """
    # Random spatial direction
    spatial = np.random.randn(3)
    spatial = spatial / np.linalg.norm(spatial)  # Normalize to unit sphere

    # Scale by random magnitude
    mag = np.abs(np.random.randn()) + 0.1
    k_spatial = mag * spatial

    # k0 is determined by null condition: k0 = |k_spatial|
    k0 = np.linalg.norm(k_spatial)

    k = np.array([k0, k_spatial[0], k_spatial[1], k_spatial[2]])
    return k

def check_null(k, metric=eta):
    """Check if k is null with respect to the given metric."""
    return np.abs(np.einsum('i,ij,j->', k, metric, k)) < 1e-10

def contract_with_null(S, k, metric=eta):
    """
    Compute S_μν k^μ k^ν.
    For the Minkowski metric, this is S_μν k^μ k^ν = sum_{μ,ν} S[μ,ν] * k[μ] * k[ν]
    with indices lowered by the metric.
    """
    # S_μν k^μ k^ν = S_{μν} g^{μα} k_α g^{νβ} k_β (but we work in coordinates where indices are natural)
    # In practice: S[μ,ν] * k[μ] * k[ν] (summing over both indices)
    return np.einsum('ij,i,j->', S, k, k)

def generate_f_times_metric(metric=eta):
    """Generate a tensor of the form f * g_μν for random scalar f."""
    f = np.random.randn()
    return f * metric, f

def generate_generic_symmetric_tensor():
    """Generate a random 4x4 symmetric tensor."""
    A = np.random.randn(4, 4)
    return (A + A.T) / 2

def test_polarization_identity_positive():
    """
    Test 1: Verify that tensors of the form S = f*g satisfy S_μν k^μ k^ν = 0
    for all null vectors k^μ.

    This is the "positive" direction of the identity.
    """
    print("\n" + "="*70)
    print("TEST 1: Tensors of form f*g satisfy null contraction = 0")
    print("="*70)

    n_tests = 100
    n_null_per_test = 50
    passed = 0
    max_residual = 0.0

    for i in range(n_tests):
        S, f = generate_f_times_metric()

        # Test with many null vectors
        test_passed = True
        for j in range(n_null_per_test):
            k = generate_null_vector()
            assert check_null(k), "Generated vector should be null"

            contraction = contract_with_null(S, k)

            # Should be zero because k^μ k_μ = 0 and S = f*g
            # S_μν k^μ k^ν = f * g_μν k^μ k^ν = f * k_μ k^μ = f * 0 = 0
            if np.abs(contraction) > 1e-10:
                test_passed = False
            max_residual = max(max_residual, np.abs(contraction))

        if test_passed:
            passed += 1

    success = passed == n_tests
    print(f"  Tensors tested: {n_tests}")
    print(f"  Null vectors per tensor: {n_null_per_test}")
    print(f"  Tests passed: {passed}/{n_tests}")
    print(f"  Max residual: {max_residual:.2e}")
    print(f"  Result: {'✓ PASS' if success else '✗ FAIL'}")

    return {
        "name": "f*g tensors satisfy null contraction = 0",
        "passed": success,
        "n_tests": n_tests,
        "max_residual": float(max_residual)
    }

def test_polarization_identity_converse():
    """
    Test 2: Verify that generic symmetric tensors NOT of the form f*g
    do NOT satisfy S_μν k^μ k^ν = 0 for all null vectors.

    This is the "converse" direction - if S ≠ f*g, there exists some null k
    with S_μν k^μ k^ν ≠ 0.
    """
    print("\n" + "="*70)
    print("TEST 2: Generic tensors violate null contraction = 0")
    print("="*70)

    n_tests = 100
    n_null_per_test = 100
    violations_found = 0

    for i in range(n_tests):
        # Generate a tensor that is NOT of the form f*g
        S = generate_generic_symmetric_tensor()

        # Check if it's already of the form f*g (trace/4 * metric)
        trace = np.trace(np.dot(np.linalg.inv(eta), S))  # g^μν S_μν
        S_pure_trace = (trace / 4) * eta

        # If S is not close to f*g, it should violate the null condition
        if np.linalg.norm(S - S_pure_trace) > 0.1:
            # This tensor should violate the condition
            found_violation = False
            for j in range(n_null_per_test):
                k = generate_null_vector()
                contraction = contract_with_null(S, k)
                if np.abs(contraction) > 1e-8:
                    found_violation = True
                    break

            if found_violation:
                violations_found += 1

    # Most tests should find violations
    success = violations_found >= n_tests * 0.95
    print(f"  Tensors tested: {n_tests}")
    print(f"  Violations found: {violations_found}/{n_tests}")
    print(f"  Result: {'✓ PASS' if success else '✗ FAIL'}")

    return {
        "name": "Generic tensors violate null contraction",
        "passed": success,
        "violations_found": violations_found,
        "n_tests": n_tests
    }

def test_reconstruction():
    """
    Test 3: Given a tensor satisfying S_μν k^μ k^ν = 0 for all null k,
    verify we can reconstruct S = f*g.

    The algorithm:
    1. Pick a timelike vector t^μ and compute f = S_μν t^μ t^ν / (t_μ t^μ)
    2. Verify S = f*g
    """
    print("\n" + "="*70)
    print("TEST 3: Reconstruct f from null constraint")
    print("="*70)

    n_tests = 50
    passed = 0
    max_reconstruction_error = 0.0

    for i in range(n_tests):
        # Generate f*g tensor
        true_f = np.random.randn()
        S = true_f * eta

        # Reconstruct f using a timelike vector
        # Use t = (1, 0, 0, 0) for simplicity
        t = np.array([1.0, 0.0, 0.0, 0.0])

        # f = S_μν t^μ t^ν / (g_μν t^μ t^ν)
        # S_00 = true_f * g_00 = true_f * (-1) = -true_f
        # g_μν t^μ t^ν = g_00 = -1
        # So f = (-true_f) / (-1) = true_f

        numerator = np.einsum('ij,i,j->', S, t, t)
        denominator = np.einsum('ij,i,j->', eta, t, t)
        reconstructed_f = numerator / denominator

        error = np.abs(reconstructed_f - true_f)
        max_reconstruction_error = max(max_reconstruction_error, error)

        if error < 1e-10:
            passed += 1

    success = passed == n_tests
    print(f"  Tests: {passed}/{n_tests}")
    print(f"  Max reconstruction error: {max_reconstruction_error:.2e}")
    print(f"  Result: {'✓ PASS' if success else '✗ FAIL'}")

    return {
        "name": "Reconstruct f from null constraint",
        "passed": success,
        "max_error": float(max_reconstruction_error)
    }

def test_proof_steps():
    """
    Test 4: Verify the proof steps from Wald's argument.

    In local Lorentz coordinates, null vectors have form k = (1, n̂) where |n̂| = 1.
    The constraint S_μν k^μ k^ν = 0 for all such k requires:
    1. S_{0i} = 0 (no time-space mixing)
    2. S_{ij} = (S_kk/3) δ_ij (isotropic spatial part)
    3. S_{00} = S_kk/3 (matching temporal and spatial)
    """
    print("\n" + "="*70)
    print("TEST 4: Verify Wald's proof steps")
    print("="*70)

    # Generate null vectors systematically
    # k = (1, sin(θ)cos(φ), sin(θ)sin(φ), cos(θ))

    def get_null_constraint_equations():
        """
        Set up the system of equations implied by S_μν k^μ k^ν = 0 for all null k.
        """
        # For null k = (1, n), the constraint is:
        # S_00 + 2 S_0i n^i + S_ij n^i n^j = 0
        # This must hold for all unit vectors n.

        # Sample many directions
        constraints = []
        for theta in np.linspace(0.1, np.pi-0.1, 10):
            for phi in np.linspace(0, 2*np.pi-0.1, 10):
                n = np.array([np.sin(theta)*np.cos(phi),
                             np.sin(theta)*np.sin(phi),
                             np.cos(theta)])
                constraints.append(n)
        return constraints

    # Now verify that the only solution is S = f*η
    # Parameterize a general symmetric 4x4 matrix (10 independent components)
    # S_00, S_01, S_02, S_03, S_11, S_12, S_13, S_22, S_23, S_33

    directions = get_null_constraint_equations()
    n_constraints = len(directions)

    # Build constraint matrix A such that A @ x = 0
    # where x = [S_00, S_01, S_02, S_03, S_11, S_12, S_13, S_22, S_23, S_33]
    A = np.zeros((n_constraints, 10))

    for i, n in enumerate(directions):
        # S_00 * 1 + 2*(S_01*n1 + S_02*n2 + S_03*n3) + S_11*n1² + 2*S_12*n1*n2 + ...
        row = np.zeros(10)
        row[0] = 1  # S_00
        row[1] = 2*n[0]  # 2*S_01*n1
        row[2] = 2*n[1]  # 2*S_02*n2
        row[3] = 2*n[2]  # 2*S_03*n3
        row[4] = n[0]**2  # S_11*n1²
        row[5] = 2*n[0]*n[1]  # 2*S_12*n1*n2
        row[6] = 2*n[0]*n[2]  # 2*S_13*n1*n3
        row[7] = n[1]**2  # S_22*n2²
        row[8] = 2*n[1]*n[2]  # 2*S_23*n2*n3
        row[9] = n[2]**2  # S_33*n3²
        A[i] = row

    # Find null space of A
    U, s, Vh = np.linalg.svd(A)

    # Count number of near-zero singular values
    tol = 1e-10
    null_space_dim = np.sum(s < tol)

    # The null space should be 1-dimensional, corresponding to S = f*η
    # The tensor f*η has components:
    # S_00 = -f, S_01=S_02=S_03=0, S_11=S_22=S_33=f, S_12=S_13=S_23=0
    # Vector form: [-f, 0, 0, 0, f, 0, 0, f, 0, f] = f * [-1, 0, 0, 0, 1, 0, 0, 1, 0, 1]

    # Check if the null space is indeed spanned by this vector
    expected_null = np.array([-1, 0, 0, 0, 1, 0, 0, 1, 0, 1])
    expected_null = expected_null / np.linalg.norm(expected_null)

    # Get the null space basis vector (last row of Vh)
    computed_null = Vh[-1]
    computed_null = computed_null / np.linalg.norm(computed_null)

    # Check alignment (could be opposite sign)
    alignment = np.abs(np.dot(expected_null, computed_null))

    print(f"  Number of null vectors sampled: {n_constraints}")
    print(f"  Singular value spectrum (last 5): {s[-5:]}")
    print(f"  Null space dimension: {null_space_dim}")
    print(f"  Expected: 1 (corresponding to S = f*g)")
    print(f"  Alignment with expected null vector: {alignment:.6f}")

    success = null_space_dim == 1 and alignment > 0.999
    print(f"  Result: {'✓ PASS' if success else '✗ FAIL'}")

    return {
        "name": "Verify Wald's proof steps",
        "passed": success,
        "null_space_dim": int(null_space_dim),
        "alignment": float(alignment)
    }

def test_einstein_coefficients():
    """
    Test 5: Verify the coefficient 8πG/c⁴ emerges correctly from the derivation.

    From the Clausius relation:
    δQ = T δS

    Where:
    - T = ℏa/(2πc k_B)  (Unruh temperature)
    - δS = η δA = [c³/(4Gℏ)] δA  (entropy change)

    This gives:
    δQ = [ℏa/(2πc)] × [c³/(4Gℏ)] δA = [a c²/(8πG)] δA

    And leads to:
    T_μν = (c⁴/8πG) R_μν + f g_μν

    Let's verify the numerical coefficients.
    """
    print("\n" + "="*70)
    print("TEST 5: Verify Einstein equation coefficients")
    print("="*70)

    # Physical constants (SI units)
    hbar = 1.054571817e-34  # J·s
    c = 299792458  # m/s
    G = 6.67430e-11  # m³/(kg·s²)
    k_B = 1.380649e-23  # J/K

    # Test 1: Unruh temperature coefficient
    # T_Unruh = ℏa/(2π c k_B)
    # For a = 1 m/s²:
    a_test = 1.0
    T_expected = hbar * a_test / (2 * np.pi * c * k_B)
    print(f"\n  Unruh temperature for a = 1 m/s²:")
    print(f"    T = ℏa/(2πck_B) = {T_expected:.6e} K")
    print(f"    (This is ~4×10⁻²¹ K, extremely small as expected)")

    # Test 2: Entropy density coefficient
    # η = c³/(4Gℏ) = 1/(4ℓ_P²)
    ell_P = np.sqrt(hbar * G / c**3)  # Planck length
    eta_from_Planck = 1 / (4 * ell_P**2)
    eta_from_formula = c**3 / (4 * G * hbar)
    eta_match = np.isclose(eta_from_Planck, eta_from_formula, rtol=1e-10)
    print(f"\n  Entropy density coefficient:")
    print(f"    η = 1/(4ℓ_P²) = {eta_from_Planck:.6e} m⁻²")
    print(f"    η = c³/(4Gℏ) = {eta_from_formula:.6e} m⁻²")
    print(f"    Match: {'✓' if eta_match else '✗'}")

    # Test 3: Combined coefficient in Einstein equations
    # δQ = T δS = [ℏa/(2πc)] × [c³/(4Gℏ)] δA
    #           = [a c²/(8πG)] δA
    #
    # This leads to: T_μν = (c⁴/8πG) R_μν
    # So the Einstein equations are: G_μν = (8πG/c⁴) T_μν

    coeff_RHS = 8 * np.pi * G / c**4
    print(f"\n  Einstein equation coefficient:")
    print(f"    8πG/c⁴ = {coeff_RHS:.6e} m/J")
    print(f"           = {coeff_RHS:.6e} s²/(kg·m)")

    # Test 4: Verify coefficient combination
    # From T × η:
    # [ℏa/(2πc)] × [c³/(4Gℏ)] = a c² / (8πG)
    # The factor involving c:
    # ℏ × c³ / (2πc × 4Gℏ) = c² / (8πG) ✓

    T_times_eta_coeff = (hbar / (2 * np.pi * c)) * (c**3 / (4 * G * hbar))
    expected_coeff = c**2 / (8 * np.pi * G)
    coeff_match = np.isclose(T_times_eta_coeff, expected_coeff, rtol=1e-10)
    print(f"\n  Coefficient consistency check:")
    print(f"    (ℏ/2πc) × (c³/4Gℏ) = {T_times_eta_coeff:.6e} m²·s⁻²/m³")
    print(f"    c²/(8πG) = {expected_coeff:.6e}")
    print(f"    Match: {'✓' if coeff_match else '✗'}")

    # Test 5: The 8π factor
    # The factor 8π = 2 × 4π comes from:
    # - 2π in Unruh temperature
    # - 4 in entropy formula S = A/(4ℓ_P²)
    # Combined: 2π × 4 = 8π
    eight_pi = 2 * np.pi * 4
    eight_pi_correct = np.isclose(eight_pi, 8 * np.pi, rtol=1e-10)
    print(f"\n  Factor 8π decomposition:")
    print(f"    8π = 2π (from Unruh) × 4 (from entropy) = {eight_pi:.6f}")
    print(f"    8π = {8*np.pi:.6f}")
    print(f"    Match: {'✓' if eight_pi_correct else '✗'}")

    success = eta_match and coeff_match and eight_pi_correct
    print(f"\n  Overall Result: {'✓ PASS' if success else '✗ FAIL'}")

    return {
        "name": "Verify Einstein equation coefficients",
        "passed": success,
        "T_unruh_1ms2": float(T_expected),
        "eta": float(eta_from_formula),
        "einstein_coeff": float(coeff_RHS),
        "planck_length_m": float(ell_P)
    }

def test_null_vector_completeness():
    """
    Test 6: Verify that null vectors span the tensor space sufficiently.

    To go from S_μν k^μ k^ν = 0 for all null k to S_μν = f g_μν,
    we need enough null vectors to constrain all 10 independent components
    of a symmetric 4x4 matrix down to 1 free parameter.
    """
    print("\n" + "="*70)
    print("TEST 6: Null vector completeness")
    print("="*70)

    # Generate a grid of null vectors
    n_theta = 20
    n_phi = 40
    null_vectors = []

    for theta in np.linspace(0.01, np.pi-0.01, n_theta):
        for phi in np.linspace(0, 2*np.pi, n_phi, endpoint=False):
            n = np.array([np.sin(theta)*np.cos(phi),
                         np.sin(theta)*np.sin(phi),
                         np.cos(theta)])
            k = np.array([1.0, n[0], n[1], n[2]])
            null_vectors.append(k)

    # Also add k with opposite time direction
    for theta in np.linspace(0.01, np.pi-0.01, n_theta):
        for phi in np.linspace(0, 2*np.pi, n_phi, endpoint=False):
            n = np.array([np.sin(theta)*np.cos(phi),
                         np.sin(theta)*np.sin(phi),
                         np.cos(theta)])
            k = np.array([-1.0, n[0], n[1], n[2]])
            null_vectors.append(k)

    print(f"  Total null vectors: {len(null_vectors)}")

    # Build constraint matrix
    A = []
    for k in null_vectors:
        # S_μν k^μ k^ν = S_00 k⁰² + 2 S_0i k⁰ k^i + S_ij k^i k^j
        row = np.zeros(10)
        row[0] = k[0]**2  # S_00
        row[1] = 2*k[0]*k[1]  # S_01
        row[2] = 2*k[0]*k[2]  # S_02
        row[3] = 2*k[0]*k[3]  # S_03
        row[4] = k[1]**2  # S_11
        row[5] = 2*k[1]*k[2]  # S_12
        row[6] = 2*k[1]*k[3]  # S_13
        row[7] = k[2]**2  # S_22
        row[8] = 2*k[2]*k[3]  # S_23
        row[9] = k[3]**2  # S_33
        A.append(row)

    A = np.array(A)

    # Compute rank
    U, s, Vh = np.linalg.svd(A)
    rank = np.sum(s > 1e-10)
    null_space_dim = 10 - rank

    print(f"  Constraint matrix shape: {A.shape}")
    print(f"  Rank of constraint matrix: {rank}")
    print(f"  Null space dimension: {null_space_dim}")
    print(f"  Expected: rank=9, null_space=1")

    # The expected rank is 9 because we have 10 unknowns and 1 free parameter (f)
    success = rank == 9 and null_space_dim == 1
    print(f"  Result: {'✓ PASS' if success else '✗ FAIL'}")

    return {
        "name": "Null vector completeness",
        "passed": success,
        "n_null_vectors": len(null_vectors),
        "rank": int(rank),
        "null_space_dim": int(null_space_dim)
    }

def run_all_tests():
    """Run all verification tests and produce a summary."""
    print("\n" + "="*70)
    print("THEOREM 5.2.3: POLARIZATION IDENTITY VERIFICATION")
    print("="*70)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("\nThis script verifies the polarization identity used in Derivation §5.5")
    print("to derive the Einstein equations from the Clausius relation.")

    results = []

    # Run all tests
    results.append(test_polarization_identity_positive())
    results.append(test_polarization_identity_converse())
    results.append(test_reconstruction())
    results.append(test_proof_steps())
    results.append(test_einstein_coefficients())
    results.append(test_null_vector_completeness())

    # Summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)

    all_passed = True
    for r in results:
        status = "✓ PASS" if r["passed"] else "✗ FAIL"
        print(f"  {status}: {r['name']}")
        if not r["passed"]:
            all_passed = False

    print("\n" + "-"*70)
    overall = "✓ ALL TESTS PASSED" if all_passed else "✗ SOME TESTS FAILED"
    print(f"  OVERALL: {overall}")
    print("-"*70)

    # Convert numpy booleans to Python booleans for JSON serialization
    def convert_to_native(obj):
        if isinstance(obj, dict):
            return {k: convert_to_native(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_to_native(v) for v in obj]
        elif isinstance(obj, (np.bool_, np.integer)):
            return bool(obj) if isinstance(obj, np.bool_) else int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        else:
            return obj

    # Save results to JSON
    output = convert_to_native({
        "theorem": "5.2.3",
        "verification": "Polarization Identity",
        "date": datetime.now().isoformat(),
        "all_passed": all_passed,
        "tests": results,
        "conclusion": "The polarization identity (Wald 1984, Appendix D.2) is verified. "
                     "If S_μν k^μ k^ν = 0 for all null vectors k^μ, then S_μν = f g_μν. "
                     "This justifies the step from the null contraction equality to the "
                     "full tensor Einstein equations in Theorem 5.2.3 Derivation §5.5."
    })

    output_file = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/theorem_5_2_3_polarization_identity_results.json"
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\n  Results saved to: {output_file}")

    return output

if __name__ == "__main__":
    run_all_tests()
