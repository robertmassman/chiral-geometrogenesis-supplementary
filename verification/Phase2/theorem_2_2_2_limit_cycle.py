"""
Theorem 2.2.2: Limit Cycle Existence in the R→G→B Phase System
================================================================
Numerical Verification Script

This script verifies the key claims of Theorem 2.2.2:
1. The system possesses a stable limit cycle (periodic orbit)
2. The limit cycle has period T = 2π/ω
3. Phases remain locked at 120° separation on the cycle
4. Floquet multipliers confirm orbital stability
5. The saddle point structure and separatrix exist
6. Global attraction — almost all initial conditions converge

Reference: docs/proofs/Theorem-2.2.2-Limit-Cycle.md
"""

import numpy as np
from scipy.integrate import odeint, solve_ivp
from scipy.linalg import eigvals
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from typing import Tuple, List, Dict
import json
from datetime import datetime

# ============================================================================
# CONSTANTS
# ============================================================================

ALPHA = 2 * np.pi / 3  # Phase frustration parameter (120°)
TARGET_PHASE_DIFF = 2 * np.pi / 3  # Expected equilibrium phase difference


# ============================================================================
# DYNAMICAL SYSTEM DEFINITIONS
# ============================================================================

def sakaguchi_kuramoto_full(phi: np.ndarray, t: float, omega: float, K: float) -> np.ndarray:
    """
    Full 3-phase Sakaguchi-Kuramoto model (TARGET-SPECIFIC form from Theorem 2.2.2).

    Each coupling term has a phase shift equal to its TARGET phase difference.
    This ensures ALL coupling terms vanish at the 120° equilibrium.

    From Theorem 2.2.2 §1.1:
    dφ_R/dt = ω + (K/2)[sin(φ_G - φ_R - 2π/3) + sin(φ_B - φ_R - 4π/3)]
    dφ_G/dt = ω + (K/2)[sin(φ_R - φ_G + 2π/3) + sin(φ_B - φ_G - 2π/3)]
    dφ_B/dt = ω + (K/2)[sin(φ_R - φ_B + 4π/3) + sin(φ_G - φ_B + 2π/3)]

    Parameters:
        phi: Array [φ_R, φ_G, φ_B] of phase values
        t: Time (unused, for odeint compatibility)
        omega: Natural frequency
        K: Coupling strength

    Returns:
        Array of derivatives [dφ_R/dt, dφ_G/dt, dφ_B/dt]
    """
    phi_R, phi_G, phi_B = phi
    alpha = 2 * np.pi / 3  # 120°

    # Target-specific model: each term vanishes at its target separation
    dphi_R = omega + (K/2) * (
        np.sin(phi_G - phi_R - alpha) +        # Target: φ_G - φ_R = 2π/3
        np.sin(phi_B - phi_R - 2*alpha)        # Target: φ_B - φ_R = 4π/3
    )
    dphi_G = omega + (K/2) * (
        np.sin(phi_R - phi_G + alpha) +        # Target: φ_G - φ_R = 2π/3
        np.sin(phi_B - phi_G - alpha)          # Target: φ_B - φ_G = 2π/3
    )
    dphi_B = omega + (K/2) * (
        np.sin(phi_R - phi_B + 2*alpha) +      # Target: φ_B - φ_R = 4π/3
        np.sin(phi_G - phi_B + alpha)          # Target: φ_B - φ_G = 2π/3
    )

    return np.array([dphi_R, dphi_G, dphi_B])


def phase_difference_dynamics(psi: np.ndarray, t: float, K: float) -> np.ndarray:
    """
    Phase-difference dynamics (reduced 2D system).

    ψ₁ = φ_G - φ_R,  ψ₂ = φ_B - φ_G

    Parameters:
        psi: Array [ψ₁, ψ₂] of phase differences
        t: Time (unused)
        K: Coupling strength

    Returns:
        Array of derivatives [dψ₁/dt, dψ₂/dt]
    """
    psi1, psi2 = psi
    alpha = ALPHA

    # From the symmetric model
    dpsi1 = (K/2) * (
        np.sin(-psi1 - alpha) + np.sin(psi2 - alpha)
        - np.sin(psi1 - alpha) - np.sin(psi1 + psi2 - alpha)
    )

    dpsi2 = (K/2) * (
        np.sin(-psi1 - psi2 - alpha) + np.sin(-psi2 - alpha)
        - np.sin(-psi1 - alpha) - np.sin(psi2 - alpha)
    )

    return np.array([dpsi1, dpsi2])


def compute_jacobian_numerical(psi: np.ndarray, K: float, eps: float = 1e-6) -> np.ndarray:
    """Compute Jacobian matrix numerically at a given point."""
    J = np.zeros((2, 2))
    f0 = phase_difference_dynamics(psi, 0, K)

    for j in range(2):
        psi_plus = psi.copy()
        psi_plus[j] += eps
        f_plus = phase_difference_dynamics(psi_plus, 0, K)
        J[:, j] = (f_plus - f0) / eps

    return J


def torus_distance(psi1: np.ndarray, psi2: np.ndarray) -> float:
    """Compute distance on 2-torus with proper wrapping."""
    diff = psi1 - psi2
    diff = np.mod(diff + np.pi, 2*np.pi) - np.pi
    return np.linalg.norm(diff)


# ============================================================================
# VERIFICATION TESTS
# ============================================================================

def test_1_limit_cycle_existence(K: float = 1.0, omega: float = 1.0) -> Dict:
    """
    Test 1: Verify limit cycle existence.

    The trajectory γ(t) = (ωt, ωt + 2π/3, ωt + 4π/3) should be a periodic solution.

    Key insight: When phases are EXACTLY at 120° separation, ALL coupling terms
    sin(φⱼ - φᵢ - α) = sin(±2π/3 - 2π/3) = sin(0) or sin(-4π/3) = 0
    So dφᵢ/dt = ω exactly on the limit cycle.
    """
    print("\n" + "="*70)
    print("TEST 1: Limit Cycle Existence")
    print("="*70)

    results = {
        "test_name": "Limit Cycle Existence",
        "passed": True,
        "K": K,
        "omega": omega,
        "tolerance": 0.01
    }

    # Start EXACTLY on equilibrium (120° separation)
    phi0 = np.array([0.0, 2*np.pi/3, 4*np.pi/3])

    # Verify the coupling terms vanish at equilibrium
    dphi = sakaguchi_kuramoto_full(phi0, 0, omega, K)
    coupling_contribution = dphi - omega  # Should be zero at equilibrium

    print(f"\n  Parameters: K = {K}, ω = {omega}")
    print(f"\n  At equilibrium φ = (0, 2π/3, 4π/3):")
    print(f"    dφ_R/dt = {dphi[0]:.6f} (expected: ω = {omega})")
    print(f"    dφ_G/dt = {dphi[1]:.6f} (expected: ω = {omega})")
    print(f"    dφ_B/dt = {dphi[2]:.6f} (expected: ω = {omega})")
    print(f"    Coupling contribution: {np.max(np.abs(coupling_contribution)):.2e}")

    # Simulate for several periods
    T_expected = 2 * np.pi / omega
    t_span = np.linspace(0, 10 * T_expected, 2000)
    solution = odeint(sakaguchi_kuramoto_full, phi0, t_span, args=(omega, K))

    # Check that phases maintain 120° separation
    psi1 = (solution[:, 1] - solution[:, 0]) % (2*np.pi)
    psi2 = (solution[:, 2] - solution[:, 1]) % (2*np.pi)

    # Compute deviation from 120°
    psi1_error = np.abs(psi1 - 2*np.pi/3)
    psi2_error = np.abs(psi2 - 2*np.pi/3)

    # Handle wrapping
    psi1_error = np.minimum(psi1_error, 2*np.pi - psi1_error)
    psi2_error = np.minimum(psi2_error, 2*np.pi - psi2_error)

    max_phase_error = max(np.max(psi1_error), np.max(psi2_error))

    print(f"\n  Phase separation analysis (on limit cycle):")
    print(f"    Max |ψ₁ - 2π/3|: {np.degrees(np.max(psi1_error)):.6f}°")
    print(f"    Max |ψ₂ - 2π/3|: {np.degrees(np.max(psi2_error)):.6f}°")

    # Compute actual rotation rate at late times (should equal ω)
    # Use only late-time data where system is on the limit cycle
    late_idx = len(t_span) // 2
    dphi_R = np.gradient(np.unwrap(solution[late_idx:, 0]), t_span[late_idx:])
    mean_rotation_rate = np.mean(dphi_R)

    print(f"\n  Rotation analysis (late time):")
    print(f"    Mean dφ_R/dt: {mean_rotation_rate:.6f}")
    print(f"    Expected (ω): {omega:.6f}")
    print(f"    Error:        {abs(mean_rotation_rate - omega):.6f}")

    # The key test: on the limit cycle, rotation rate should equal ω
    # because coupling terms vanish at 120° separation
    coupling_terms_vanish = np.max(np.abs(coupling_contribution)) < 1e-10
    phase_locked = max_phase_error < results["tolerance"]
    rate_correct = abs(mean_rotation_rate - omega) < 0.01

    results["max_phase_error_rad"] = float(max_phase_error)
    results["mean_rotation_rate"] = float(mean_rotation_rate)
    results["coupling_terms_vanish"] = coupling_terms_vanish
    results["phase_locked"] = phase_locked
    results["rate_correct"] = rate_correct

    passed = phase_locked and coupling_terms_vanish
    results["passed"] = passed

    print(f"\n  {'✓' if phase_locked else '✗'} Phases locked at 120°")
    print(f"  {'✓' if coupling_terms_vanish else '✗'} Coupling terms vanish at equilibrium")
    print(f"  {'✓' if rate_correct else '✗'} Rotation rate = ω")
    print(f"\n  {'✓ PASSED' if passed else '✗ FAILED'}: Limit cycle exists")

    return results


def test_2_period_measurement(K: float = 1.0, omega: float = 1.0) -> Dict:
    """
    Test 2: Verify limit cycle period T = 2π/ω.

    Measure the period by detecting zero-crossings.
    """
    print("\n" + "="*70)
    print("TEST 2: Period Measurement")
    print("="*70)

    results = {
        "test_name": "Period Measurement",
        "passed": True,
        "K": K,
        "omega": omega,
        "tolerance_percent": 1.0
    }

    # Start from arbitrary initial condition, let it settle
    phi0 = np.array([0.0, np.pi/3, np.pi])

    # Settle to limit cycle
    t_settle = np.linspace(0, 50, 1000)
    solution_settle = odeint(sakaguchi_kuramoto_full, phi0, t_settle, args=(omega, K))
    phi_settled = solution_settle[-1]

    # Now measure periods
    t_measure = np.linspace(0, 100, 10000)
    solution = odeint(sakaguchi_kuramoto_full, phi_settled, t_measure, args=(omega, K))

    # Detect zero crossings of phi_R (mod 2π)
    phi_R_wrapped = np.mod(solution[:, 0], 2*np.pi)
    crossings = []

    for i in range(1, len(phi_R_wrapped)):
        # Detect crossing from high to low (wrapping around 2π)
        if phi_R_wrapped[i-1] > 5 and phi_R_wrapped[i] < 1:
            # Interpolate to find exact crossing time
            t_cross = t_measure[i-1] + (t_measure[i] - t_measure[i-1]) * \
                      (2*np.pi - phi_R_wrapped[i-1]) / (phi_R_wrapped[i] + 2*np.pi - phi_R_wrapped[i-1])
            crossings.append(t_cross)

    # Compute periods from consecutive crossings
    periods = np.diff(crossings)

    if len(periods) > 0:
        mean_period = np.mean(periods)
        std_period = np.std(periods)
        expected_period = 2 * np.pi / omega

        rel_error = abs(mean_period - expected_period) / expected_period * 100

        print(f"\n  Parameters: K = {K}, ω = {omega}")
        print(f"\n  Period measurements:")
        print(f"    Number of cycles detected: {len(periods)}")
        print(f"    Mean measured period:      {mean_period:.6f}")
        print(f"    Standard deviation:        {std_period:.6f}")
        print(f"    Expected period (2π/ω):    {expected_period:.6f}")
        print(f"    Relative error:            {rel_error:.4f}%")

        passed = rel_error < results["tolerance_percent"]
        results["passed"] = passed
        results["n_cycles"] = len(periods)
        results["mean_period"] = float(mean_period)
        results["std_period"] = float(std_period)
        results["expected_period"] = float(expected_period)
        results["relative_error_percent"] = float(rel_error)

        print(f"\n  {'✓ PASSED' if passed else '✗ FAILED'}: Period = 2π/ω within {results['tolerance_percent']}%")
    else:
        print("\n  ✗ No cycles detected")
        results["passed"] = False

    return results


def test_3_floquet_multipliers(K: float = 1.0, omega: float = 1.0) -> Dict:
    """
    Test 3: Compute Floquet multipliers for orbital stability.

    For a stable limit cycle, transverse Floquet multipliers should have |μ| < 1.
    """
    print("\n" + "="*70)
    print("TEST 3: Floquet Multipliers (Orbital Stability)")
    print("="*70)

    results = {
        "test_name": "Floquet Multipliers",
        "passed": True,
        "K": K,
        "omega": omega
    }

    # The limit cycle in phase-difference coordinates is a fixed point
    # Floquet multipliers are related to eigenvalues by μ = exp(λT)
    psi_star = np.array([ALPHA, ALPHA])
    J = compute_jacobian_numerical(psi_star, K)
    eigenvalues = np.real(eigvals(J))

    T = 2 * np.pi / omega

    # Compute Floquet multipliers
    floquet_multipliers = np.exp(eigenvalues * T)

    print(f"\n  Parameters: K = {K}, ω = {omega}, T = {T:.4f}")
    print(f"\n  At fixed point (ψ₁*, ψ₂*) = (2π/3, 2π/3):")
    print(f"    Jacobian eigenvalues: λ₁ = {eigenvalues[0]:.6f}, λ₂ = {eigenvalues[1]:.6f}")
    print(f"\n  Floquet multipliers (μ = e^(λT)):")
    print(f"    μ₁ = e^({eigenvalues[0]:.4f} × {T:.4f}) = {floquet_multipliers[0]:.6f}")
    print(f"    μ₂ = e^({eigenvalues[1]:.4f} × {T:.4f}) = {floquet_multipliers[1]:.6f}")

    # Check stability: all transverse multipliers must have |μ| < 1
    stable = all(np.abs(floquet_multipliers) < 1)

    print(f"\n  Orbital stability check:")
    print(f"    |μ₁| = {np.abs(floquet_multipliers[0]):.6f} {'< 1 ✓' if np.abs(floquet_multipliers[0]) < 1 else '≥ 1 ✗'}")
    print(f"    |μ₂| = {np.abs(floquet_multipliers[1]):.6f} {'< 1 ✓' if np.abs(floquet_multipliers[1]) < 1 else '≥ 1 ✗'}")

    results["eigenvalues"] = [float(e) for e in eigenvalues]
    results["floquet_multipliers"] = [float(m) for m in floquet_multipliers]
    results["stable"] = stable
    results["passed"] = stable

    print(f"\n  {'✓ PASSED' if stable else '✗ FAILED'}: Limit cycle is orbitally stable")

    return results


def test_4_fixed_point_classification(K: float = 1.0) -> Dict:
    """
    Test 4: Classify all fixed points in phase-difference space.

    Verify the structure: 2 stable nodes, 1 unstable node, 1 saddle.
    """
    print("\n" + "="*70)
    print("TEST 4: Fixed Point Classification")
    print("="*70)

    results = {
        "test_name": "Fixed Point Classification",
        "passed": True,
        "K": K,
        "fixed_points": []
    }

    # Known fixed points from theorem
    fixed_points = [
        ("FP1", np.array([ALPHA, ALPHA]), "Stable (R→G→B)"),
        ("FP2", np.array([-ALPHA, -ALPHA]), "Stable (R→B→G)"),
        ("FP3", np.array([0, 0]), "Unstable (sync)"),
        ("FP4", np.array([ALPHA, -ALPHA]), "Saddle"),
    ]

    print(f"\n  Coupling strength K = {K}")
    print(f"\n  Fixed Point Analysis:")
    print(f"  {'Name':<6} | {'ψ₁ (deg)':<12} | {'ψ₂ (deg)':<12} | {'λ₁':<12} | {'λ₂':<12} | {'Type':<15}")
    print("  " + "-"*80)

    n_stable = 0
    n_unstable = 0
    n_saddle = 0

    for name, psi, expected_type in fixed_points:
        # Compute Jacobian eigenvalues
        J = compute_jacobian_numerical(psi, K)
        eigs = np.real(eigvals(J))

        # Classify
        if all(e < 0 for e in eigs):
            fp_type = "Stable node"
            n_stable += 1
        elif all(e > 0 for e in eigs):
            fp_type = "Unstable node"
            n_unstable += 1
        else:
            fp_type = "Saddle"
            n_saddle += 1

        psi1_deg = np.degrees(psi[0] % (2*np.pi))
        psi2_deg = np.degrees(psi[1] % (2*np.pi))

        print(f"  {name:<6} | {psi1_deg:<12.2f} | {psi2_deg:<12.2f} | {eigs[0]:<12.6f} | {eigs[1]:<12.6f} | {fp_type:<15}")

        results["fixed_points"].append({
            "name": name,
            "psi": [float(p) for p in psi],
            "eigenvalues": [float(e) for e in eigs],
            "type": fp_type
        })

    print(f"\n  Summary:")
    print(f"    Stable nodes:   {n_stable} (expected: 2)")
    print(f"    Unstable nodes: {n_unstable} (expected: 1)")
    print(f"    Saddles:        {n_saddle} (expected: 1)")

    # Check structure
    correct_structure = (n_stable == 2 and n_unstable == 1 and n_saddle == 1)
    results["n_stable"] = n_stable
    results["n_unstable"] = n_unstable
    results["n_saddle"] = n_saddle
    results["passed"] = correct_structure

    print(f"\n  {'✓ PASSED' if correct_structure else '✗ FAILED'}: Fixed point structure verified")

    return results


def test_5_global_attraction(K: float = 1.0, n_samples: int = 300) -> Dict:
    """
    Test 5: Verify global attraction to limit cycles.

    Almost all initial conditions should converge to one of the two stable fixed points.
    """
    print("\n" + "="*70)
    print("TEST 5: Global Attraction Analysis")
    print("="*70)

    results = {
        "test_name": "Global Attraction",
        "passed": True,
        "K": K,
        "n_samples": n_samples
    }

    # Fixed points
    FP1 = np.array([ALPHA, ALPHA])
    FP2 = np.array([-ALPHA, -ALPHA])

    # Sample initial conditions
    np.random.seed(42)
    psi1_init = np.random.uniform(0, 2*np.pi, n_samples)
    psi2_init = np.random.uniform(0, 2*np.pi, n_samples)

    basin_FP1 = []
    basin_FP2 = []
    other = []

    t_span = np.linspace(0, 150, 1500)

    for i in range(n_samples):
        psi0 = np.array([psi1_init[i], psi2_init[i]])
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))
        psi_final = solution[-1]

        dist_FP1 = torus_distance(psi_final, FP1)
        dist_FP2 = torus_distance(psi_final, FP2)

        threshold = 0.2

        if dist_FP1 < threshold:
            basin_FP1.append(psi0)
        elif dist_FP2 < threshold:
            basin_FP2.append(psi0)
        else:
            other.append(psi0)

    n_FP1 = len(basin_FP1)
    n_FP2 = len(basin_FP2)
    n_other = len(other)
    fraction_converged = (n_FP1 + n_FP2) / n_samples

    print(f"\n  Sampled {n_samples} initial conditions on 𝕋²")
    print(f"\n  Convergence to fixed points:")
    print(f"    FP1 (R→G→B chirality): {n_FP1} ({100*n_FP1/n_samples:.1f}%)")
    print(f"    FP2 (R→B→G chirality): {n_FP2} ({100*n_FP2/n_samples:.1f}%)")
    print(f"    Other/boundary:        {n_other} ({100*n_other/n_samples:.1f}%)")
    print(f"\n  Total converging to stable limit cycles: {100*fraction_converged:.1f}%")

    results["n_FP1"] = n_FP1
    results["n_FP2"] = n_FP2
    results["n_other"] = n_other
    results["fraction_converged"] = float(fraction_converged)

    passed = fraction_converged > 0.98
    results["passed"] = passed

    print(f"\n  {'✓ PASSED' if passed else '✗ FAILED'}: >98% of initial conditions converge to limit cycle")

    return results, np.array(basin_FP1), np.array(basin_FP2)


def test_6_color_neutrality_on_cycle(K: float = 1.0, omega: float = 1.0) -> Dict:
    """
    Test 6: Verify color neutrality is maintained on the limit cycle.

    At all times: e^(iφ_R) + e^(iφ_G) + e^(iφ_B) = 0
    """
    print("\n" + "="*70)
    print("TEST 6: Color Neutrality on Limit Cycle")
    print("="*70)

    results = {
        "test_name": "Color Neutrality",
        "passed": True,
        "K": K,
        "omega": omega,
        "tolerance": 1e-6
    }

    # Start on the limit cycle
    phi0 = np.array([0.0, 2*np.pi/3, 4*np.pi/3])

    T = 2 * np.pi / omega
    t_span = np.linspace(0, 5 * T, 1000)
    solution = odeint(sakaguchi_kuramoto_full, phi0, t_span, args=(omega, K))

    # Compute color sum at each time
    color_sum = np.exp(1j*solution[:, 0]) + np.exp(1j*solution[:, 1]) + np.exp(1j*solution[:, 2])
    magnitudes = np.abs(color_sum)

    max_magnitude = np.max(magnitudes)
    mean_magnitude = np.mean(magnitudes)

    print(f"\n  Parameters: K = {K}, ω = {omega}")
    print(f"\n  Color neutrality: |e^(iφ_R) + e^(iφ_G) + e^(iφ_B)|")
    print(f"    Maximum over 5 periods: {max_magnitude:.2e}")
    print(f"    Mean over 5 periods:    {mean_magnitude:.2e}")
    print(f"    Expected:               0")

    passed = max_magnitude < results["tolerance"]
    results["max_magnitude"] = float(max_magnitude)
    results["mean_magnitude"] = float(mean_magnitude)
    results["passed"] = passed

    print(f"\n  {'✓ PASSED' if passed else '✗ FAILED'}: Color neutrality maintained")

    return results


def test_7_chirality_persistence(K: float = 1.0, omega: float = 1.0) -> Dict:
    """
    Test 7: Verify chirality persists over time.

    Once the system settles into a chirality, it should not spontaneously flip.
    """
    print("\n" + "="*70)
    print("TEST 7: Chirality Persistence")
    print("="*70)

    results = {
        "test_name": "Chirality Persistence",
        "passed": True,
        "K": K,
        "omega": omega
    }

    # Start near FP1 (R→G→B chirality)
    phi0 = np.array([0.0, 2*np.pi/3 + 0.1, 4*np.pi/3 - 0.1])

    # Run for a long time
    t_span = np.linspace(0, 500, 5000)
    solution = odeint(sakaguchi_kuramoto_full, phi0, t_span, args=(omega, K))

    # Track chirality: sign of (φ_G - φ_R) - (φ_B - φ_G)
    # For R→G→B: both should be ~2π/3, so difference is ~0
    # For R→B→G: both should be ~4π/3, so difference is ~0
    psi1 = (solution[:, 1] - solution[:, 0]) % (2*np.pi)
    psi2 = (solution[:, 2] - solution[:, 1]) % (2*np.pi)

    # Determine initial chirality
    FP1 = np.array([ALPHA, ALPHA])
    FP2 = np.array([-ALPHA % (2*np.pi), -ALPHA % (2*np.pi)])

    initial_psi = np.array([psi1[100], psi2[100]])  # After initial transient
    final_psi = np.array([psi1[-1], psi2[-1]])

    dist_FP1_initial = torus_distance(initial_psi, FP1)
    dist_FP2_initial = torus_distance(initial_psi, FP2)
    dist_FP1_final = torus_distance(final_psi, FP1)
    dist_FP2_final = torus_distance(final_psi, FP2)

    initial_chirality = "R→G→B" if dist_FP1_initial < dist_FP2_initial else "R→B→G"
    final_chirality = "R→G→B" if dist_FP1_final < dist_FP2_final else "R→B→G"

    chirality_preserved = (initial_chirality == final_chirality)

    print(f"\n  Parameters: K = {K}, ω = {omega}")
    print(f"  Simulation time: 500 time units")
    print(f"\n  Chirality tracking:")
    print(f"    Initial chirality (t=10): {initial_chirality}")
    print(f"    Final chirality (t=500):  {final_chirality}")
    print(f"    Chirality preserved:      {'Yes ✓' if chirality_preserved else 'No ✗'}")

    results["initial_chirality"] = initial_chirality
    results["final_chirality"] = final_chirality
    results["chirality_preserved"] = chirality_preserved
    results["passed"] = chirality_preserved

    print(f"\n  {'✓ PASSED' if chirality_preserved else '✗ FAILED'}: Chirality is stable")

    return results


# ============================================================================
# PLOTTING FUNCTIONS
# ============================================================================

def plot_limit_cycle_3d(K: float = 1.0, omega: float = 1.0, save_path: str = None):
    """Plot the limit cycle in 3D phase space."""
    fig = plt.figure(figsize=(12, 5))

    # Start from off-equilibrium
    phi0 = np.array([0.0, np.pi/4, np.pi/2])

    T = 2 * np.pi / omega
    t_span = np.linspace(0, 20 * T, 2000)
    solution = odeint(sakaguchi_kuramoto_full, phi0, t_span, args=(omega, K))

    # 3D trajectory
    ax1 = fig.add_subplot(121, projection='3d')

    # Wrap phases to [0, 2π)
    phi_R = solution[:, 0] % (2*np.pi)
    phi_G = solution[:, 1] % (2*np.pi)
    phi_B = solution[:, 2] % (2*np.pi)

    # Color by time
    colors = plt.cm.viridis(np.linspace(0, 1, len(t_span)))
    for i in range(len(t_span)-1):
        ax1.plot3D(phi_R[i:i+2], phi_G[i:i+2], phi_B[i:i+2],
                  color=colors[i], linewidth=0.5)

    ax1.set_xlabel('φ_R (rad)')
    ax1.set_ylabel('φ_G (rad)')
    ax1.set_zlabel('φ_B (rad)')
    ax1.set_title('Trajectory in 3D Phase Space')

    # Phase differences over time
    ax2 = fig.add_subplot(122)
    psi1 = np.degrees((solution[:, 1] - solution[:, 0]) % (2*np.pi))
    psi2 = np.degrees((solution[:, 2] - solution[:, 1]) % (2*np.pi))

    ax2.plot(t_span, psi1, 'b-', label='ψ₁ = φ_G - φ_R', linewidth=1)
    ax2.plot(t_span, psi2, 'r-', label='ψ₂ = φ_B - φ_G', linewidth=1)
    ax2.axhline(y=120, color='k', linestyle='--', alpha=0.5, label='Target: 120°')
    ax2.set_xlabel('Time')
    ax2.set_ylabel('Phase Difference (degrees)')
    ax2.set_title('Convergence to 120° Separation')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim(0, 360)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"  Saved: {save_path}")
    plt.close()


def plot_phase_portrait_with_trajectories(K: float = 1.0, save_path: str = None):
    """Plot phase portrait with sample trajectories."""
    fig, ax = plt.subplots(figsize=(10, 10))

    # Vector field
    n_grid = 20
    psi1_grid = np.linspace(0, 2*np.pi, n_grid)
    psi2_grid = np.linspace(0, 2*np.pi, n_grid)
    PSI1, PSI2 = np.meshgrid(psi1_grid, psi2_grid)

    DPSI1 = np.zeros_like(PSI1)
    DPSI2 = np.zeros_like(PSI2)

    for i in range(n_grid):
        for j in range(n_grid):
            psi = np.array([PSI1[i, j], PSI2[i, j]])
            dpsi = phase_difference_dynamics(psi, 0, K)
            DPSI1[i, j] = dpsi[0]
            DPSI2[i, j] = dpsi[1]

    magnitude = np.sqrt(DPSI1**2 + DPSI2**2)
    magnitude[magnitude == 0] = 1
    DPSI1_norm = DPSI1 / magnitude
    DPSI2_norm = DPSI2 / magnitude

    ax.quiver(np.degrees(PSI1), np.degrees(PSI2), DPSI1_norm, DPSI2_norm,
              magnitude, cmap='viridis', alpha=0.6)

    # Sample trajectories
    np.random.seed(123)
    n_traj = 20
    t_span = np.linspace(0, 50, 500)

    for _ in range(n_traj):
        psi0 = np.random.uniform(0, 2*np.pi, 2)
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))
        ax.plot(np.degrees(solution[:, 0] % (2*np.pi)),
               np.degrees(solution[:, 1] % (2*np.pi)),
               'b-', alpha=0.3, linewidth=0.8)

    # Mark fixed points
    fixed_points = [
        (ALPHA, ALPHA, 'FP1: Stable\n(R→G→B)', 'go'),
        (4*np.pi/3, 4*np.pi/3, 'FP2: Stable\n(R→B→G)', 'go'),
        (0, 0, 'FP3: Unstable', 'ro'),
        (ALPHA, 4*np.pi/3, 'FP4: Saddle', 'yo'),
    ]

    for psi1, psi2, label, marker in fixed_points:
        ax.plot(np.degrees(psi1), np.degrees(psi2), marker, markersize=12,
               markeredgecolor='black', label=label)

    ax.set_xlabel('ψ₁ = φ_G - φ_R (degrees)', fontsize=12)
    ax.set_ylabel('ψ₂ = φ_B - φ_G (degrees)', fontsize=12)
    ax.set_title(f'Phase Portrait on 𝕋² (K = {K})', fontsize=14)
    ax.set_xlim(0, 360)
    ax.set_ylim(0, 360)
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)
    ax.set_aspect('equal')

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"  Saved: {save_path}")
    plt.close()


def plot_basin_of_attraction(basin_FP1, basin_FP2, save_path: str = None):
    """Visualize basins of attraction."""
    fig, ax = plt.subplots(figsize=(10, 10))

    if len(basin_FP1) > 0:
        ax.scatter(np.degrees(basin_FP1[:, 0]), np.degrees(basin_FP1[:, 1]),
                  c='blue', alpha=0.5, s=20, label='→ FP1 (R→G→B)')
    if len(basin_FP2) > 0:
        ax.scatter(np.degrees(basin_FP2[:, 0]), np.degrees(basin_FP2[:, 1]),
                  c='red', alpha=0.5, s=20, label='→ FP2 (R→B→G)')

    # Mark fixed points
    ax.plot(120, 120, 'b*', markersize=20, markeredgecolor='black', label='FP1')
    ax.plot(240, 240, 'r*', markersize=20, markeredgecolor='black', label='FP2')

    ax.set_xlabel('ψ₁ initial (degrees)', fontsize=12)
    ax.set_ylabel('ψ₂ initial (degrees)', fontsize=12)
    ax.set_title('Basin of Attraction', fontsize=14)
    ax.set_xlim(0, 360)
    ax.set_ylim(0, 360)
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_aspect('equal')

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"  Saved: {save_path}")
    plt.close()


def plot_floquet_analysis(K: float = 1.0, omega: float = 1.0, save_path: str = None):
    """Plot Floquet multiplier analysis."""
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Vary K
    K_values = np.linspace(0.1, 5, 50)
    eigenvalues_1 = []
    eigenvalues_2 = []
    multipliers_1 = []
    multipliers_2 = []

    psi_star = np.array([ALPHA, ALPHA])
    T = 2 * np.pi / omega

    for K_val in K_values:
        J = compute_jacobian_numerical(psi_star, K_val)
        eigs = np.sort(np.real(eigvals(J)))
        eigenvalues_1.append(eigs[0])
        eigenvalues_2.append(eigs[1])
        multipliers_1.append(np.exp(eigs[0] * T))
        multipliers_2.append(np.exp(eigs[1] * T))

    ax = axes[0]
    ax.plot(K_values, eigenvalues_1, 'b-', linewidth=2, label='λ₁')
    ax.plot(K_values, eigenvalues_2, 'r-', linewidth=2, label='λ₂')
    ax.axhline(y=0, color='k', linestyle='--', alpha=0.5)
    ax.set_xlabel('Coupling K', fontsize=12)
    ax.set_ylabel('Eigenvalue λ', fontsize=12)
    ax.set_title('Eigenvalues vs Coupling Strength', fontsize=14)
    ax.legend()
    ax.grid(True, alpha=0.3)

    ax = axes[1]
    ax.semilogy(K_values, multipliers_1, 'b-', linewidth=2, label='|μ₁|')
    ax.semilogy(K_values, multipliers_2, 'r-', linewidth=2, label='|μ₂|')
    ax.axhline(y=1, color='k', linestyle='--', alpha=0.5, label='Stability boundary')
    ax.set_xlabel('Coupling K', fontsize=12)
    ax.set_ylabel('Floquet multiplier |μ|', fontsize=12)
    ax.set_title(f'Floquet Multipliers (ω = {omega})', fontsize=14)
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"  Saved: {save_path}")
    plt.close()


# ============================================================================
# MAIN VERIFICATION ROUTINE
# ============================================================================

def run_all_tests(K: float = 1.0, omega: float = 1.0, generate_plots: bool = True) -> Dict:
    """
    Run all verification tests for Theorem 2.2.2.

    Parameters:
        K: Coupling strength (default 1.0)
        omega: Natural frequency (default 1.0)
        generate_plots: Whether to generate and save plots

    Returns:
        Dictionary with all test results
    """
    print("="*70)
    print("THEOREM 2.2.2 NUMERICAL VERIFICATION")
    print("Limit Cycle Existence in the R→G→B Phase System")
    print("="*70)
    print(f"\nParameters: K = {K}, ω = {omega}")
    print(f"Expected period: T = 2π/ω = {2*np.pi/omega:.4f}")
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

    results = {
        "theorem": "2.2.2",
        "name": "Limit Cycle Existence",
        "date": datetime.now().isoformat(),
        "parameters": {"K": K, "omega": omega},
        "tests": {}
    }

    # Run all tests
    results["tests"]["test_1_existence"] = test_1_limit_cycle_existence(K, omega)
    results["tests"]["test_2_period"] = test_2_period_measurement(K, omega)
    results["tests"]["test_3_floquet"] = test_3_floquet_multipliers(K, omega)
    results["tests"]["test_4_fixed_points"] = test_4_fixed_point_classification(K)

    test5_results, basin_FP1, basin_FP2 = test_5_global_attraction(K)
    results["tests"]["test_5_global"] = test5_results

    results["tests"]["test_6_color_neutrality"] = test_6_color_neutrality_on_cycle(K, omega)
    results["tests"]["test_7_chirality"] = test_7_chirality_persistence(K, omega)

    # Summary
    all_passed = all(test["passed"] for test in results["tests"].values())
    results["all_passed"] = all_passed

    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)

    for test_name, test_result in results["tests"].items():
        status = "✓ PASSED" if test_result["passed"] else "✗ FAILED"
        print(f"  {test_name}: {status}")

    print(f"\n  Overall: {'✓ ALL TESTS PASSED' if all_passed else '✗ SOME TESTS FAILED'}")

    # Generate plots
    if generate_plots:
        print("\n" + "="*70)
        print("GENERATING PLOTS")
        print("="*70)

        plot_dir = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots"
        import os
        os.makedirs(plot_dir, exist_ok=True)

        plot_limit_cycle_3d(K, omega, f"{plot_dir}/theorem_2_2_2_limit_cycle_3d.png")
        plot_phase_portrait_with_trajectories(K, f"{plot_dir}/theorem_2_2_2_phase_portrait.png")
        plot_basin_of_attraction(basin_FP1, basin_FP2, f"{plot_dir}/theorem_2_2_2_basin.png")
        plot_floquet_analysis(K, omega, f"{plot_dir}/theorem_2_2_2_floquet.png")

    # Save results to JSON
    def convert_numpy(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.bool_, np.integer)):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, dict):
            return {k: convert_numpy(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_numpy(v) for v in obj]
        return obj

    results_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/theorem_2_2_2_results.json"
    with open(results_path, 'w') as f:
        json.dump(convert_numpy(results), f, indent=2)
    print(f"\n  Results saved to: {results_path}")

    return results


if __name__ == "__main__":
    results = run_all_tests(K=1.0, omega=1.0, generate_plots=True)
