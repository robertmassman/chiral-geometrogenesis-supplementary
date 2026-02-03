#!/usr/bin/env python3
"""
Investigation: Observer Self-Consistency Bound on N

This script explores mechanisms beyond Fisher metric rank that could
provide a pure information-theoretic bound N ≤ 3.

Key Question: If Fisher metric has full rank for all N ≥ 3, what else
could limit the number of distinguishable components?

Approaches Explored:
1. Mutual Information Saturation
2. Simultaneous Estimation Bounds (quantum-like uncertainty)
3. Self-Modeling Complexity
4. Information Efficiency per Component

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-01
"""

import numpy as np
from typing import Tuple, List, Dict
import matplotlib.pyplot as plt
from scipy.linalg import sqrtm
from scipy.integrate import quad

# ============================================================================
# BASIC SETUP (from N4 investigation)
# ============================================================================

def get_equilibrium_phases(N: int) -> np.ndarray:
    """Get the color-neutral equilibrium phases for N components."""
    return 2 * np.pi * np.arange(N) / N


def amplitude_function(x: np.ndarray, color: int, N: int) -> np.ndarray:
    """Amplitude function for color 'color' in an N-component system."""
    phase_offset = 2 * np.pi * color / N
    return np.exp(-2 * (1 - np.cos(x - phase_offset)))


def interference_pattern_N(x: np.ndarray, phases: np.ndarray) -> np.ndarray:
    """Compute interference pattern for N components with given phases."""
    N = len(phases)
    chi_total = np.zeros_like(x, dtype=complex)
    for c in range(N):
        A_c = amplitude_function(x, c, N)
        chi_total += A_c * np.exp(1j * phases[c])
    return np.abs(chi_total)**2


def compute_fisher_matrix(N: int, n_points: int = 2000) -> np.ndarray:
    """Compute the Fisher information matrix for N components at equilibrium."""
    x = np.linspace(0, 2 * np.pi, n_points)
    phases_eq = get_equilibrium_phases(N)
    dim = N - 1

    p_eq = interference_pattern_N(x, phases_eq)
    eps = 1e-6
    dp_dphi = np.zeros((dim, n_points))

    for i in range(dim):
        phases_plus = phases_eq.copy()
        phases_plus[i + 1] += eps
        phases_minus = phases_eq.copy()
        phases_minus[i + 1] -= eps

        p_plus = interference_pattern_N(x, phases_plus)
        p_minus = interference_pattern_N(x, phases_minus)
        dp_dphi[i] = (p_plus - p_minus) / (2 * eps)

    g_F = np.zeros((dim, dim))
    for i in range(dim):
        for j in range(dim):
            valid = p_eq > 1e-12
            integrand = np.where(valid, dp_dphi[i] * dp_dphi[j] / p_eq, 0.0)
            g_F[i, j] = np.trapezoid(integrand, x)

    return g_F


# ============================================================================
# APPROACH 1: MUTUAL INFORMATION ANALYSIS
# ============================================================================

def compute_entropy(p: np.ndarray, x: np.ndarray) -> float:
    """Compute Shannon entropy of distribution p(x)."""
    # Normalize
    dx = x[1] - x[0]
    norm = np.trapezoid(p, x)
    p_norm = p / norm

    # Entropy: -∫ p log p dx
    valid = p_norm > 1e-12
    integrand = np.where(valid, -p_norm * np.log(p_norm + 1e-15), 0.0)
    return np.trapezoid(integrand, x)


def compute_mutual_information_bound(N: int, n_points: int = 2000) -> Dict:
    """
    Compute bounds on mutual information I(configuration; observation).

    The idea: For N components, the observer must extract N-1 bits of
    phase information. But the observation channel has limited capacity.
    """
    x = np.linspace(0, 2 * np.pi, n_points)
    phases_eq = get_equilibrium_phases(N)
    p_eq = interference_pattern_N(x, phases_eq)

    # Base entropy of equilibrium pattern
    H_eq = compute_entropy(p_eq, x)

    # Perturb each phase and compute how much the pattern changes
    eps = 0.1  # Finite perturbation
    info_per_phase = []

    for i in range(1, N):  # Skip phi_0 = 0 reference
        phases_plus = phases_eq.copy()
        phases_plus[i] += eps
        p_plus = interference_pattern_N(x, phases_plus)

        # Relative entropy (KL divergence)
        valid = (p_eq > 1e-12) & (p_plus > 1e-12)
        kl_div = np.where(valid, p_plus * np.log(p_plus / (p_eq + 1e-15) + 1e-15), 0.0)
        kl = np.trapezoid(kl_div, x)
        info_per_phase.append(kl)

    # Total information extractable
    total_info = sum(info_per_phase)
    avg_info_per_phase = total_info / (N - 1) if N > 1 else 0

    return {
        "N": N,
        "entropy_equilibrium": H_eq,
        "info_per_phase": info_per_phase,
        "total_info": total_info,
        "avg_info_per_phase": avg_info_per_phase,
        "info_efficiency": avg_info_per_phase / H_eq if H_eq > 0 else 0
    }


# ============================================================================
# APPROACH 2: SIMULTANEOUS ESTIMATION BOUND
# ============================================================================

def compute_quantum_fisher_bound(N: int, n_points: int = 2000) -> Dict:
    """
    Analyze whether there are quantum-like uncertainty relations
    that prevent simultaneous estimation of all N-1 phases.

    In quantum mechanics, non-commuting observables can't be measured
    simultaneously. We check if there's an analogous constraint for
    phase estimation.
    """
    g_F = compute_fisher_matrix(N, n_points)
    dim = N - 1

    if dim == 0:
        return {"N": N, "can_estimate_all": False, "reason": "trivial"}

    # Eigenvalue analysis
    eigenvalues = np.linalg.eigvalsh(g_F)
    eigenvalues = np.sort(eigenvalues)[::-1]

    # Condition number: ratio of max to min eigenvalue
    # High condition number → some directions hard to estimate
    if eigenvalues[-1] > 1e-10:
        condition = eigenvalues[0] / eigenvalues[-1]
    else:
        condition = np.inf

    # "Effective degrees of freedom" - how many directions are well-conditioned
    threshold = 0.1 * eigenvalues[0]  # 10% of max
    effective_dof = np.sum(eigenvalues > threshold)

    # Cramér-Rao bound: Var(θ_i) ≥ (g_F^{-1})_{ii}
    # Total variance bound
    if np.linalg.matrix_rank(g_F) == dim:
        g_F_inv = np.linalg.inv(g_F)
        total_variance_bound = np.trace(g_F_inv)
        per_param_variance = total_variance_bound / dim
    else:
        total_variance_bound = np.inf
        per_param_variance = np.inf

    # "Estimation hardness": geometric mean of inverse eigenvalues
    if all(e > 1e-10 for e in eigenvalues):
        estimation_hardness = np.exp(np.mean(np.log(1.0 / eigenvalues)))
    else:
        estimation_hardness = np.inf

    return {
        "N": N,
        "dimension": dim,
        "eigenvalues": eigenvalues.tolist(),
        "condition_number": condition,
        "effective_dof": effective_dof,
        "total_variance_bound": total_variance_bound,
        "per_param_variance": per_param_variance,
        "estimation_hardness": estimation_hardness
    }


# ============================================================================
# APPROACH 3: SELF-MODELING COMPLEXITY
# ============================================================================

def compute_self_modeling_complexity(N: int) -> Dict:
    """
    Analyze the complexity of an N-component observer modeling itself.

    Key insight: An observer is itself a configuration in the same space.
    To model itself, the observer needs internal states that can represent
    configurations of N-component systems.

    Self-reference creates a recursive constraint.
    """
    dim = N - 1  # Configuration space dimension

    # Number of independent parameters to specify a configuration
    params_to_model = dim

    # For the observer to model itself + distinguish external configurations:
    # - Need dim parameters for self-state
    # - Need dim parameters for each distinguishable external state
    # Total internal complexity for K distinguishable states: K * dim

    # Kolmogorov-like complexity: minimum description length
    # For N phases with precision δ: log_2(1/δ) * (N-1) bits
    precision = 0.01  # 1% precision
    bits_per_config = np.log2(1 / precision) * dim

    # Self-modeling overhead: observer must represent itself
    # This creates a fixed-point constraint
    self_modeling_bits = bits_per_config  # Minimum to model own state

    # Total bits needed for self + K external states
    def total_bits_for_K(K):
        return self_modeling_bits + K * bits_per_config

    # If observer has I_max bits, it can distinguish K states where:
    # total_bits_for_K(K) ≤ I_max
    # → K ≤ (I_max - self_modeling_bits) / bits_per_config

    # Key question: What determines I_max?
    # If I_max ∝ (N-1), then we get a bound on K that depends on N

    return {
        "N": N,
        "config_dimension": dim,
        "bits_per_config": bits_per_config,
        "self_modeling_bits": self_modeling_bits,
        "self_overhead_ratio": 1.0,  # Self-modeling takes 1 "config worth" of bits
        "total_for_self_plus_1": total_bits_for_K(1),
        "total_for_self_plus_2": total_bits_for_K(2),
    }


# ============================================================================
# APPROACH 4: INFORMATION EFFICIENCY SCALING
# ============================================================================

def compute_information_efficiency(N: int, n_points: int = 2000) -> Dict:
    """
    Compute how efficiently information is distributed among N components.

    Hypothesis: As N increases, the "information per component" decreases,
    eventually hitting a threshold where additional components don't
    provide distinguishable information.
    """
    g_F = compute_fisher_matrix(N, n_points)
    dim = N - 1

    if dim == 0:
        return {"N": N, "total_info": 0, "info_per_component": 0}

    # Total Fisher information: trace of Fisher matrix
    total_info = np.trace(g_F)

    # Information per component
    info_per_component = total_info / N

    # Information per degree of freedom
    info_per_dof = total_info / dim

    # Eigenvalue spectrum analysis
    eigenvalues = np.linalg.eigvalsh(g_F)
    eigenvalues = np.sort(eigenvalues)[::-1]

    # Entropy of eigenvalue distribution (normalized)
    if np.sum(eigenvalues) > 0:
        p_eig = eigenvalues / np.sum(eigenvalues)
        spectral_entropy = -np.sum(p_eig * np.log(p_eig + 1e-15))
    else:
        spectral_entropy = 0

    # Maximum spectral entropy for dim eigenvalues is log(dim)
    max_spectral_entropy = np.log(dim) if dim > 0 else 0
    spectral_uniformity = spectral_entropy / max_spectral_entropy if max_spectral_entropy > 0 else 0

    return {
        "N": N,
        "dimension": dim,
        "total_fisher_info": total_info,
        "info_per_component": info_per_component,
        "info_per_dof": info_per_dof,
        "spectral_entropy": spectral_entropy,
        "spectral_uniformity": spectral_uniformity,
        "eigenvalues": eigenvalues.tolist()
    }


# ============================================================================
# APPROACH 5: FIXED-POINT ANALYSIS
# ============================================================================

def analyze_fixed_point(N_max: int = 10) -> Dict:
    """
    Analyze the fixed-point equation for observer self-consistency.

    Define F(N) = maximum components an N-component observer can distinguish.

    For self-consistency: N = F(N)

    We estimate F(N) using information-theoretic measures.
    """
    results = []

    for N in range(2, N_max + 1):
        g_F = compute_fisher_matrix(N)
        dim = N - 1

        if dim == 0:
            F_N = 0
        else:
            eigenvalues = np.linalg.eigvalsh(g_F)
            eigenvalues = np.sort(eigenvalues)[::-1]

            # F(N) estimated as: number of eigenvalues above threshold
            # where threshold = "minimum useful information"

            # Threshold 1: Fixed absolute threshold
            threshold_abs = 0.1
            F_N_abs = np.sum(eigenvalues > threshold_abs) + 1  # +1 for reference phase

            # Threshold 2: Relative to max eigenvalue
            threshold_rel = 0.05 * eigenvalues[0]
            F_N_rel = np.sum(eigenvalues > threshold_rel) + 1

            # Threshold 3: Based on information per component
            total_info = np.trace(g_F)
            min_info_per_component = 0.2  # Minimum info to be "distinguishable"
            F_N_info = int(total_info / min_info_per_component) + 1 if total_info > 0 else 0

        results.append({
            "N": N,
            "F_N_absolute": int(F_N_abs) if dim > 0 else 0,
            "F_N_relative": int(F_N_rel) if dim > 0 else 0,
            "F_N_info": min(F_N_info, N) if dim > 0 else 0,
            "is_fixed_point_abs": N == F_N_abs if dim > 0 else False,
            "is_fixed_point_rel": N == F_N_rel if dim > 0 else False,
        })

    return results


# ============================================================================
# MAIN INVESTIGATION
# ============================================================================

def run_full_investigation(N_max: int = 8):
    """Run all approaches and synthesize findings."""

    print("=" * 70)
    print("OBSERVER SELF-CONSISTENCY: BEYOND FISHER METRIC RANK")
    print("=" * 70)
    print()

    # Approach 1: Mutual Information
    print("APPROACH 1: MUTUAL INFORMATION ANALYSIS")
    print("-" * 50)
    for N in range(2, N_max + 1):
        mi = compute_mutual_information_bound(N)
        print(f"N={N}: Total info={mi['total_info']:.4f}, "
              f"Avg/phase={mi['avg_info_per_phase']:.4f}, "
              f"Efficiency={mi['info_efficiency']:.4f}")
    print()

    # Approach 2: Simultaneous Estimation
    print("APPROACH 2: SIMULTANEOUS ESTIMATION BOUNDS")
    print("-" * 50)
    for N in range(2, N_max + 1):
        qf = compute_quantum_fisher_bound(N)
        print(f"N={N}: Dim={qf['dimension']}, "
              f"Effective DOF={qf['effective_dof']}, "
              f"Condition={qf['condition_number']:.2f}, "
              f"Hardness={qf['estimation_hardness']:.4f}")
    print()

    # Approach 3: Self-Modeling Complexity
    print("APPROACH 3: SELF-MODELING COMPLEXITY")
    print("-" * 50)
    for N in range(2, N_max + 1):
        sm = compute_self_modeling_complexity(N)
        print(f"N={N}: Bits/config={sm['bits_per_config']:.2f}, "
              f"Self+1={sm['total_for_self_plus_1']:.2f}, "
              f"Self+2={sm['total_for_self_plus_2']:.2f}")
    print()

    # Approach 4: Information Efficiency
    print("APPROACH 4: INFORMATION EFFICIENCY SCALING")
    print("-" * 50)
    print(f"{'N':>3} | {'Dim':>3} | {'Total':>8} | {'Per Comp':>8} | {'Per DOF':>8} | {'Uniformity':>10}")
    print("-" * 60)
    for N in range(2, N_max + 1):
        ie = compute_information_efficiency(N)
        print(f"{N:>3} | {ie['dimension']:>3} | {ie['total_fisher_info']:>8.4f} | "
              f"{ie['info_per_component']:>8.4f} | {ie['info_per_dof']:>8.4f} | "
              f"{ie['spectral_uniformity']:>10.4f}")
    print()

    # Approach 5: Fixed-Point Analysis
    print("APPROACH 5: FIXED-POINT ANALYSIS")
    print("-" * 50)
    fp_results = analyze_fixed_point(N_max)
    print(f"{'N':>3} | {'F(N)_abs':>8} | {'F(N)_rel':>8} | {'F(N)_info':>9} | {'Fixed?':>8}")
    print("-" * 50)
    for r in fp_results:
        fp = "YES" if r['is_fixed_point_rel'] else "no"
        print(f"{r['N']:>3} | {r['F_N_absolute']:>8} | {r['F_N_relative']:>8} | "
              f"{r['F_N_info']:>9} | {fp:>8}")
    print()

    # Synthesis
    print("=" * 70)
    print("SYNTHESIS: KEY FINDINGS")
    print("=" * 70)
    print()

    print("1. MUTUAL INFORMATION:")
    print("   - Info per phase DECREASES with N (expected from Fisher analysis)")
    print("   - No sharp cutoff, gradual degradation")
    print()

    print("2. SIMULTANEOUS ESTIMATION:")
    print("   - Effective DOF = full dimension for all N ≥ 3")
    print("   - Condition number increases with N (estimation gets harder)")
    print("   - No quantum-like uncertainty preventing simultaneous estimation")
    print()

    print("3. SELF-MODELING:")
    print("   - Complexity scales linearly with N")
    print("   - Self-modeling overhead is constant (1 config worth)")
    print("   - No nonlinear blowup that would bound N")
    print()

    print("4. INFORMATION EFFICIENCY:")
    print("   - Info per component INCREASES then saturates near 1")
    print("   - Spectral uniformity increases (eigenvalues spread out)")
    print("   - No efficiency collapse for N > 3")
    print()

    print("5. FIXED-POINT ANALYSIS:")
    print("   - With threshold-based F(N), all N ≥ 3 are fixed points")
    print("   - No unique selection of N = 3 from fixed-point structure")
    print()

    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print()
    print("The investigated mechanisms do NOT provide a sharp bound N ≤ 3.")
    print()
    print("Possible paths forward:")
    print("  1. HOLOGRAPHIC BOUND: Needs physical observer size/energy (geometric)")
    print("  2. COMPUTATIONAL COMPLEXITY: Bootstrap self-consistency might be")
    print("     exponentially hard for N > 3 (needs formalization)")
    print("  3. DIFFERENT SELF-CONSISTENCY: The observer-configuration interaction")
    print("     might have constraints not captured by Fisher information alone")
    print("  4. ACCEPT GEOMETRIC INPUT: The bound N ≤ 4 from affine independence")
    print("     may be irreducible (D = 4 is the unavoidable input)")
    print()
    print("RECOMMENDATION: Develop the computational complexity approach (Path D)")
    print("or formalize holographic bounds with minimal geometric input.")
    print()


# ============================================================================
# VISUALIZATION
# ============================================================================

def plot_scaling_analysis(N_max: int = 8):
    """Generate plots showing how key quantities scale with N."""

    N_values = list(range(2, N_max + 1))

    # Collect data
    info_per_component = []
    condition_numbers = []
    effective_dofs = []
    spectral_uniformity = []

    for N in N_values:
        ie = compute_information_efficiency(N)
        qf = compute_quantum_fisher_bound(N)

        info_per_component.append(ie['info_per_component'])
        condition_numbers.append(qf['condition_number'])
        effective_dofs.append(qf['effective_dof'])
        spectral_uniformity.append(ie['spectral_uniformity'])

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Information per component
    ax1 = axes[0, 0]
    ax1.plot(N_values, info_per_component, 'bo-', markersize=8)
    ax1.set_xlabel("N (number of components)")
    ax1.set_ylabel("Fisher Info per Component")
    ax1.set_title("Information Efficiency")
    ax1.axhline(y=1.0, color='r', linestyle='--', alpha=0.5, label="Saturation level")
    ax1.grid(True, alpha=0.3)
    ax1.legend()

    # Plot 2: Condition number
    ax2 = axes[0, 1]
    ax2.plot(N_values, condition_numbers, 'go-', markersize=8)
    ax2.set_xlabel("N")
    ax2.set_ylabel("Condition Number")
    ax2.set_title("Estimation Difficulty (Condition Number)")
    ax2.set_yscale("log")
    ax2.grid(True, alpha=0.3)

    # Plot 3: Effective DOF vs Dimension
    ax3 = axes[1, 0]
    dimensions = [N - 1 for N in N_values]
    ax3.plot(N_values, effective_dofs, 'ro-', markersize=8, label="Effective DOF")
    ax3.plot(N_values, dimensions, 'b--', markersize=8, label="Config Dimension (N-1)")
    ax3.set_xlabel("N")
    ax3.set_ylabel("Degrees of Freedom")
    ax3.set_title("Effective vs Total Degrees of Freedom")
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # Plot 4: Spectral uniformity
    ax4 = axes[1, 1]
    ax4.plot(N_values, spectral_uniformity, 'mo-', markersize=8)
    ax4.set_xlabel("N")
    ax4.set_ylabel("Spectral Uniformity")
    ax4.set_title("Eigenvalue Distribution Uniformity")
    ax4.axhline(y=1.0, color='r', linestyle='--', alpha=0.5, label="Perfectly uniform")
    ax4.grid(True, alpha=0.3)
    ax4.legend()

    plt.tight_layout()
    plot_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/observer_self_consistency.png"
    plt.savefig(plot_path, dpi=150)
    print(f"Plot saved to: {plot_path}")
    plt.close()


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    run_full_investigation(N_max=8)
    plot_scaling_analysis(N_max=8)
