#!/usr/bin/env python3
"""
Investigation: Fisher Metric for N = 4, 5, ... Components

This script investigates whether the Fisher metric has pathologies for N > 3
that could provide a pure information-theoretic bound on N.

Key Questions:
1. Is the Fisher metric non-degenerate for N ≥ 4?
2. Does the "effective dimension" of distinguishability plateau at 2?
3. Is there information saturation as N increases?

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-01
"""

import numpy as np
from typing import Tuple, List
import matplotlib.pyplot as plt

# ============================================================================
# INTERFERENCE PATTERNS FOR GENERAL N
# ============================================================================

def get_equilibrium_phases(N: int) -> np.ndarray:
    """
    Get the color-neutral equilibrium phases for N components.

    For N components with color neutrality: sum_c exp(i*phi_c) = 0
    The equilibrium phases are: phi_c = 2*pi*c/N for c = 0, 1, ..., N-1

    Returns:
        Array of N phases at equilibrium
    """
    return 2 * np.pi * np.arange(N) / N


def amplitude_function(x: np.ndarray, color: int, N: int) -> np.ndarray:
    """
    Amplitude function for color 'color' in an N-component system.

    Each color peaks at a different angular position.
    """
    phase_offset = 2 * np.pi * color / N
    return np.exp(-2 * (1 - np.cos(x - phase_offset)))


def interference_pattern_N(x: np.ndarray, phases: np.ndarray) -> np.ndarray:
    """
    Compute interference pattern for N components with given phases.

    p(x) = |sum_c A_c(x) * exp(i * phi_c)|^2
    """
    N = len(phases)
    chi_total = np.zeros_like(x, dtype=complex)

    for c in range(N):
        A_c = amplitude_function(x, c, N)
        chi_total += A_c * np.exp(1j * phases[c])

    return np.abs(chi_total)**2


def verify_color_neutrality(N: int) -> float:
    """Verify that equilibrium phases satisfy color neutrality."""
    phases = get_equilibrium_phases(N)
    phase_sum = np.sum(np.exp(1j * phases))
    return np.abs(phase_sum)


# ============================================================================
# FISHER METRIC COMPUTATION FOR GENERAL N
# ============================================================================

def compute_fisher_metric_general_N(N: int, n_points: int = 2000) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute the Fisher information matrix for N components at equilibrium.

    The configuration space has dimension N - 1 (after U(1) quotient).
    We use phases (phi_1, phi_2, ..., phi_{N-1}) with phi_0 = 0 as reference.

    Returns:
        (Fisher matrix, eigenvalues)
    """
    x = np.linspace(0, 2 * np.pi, n_points)
    phases_eq = get_equilibrium_phases(N)

    # Configuration space dimension
    dim = N - 1

    # Interference pattern at equilibrium
    p_eq = interference_pattern_N(x, phases_eq)

    # Compute partial derivatives numerically
    eps = 1e-6
    dp_dphi = np.zeros((dim, n_points))

    for i in range(dim):
        # Perturb phase phi_{i+1} (since phi_0 is reference)
        phases_plus = phases_eq.copy()
        phases_plus[i + 1] += eps

        phases_minus = phases_eq.copy()
        phases_minus[i + 1] -= eps

        p_plus = interference_pattern_N(x, phases_plus)
        p_minus = interference_pattern_N(x, phases_minus)

        dp_dphi[i] = (p_plus - p_minus) / (2 * eps)

    # Fisher metric components
    g_F = np.zeros((dim, dim))

    for i in range(dim):
        for j in range(dim):
            # g_ij = integral of (dp/dphi_i)(dp/dphi_j) / p dx
            valid = p_eq > 1e-12
            integrand = np.where(valid, dp_dphi[i] * dp_dphi[j] / p_eq, 0.0)
            g_F[i, j] = np.trapezoid(integrand, x)

    # Compute eigenvalues
    eigenvalues = np.linalg.eigvalsh(g_F)

    return g_F, eigenvalues


def analyze_fisher_metric(N: int) -> dict:
    """
    Analyze the Fisher metric for N components.

    Returns dictionary with:
    - dimension: configuration space dimension
    - fisher_matrix: the Fisher metric
    - eigenvalues: sorted eigenvalues
    - rank: effective rank (eigenvalues > threshold)
    - condition_number: ratio of max to min eigenvalue
    - is_degenerate: whether any eigenvalue is near zero
    """
    g_F, eigs = compute_fisher_metric_general_N(N)

    # Sort eigenvalues
    eigs_sorted = np.sort(eigs)[::-1]

    # Effective rank (eigenvalues > 1% of max)
    threshold = 0.01 * eigs_sorted[0] if eigs_sorted[0] > 0 else 1e-10
    rank = np.sum(eigs_sorted > threshold)

    # Condition number
    if eigs_sorted[-1] > 1e-15:
        condition = eigs_sorted[0] / eigs_sorted[-1]
    else:
        condition = np.inf

    # Degeneracy check
    is_degenerate = eigs_sorted[-1] < 1e-6

    return {
        "N": N,
        "dimension": N - 1,
        "fisher_matrix": g_F,
        "eigenvalues": eigs_sorted,
        "rank": rank,
        "condition_number": condition,
        "is_degenerate": is_degenerate,
        "min_eigenvalue": eigs_sorted[-1],
        "max_eigenvalue": eigs_sorted[0],
        "trace": np.trace(g_F)
    }


# ============================================================================
# MAIN INVESTIGATION
# ============================================================================

def investigate_N_dependence(N_max: int = 8):
    """Investigate how Fisher metric properties depend on N."""

    print("=" * 70)
    print("INVESTIGATION: FISHER METRIC FOR N COMPONENTS")
    print("=" * 70)
    print()

    results = []

    for N in range(2, N_max + 1):
        # Verify color neutrality
        neutrality_error = verify_color_neutrality(N)

        # Analyze Fisher metric
        analysis = analyze_fisher_metric(N)
        analysis["neutrality_error"] = neutrality_error
        results.append(analysis)

        print(f"N = {N}:")
        print(f"  Configuration space dimension: {analysis['dimension']}")
        print(f"  Color neutrality error: {neutrality_error:.2e}")
        print(f"  Fisher metric eigenvalues: {analysis['eigenvalues']}")
        print(f"  Effective rank: {analysis['rank']}")
        print(f"  Condition number: {analysis['condition_number']:.2f}")
        print(f"  Is degenerate: {analysis['is_degenerate']}")
        print(f"  Trace(g^F): {analysis['trace']:.6f}")
        print()

    return results


def plot_eigenvalue_scaling(results: List[dict]):
    """Plot how eigenvalues scale with N."""

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    N_values = [r["N"] for r in results]

    # Plot 1: All eigenvalues
    ax1 = axes[0, 0]
    for r in results:
        N = r["N"]
        eigs = r["eigenvalues"]
        ax1.scatter([N] * len(eigs), eigs, s=50, alpha=0.7)
    ax1.set_xlabel("N (number of components)")
    ax1.set_ylabel("Eigenvalue")
    ax1.set_title("Fisher Metric Eigenvalues vs N")
    ax1.set_yscale("log")
    ax1.grid(True, alpha=0.3)

    # Plot 2: Minimum eigenvalue
    ax2 = axes[0, 1]
    min_eigs = [r["min_eigenvalue"] for r in results]
    ax2.plot(N_values, min_eigs, 'bo-', markersize=8)
    ax2.set_xlabel("N")
    ax2.set_ylabel("Minimum Eigenvalue")
    ax2.set_title("Minimum Eigenvalue vs N")
    ax2.set_yscale("log")
    ax2.axhline(y=1e-6, color='r', linestyle='--', label="Degeneracy threshold")
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # Plot 3: Effective rank
    ax3 = axes[1, 0]
    ranks = [r["rank"] for r in results]
    dims = [r["dimension"] for r in results]
    ax3.plot(N_values, ranks, 'go-', markersize=8, label="Effective rank")
    ax3.plot(N_values, dims, 'b--', markersize=8, label="Config space dim (N-1)")
    ax3.set_xlabel("N")
    ax3.set_ylabel("Dimension")
    ax3.set_title("Effective Rank vs Configuration Space Dimension")
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # Plot 4: Trace (total information)
    ax4 = axes[1, 1]
    traces = [r["trace"] for r in results]
    ax4.plot(N_values, traces, 'mo-', markersize=8)
    ax4.set_xlabel("N")
    ax4.set_ylabel("Trace(g^F)")
    ax4.set_title("Total Fisher Information vs N")
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()
    plot_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/N_dependence_investigation.png"
    plt.savefig(plot_path, dpi=150)
    print(f"\nPlot saved to: {plot_path}")
    plt.close()


def analyze_information_saturation(results: List[dict]):
    """
    Analyze whether there's information saturation as N increases.

    Key question: Does the "information per component" decrease for large N?
    """

    print("=" * 70)
    print("ANALYSIS: INFORMATION SATURATION")
    print("=" * 70)
    print()

    print("Information metrics:")
    print(f"{'N':>3} | {'Dim':>3} | {'Trace/N':>10} | {'Min Eig':>12} | {'Rank':>4} | {'Saturated?':>10}")
    print("-" * 60)

    for r in results:
        N = r["N"]
        dim = r["dimension"]
        trace_per_N = r["trace"] / N
        min_eig = r["min_eigenvalue"]
        rank = r["rank"]

        # "Saturated" if rank < dim or trace/N decreases
        saturated = rank < dim

        print(f"{N:>3} | {dim:>3} | {trace_per_N:>10.4f} | {min_eig:>12.6f} | {rank:>4} | {'YES' if saturated else 'NO':>10}")

    print()
    print("Key findings:")

    # Check if rank plateaus
    ranks = [r["rank"] for r in results]
    dims = [r["dimension"] for r in results]

    if all(r == d for r, d in zip(ranks, dims)):
        print("  • Fisher metric has FULL RANK for all N tested")
        print("  • No information-theoretic bound on N from rank analysis")
    else:
        plateau_N = None
        for i, (r, d) in enumerate(zip(ranks, dims)):
            if r < d:
                plateau_N = results[i]["N"]
                break
        if plateau_N:
            print(f"  • Rank drops below dimension at N = {plateau_N}")
            print(f"  • This suggests information saturation!")

    # Check trace scaling
    traces = [r["trace"] for r in results]
    N_values = [r["N"] for r in results]

    # Linear fit
    coeffs = np.polyfit(N_values, traces, 1)
    print(f"\n  • Trace scales approximately as: {coeffs[0]:.4f} * N + {coeffs[1]:.4f}")

    if coeffs[0] > 0:
        print("  • Total information INCREASES with N (no saturation)")
    else:
        print("  • Total information DECREASES with N (saturation!)")


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    # Run investigation
    results = investigate_N_dependence(N_max=8)

    # Analyze saturation
    analyze_information_saturation(results)

    # Generate plots
    plot_eigenvalue_scaling(results)

    # Summary
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()

    # Key question: Is there a pure information-theoretic bound on N?
    all_full_rank = all(r["rank"] == r["dimension"] for r in results)

    if all_full_rank:
        print("FINDING: The Fisher metric is non-degenerate for all N tested (2-8).")
        print()
        print("This means:")
        print("  • There is NO obvious information-theoretic degeneracy for N > 3")
        print("  • The bound N ≤ 3 likely requires a DIFFERENT argument:")
        print("    - Observer self-consistency (fixed point)")
        print("    - Holographic bounds")
        print("    - Or the geometric argument (D = 4) may be essential")
        print()
        print("Recommended next step: Investigate observer self-consistency formalism")
    else:
        # Find where saturation occurs
        for r in results:
            if r["rank"] < r["dimension"]:
                print(f"FINDING: Fisher metric becomes degenerate at N = {r['N']}")
                print(f"  • This provides a pure information-theoretic bound!")
                break
