#!/usr/bin/env python3
"""
Lemma 0.0.17c Index Verification

Verify the correct form of the Fisher metric transformation law under permutations.
This addresses the index error identified in the multi-agent verification report.

The question: Under permutation σ acting on phases, does the Fisher metric transform as:
  g^F_ij(σ(φ)) = g^F_{σ^{-1}(i), σ^{-1}(j)}(φ)  [Document's claim]
  OR
  g^F_ij(σ(φ)) = g^F_{σ(i), σ(j)}(φ)  [Verification report's claim]
"""

import numpy as np
from itertools import permutations

def compute_fisher_metric(phi, amplitudes, dx=0.01):
    """
    Compute Fisher metric at point phi for probability distribution:
    p_phi(x) = |sum_c A_c(x) exp(i*phi_c)|^2

    Args:
        phi: array of N phases
        amplitudes: function that returns N amplitudes A_c(x) for given x
        dx: step size for numerical differentiation
    """
    N = len(phi)

    # Compute Fisher metric numerically
    # g_ij = E[d/dφ_i log(p) * d/dφ_j log(p)]

    # Use Monte Carlo over x
    n_samples = 10000
    x_samples = np.random.randn(n_samples)

    g = np.zeros((N, N))

    for x in x_samples:
        A = amplitudes(x)  # N amplitudes

        # Compute p(x) = |sum_c A_c exp(i φ_c)|^2
        psi = np.sum(A * np.exp(1j * phi))
        p = np.abs(psi)**2

        if p < 1e-12:
            continue

        # Compute d/dφ_c log(p) = d/dφ_c log|sum A exp(iφ)|^2
        # = 2 Re[(d/dφ_c psi) * conj(psi)] / |psi|^2
        # d/dφ_c psi = i A_c exp(i φ_c)

        score = np.zeros(N)
        for c in range(N):
            dpsi_dc = 1j * A[c] * np.exp(1j * phi[c])
            score[c] = 2 * np.real(dpsi_dc * np.conj(psi)) / p

        g += np.outer(score, score)

    g /= n_samples
    return g


def test_transformation_law():
    """Test how Fisher metric transforms under permutations."""

    print("=" * 70)
    print("TESTING FISHER METRIC TRANSFORMATION LAW")
    print("=" * 70)

    N = 3

    # S_N symmetric amplitudes
    def symmetric_amplitudes(x):
        """Equal amplitudes for all colors (full S_N symmetry)."""
        return np.ones(N) / np.sqrt(N)

    # Test at a generic point (not equilibrium)
    phi_0 = np.array([0.0, 0.5, 1.0])
    phi_0 = phi_0 - np.mean(phi_0)  # Ensure sum = 0

    # Compute Fisher metric at phi_0
    g_at_phi0 = compute_fisher_metric(phi_0, symmetric_amplitudes)

    print(f"\nOriginal point φ₀ = {phi_0}")
    print(f"Fisher metric at φ₀:")
    print(g_at_phi0)

    # Test permutation σ = (1 2) in cycle notation (swap first two)
    sigma = [1, 0, 2]  # σ(0)=1, σ(1)=0, σ(2)=2
    sigma_inv = [1, 0, 2]  # Same for transposition

    # Permuted point: (σ·φ)_i = φ_{σ(i)}
    phi_sigma = phi_0[sigma]

    print(f"\nPermuted point σ(φ₀) = {phi_sigma}")

    # Compute Fisher metric at permuted point
    g_at_sigma_phi = compute_fisher_metric(phi_sigma, symmetric_amplitudes)

    print(f"Fisher metric at σ(φ₀):")
    print(g_at_sigma_phi)

    # Test hypothesis 1: g_ij(σφ) = g_{σ^{-1}(i), σ^{-1}(j)}(φ)
    g_hypothesis1 = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            g_hypothesis1[i,j] = g_at_phi0[sigma_inv[i], sigma_inv[j]]

    print(f"\nHypothesis 1: g_{{σ⁻¹(i), σ⁻¹(j)}}(φ₀):")
    print(g_hypothesis1)
    print(f"Matches g(σφ)? {np.allclose(g_at_sigma_phi, g_hypothesis1, atol=0.1)}")

    # Test hypothesis 2: g_ij(σφ) = g_{σ(i), σ(j)}(φ)
    g_hypothesis2 = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            g_hypothesis2[i,j] = g_at_phi0[sigma[i], sigma[j]]

    print(f"\nHypothesis 2: g_{{σ(i), σ(j)}}(φ₀):")
    print(g_hypothesis2)
    print(f"Matches g(σφ)? {np.allclose(g_at_sigma_phi, g_hypothesis2, atol=0.1)}")

    # For S_N-symmetric distributions, both should match because:
    # p_{σφ}(x) = p_φ(x) implies g(σφ) = g(φ) (metric is constant!)

    print("\n" + "=" * 70)
    print("KEY INSIGHT")
    print("=" * 70)
    print("""
For S_N-SYMMETRIC probability distributions (p_{σφ} = p_φ), the Fisher metric
is CONSTANT over the entire phase space! Therefore:

  g(σφ) = g(φ) for all σ, φ

This means both transformation formulas are trivially satisfied when
p is S_N-invariant, because:

  g_ij = g_{σ(i),σ(j)} = g_{σ^{-1}(i),σ^{-1}(j)} (all equal to same constant)

The document's derivation is about showing that AT THE EQUILIBRIUM POINT
(where p IS symmetric), the metric must satisfy S_N symmetry.

The correct statement for the GENERAL transformation law (not assuming
p_{σφ} = p_φ) involves the Jacobian of the coordinate transformation.
""")

    # Now test with NON-symmetric amplitudes
    print("\n" + "=" * 70)
    print("TEST WITH NON-SYMMETRIC AMPLITUDES")
    print("=" * 70)

    def asymmetric_amplitudes(x):
        """Non-symmetric amplitudes."""
        return np.array([0.6, 0.3, 0.1]) * (1 + 0.1*x)

    g_asym_phi0 = compute_fisher_metric(phi_0, asymmetric_amplitudes)
    g_asym_sigma_phi = compute_fisher_metric(phi_sigma, asymmetric_amplitudes)

    print(f"g(φ₀) with asymmetric amplitudes:")
    print(g_asym_phi0)
    print(f"\ng(σφ₀) with asymmetric amplitudes:")
    print(g_asym_sigma_phi)

    # Now the metrics should be DIFFERENT because p is not S_N-symmetric
    print(f"\ng(φ₀) ≠ g(σφ₀)? {not np.allclose(g_asym_phi0, g_asym_sigma_phi, atol=0.1)}")


def analyze_transformation_formula():
    """Derive the correct transformation formula analytically."""

    print("\n" + "=" * 70)
    print("ANALYTICAL DERIVATION")
    print("=" * 70)

    print("""
Let σ act on phases by: (σ·φ)_i = φ_{σ(i)}   [standard left action]

For a coordinate transformation φ → φ' = σ·φ, the metric transforms as:

  g'_{ij}(φ') = (∂φ^k/∂φ'^i)(∂φ^l/∂φ'^j) g_{kl}(φ)

Since φ'_i = φ_{σ(i)}, we have φ_k = φ'_{σ^{-1}(k)}.

Therefore: ∂φ^k/∂φ'^i = δ^k_{σ(i)}

Substituting:
  g'_{ij}(φ') = δ^k_{σ(i)} δ^l_{σ(j)} g_{kl}(φ) = g_{σ(i),σ(j)}(φ)

So: g_{ij}(σ·φ) = g_{σ(i),σ(j)}(φ)   ← CORRECT FORMULA

The document's formula with σ^{-1} is INCORRECT for the transformation law.

However, at a symmetric point where g_{ij} = g_{π(i),π(j)} for all π ∈ S_N,
we have g_{σ(i),σ(j)} = g_{σ^{-1}σ(i), σ^{-1}σ(j)} = g_{i,j}, so both forms
reduce to the same condition.

CONCLUSION: The document should use σ(i), σ(j) in the transformation formula,
but the final S_N-invariance conclusion is still correct.
""")


def verify_equilibrium_invariance():
    """Verify S_N invariance at equilibrium point."""

    print("\n" + "=" * 70)
    print("VERIFICATION: S_N INVARIANCE AT EQUILIBRIUM")
    print("=" * 70)

    N = 3

    def symmetric_amplitudes(x):
        return np.ones(N) / np.sqrt(N)

    # Equilibrium point (equal phases)
    phi_eq = np.zeros(N)

    g_eq = compute_fisher_metric(phi_eq, symmetric_amplitudes)

    print(f"Fisher metric at equilibrium φ_eq = {phi_eq}:")
    print(g_eq)

    # Test S_3 invariance: g_ij = g_{σ(i), σ(j)} for all σ
    print("\nTesting S_3 invariance: g_{ij} = g_{σ(i),σ(j)}?")

    all_invariant = True
    for perm in permutations(range(N)):
        sigma = list(perm)
        g_permuted = np.zeros((N, N))
        for i in range(N):
            for j in range(N):
                g_permuted[i,j] = g_eq[sigma[i], sigma[j]]

        is_equal = np.allclose(g_eq, g_permuted, atol=0.05)
        if not is_equal:
            all_invariant = False
            print(f"  σ = {sigma}: NOT invariant!")

    if all_invariant:
        import math
    print(f"  ✓ All {math.factorial(N)} permutations checked: INVARIANT")

    # Show the structure
    print(f"\nMetric structure (diagonal, off-diagonal):")
    diag = g_eq[0,0]
    off_diag = g_eq[0,1]
    print(f"  Diagonal elements: {diag:.4f}")
    print(f"  Off-diagonal elements: {off_diag:.4f}")
    print(f"  Ratio: {off_diag/diag:.4f}")

    # For S_N-invariant metric, we expect g = a*I + b*11^T
    # where 1 = (1,1,...,1)^T
    # On traceless subspace, b-component vanishes


if __name__ == "__main__":
    test_transformation_law()
    analyze_transformation_formula()
    verify_equilibrium_invariance()
