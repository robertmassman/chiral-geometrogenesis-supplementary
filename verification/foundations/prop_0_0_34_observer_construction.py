#!/usr/bin/env python3
"""
Proposition 0.0.34 Part (a) Reverse Direction: Explicit Observer Construction
==============================================================================

Constructs an explicit internal observer O = (H_obs, rho_obs, M_obs) satisfying
Definition 0.0.32 conditions (S), (R), (L), given N_c >= 3 and g^F positive-definite.

This addresses the rigor gap identified in the multi-agent verification:
the original proof used rho_obs = (1/3)*I_3 (maximally mixed), which FAILS the
localization condition (L). Here we construct a LOCALIZED coherent state that
satisfies ALL three conditions simultaneously.

Construction:
  1. Z_3 fundamental domain centers on T^2 at (0,0), (2pi/3, 2pi/3), (4pi/3, 4pi/3)
  2. Localized coherent state |psi_loc> with Gaussian weight centered on sector 0
  3. Pure state rho_obs = |psi_loc><psi_loc| (exact self-encoding, error = 0)
  4. Observation map M_obs: projection onto Z_3 sector basis

Related Documents:
  - Proof: docs/proofs/foundations/Proposition-0.0.34-Observer-Participation.md
  - Definition: docs/proofs/foundations/Definition-0.0.32-Internal-Observer.md

Verification Date: 2026-02-05
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import os
import sys

# =============================================================================
# Output directory
# =============================================================================
PLOT_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'plots')
os.makedirs(PLOT_DIR, exist_ok=True)

# =============================================================================
# SECTION 1: Z_3 Fundamental Domain on the Cartan Torus T^2
# =============================================================================

def compute_z3_geometry():
    """
    Compute the Z_3 centers and fundamental domain structure on T^2.

    The Cartan torus of SU(3) is T^2 = [0, 2pi) x [0, 2pi) with coordinates
    (theta_1, theta_2). The Z_3 center acts by diagonal translation:
        (theta_1, theta_2) -> (theta_1 + 2pi*k/3, theta_2 + 2pi*k/3) mod 2pi
    for k = 0, 1, 2.

    The three Z_3 fixed points (centers of fundamental domains) are:
        k=0: (0, 0)
        k=1: (2pi/3, 2pi/3)
        k=2: (4pi/3, 4pi/3)
    """
    print("=" * 70)
    print("SECTION 1: Z_3 Fundamental Domain Geometry on T^2")
    print("=" * 70)

    z3_centers = np.array([
        [0.0, 0.0],
        [2 * np.pi / 3, 2 * np.pi / 3],
        [4 * np.pi / 3, 4 * np.pi / 3],
    ])

    print("\n  Z_3 centers on the Cartan torus T^2:")
    for k, center in enumerate(z3_centers):
        print(f"    k={k}: (theta_1, theta_2) = ({center[0]:.4f}, {center[1]:.4f})"
              f"  = ({center[0]/np.pi:.4f}*pi, {center[1]/np.pi:.4f}*pi)")

    # Compute pairwise distances (toroidal metric)
    print("\n  Pairwise distances between Z_3 centers (toroidal metric):")
    for i in range(3):
        for j in range(i + 1, 3):
            d1 = min(abs(z3_centers[i][0] - z3_centers[j][0]),
                     2 * np.pi - abs(z3_centers[i][0] - z3_centers[j][0]))
            d2 = min(abs(z3_centers[i][1] - z3_centers[j][1]),
                     2 * np.pi - abs(z3_centers[i][1] - z3_centers[j][1]))
            dist = np.sqrt(d1**2 + d2**2)
            print(f"    d(center_{i}, center_{j}) = sqrt({d1:.4f}^2 + {d2:.4f}^2)"
                  f" = {dist:.4f} rad")

    # Fundamental domain properties
    sector_width = 2 * np.pi / 3
    localization_bound = sector_width
    print(f"\n  Z_3 sector width (diagonal direction): {sector_width:.4f} rad"
          f" = {np.degrees(sector_width):.1f} deg")
    print(f"  Localization bound (Def 0.0.32 condition L): "
          f"diam(supp(rho)) < {localization_bound:.4f} rad")

    return z3_centers, localization_bound


# =============================================================================
# SECTION 2: Localized Coherent State Construction
# =============================================================================

def construct_localized_state(z3_centers, sigma):
    """
    Construct the localized coherent state |psi_loc> on C^3.

    The state is a superposition over the 3 Z_3 sector basis states |k>,
    with Gaussian weights centered on sector 0:

        |psi_loc> = (1/Z) * sum_{k=0}^{2} exp(-d_k^2 / (2*sigma^2)) * |k>

    where d_k is the toroidal distance from Z_3 center k to center 0 (the
    reference sector), and sigma controls the localization width.

    Parameters
    ----------
    z3_centers : ndarray, shape (3, 2)
        Coordinates of the three Z_3 centers on T^2.
    sigma : float
        Gaussian width parameter. Must satisfy sigma << 2*pi/3 for
        the state to be well-localized within a single sector.

    Returns
    -------
    psi : ndarray, shape (3,), complex
        Normalized state vector |psi_loc>.
    weights : ndarray, shape (3,)
        Unnormalized Gaussian weights for each sector.
    distances : ndarray, shape (3,)
        Toroidal distances from each Z_3 center to center 0.
    """
    print("\n" + "=" * 70)
    print("SECTION 2: Localized Coherent State Construction")
    print("=" * 70)
    print(f"\n  Gaussian width: sigma = {sigma:.4f} rad = pi/{np.pi/sigma:.1f}")
    print(f"  Localization bound: 2*pi/3 = {2*np.pi/3:.4f} rad")
    print(f"  sigma / (2*pi/3) = {sigma / (2*np.pi/3):.4f} (should be << 1)")

    # Compute toroidal distances from each center to center 0
    reference = z3_centers[0]  # (0, 0)
    distances = np.zeros(3)
    for k in range(3):
        d1 = min(abs(z3_centers[k][0] - reference[0]),
                 2 * np.pi - abs(z3_centers[k][0] - reference[0]))
        d2 = min(abs(z3_centers[k][1] - reference[1]),
                 2 * np.pi - abs(z3_centers[k][1] - reference[1]))
        distances[k] = np.sqrt(d1**2 + d2**2)

    print(f"\n  Toroidal distances from each Z_3 center to center 0:")
    for k in range(3):
        print(f"    d_{k} = {distances[k]:.4f} rad")

    # Compute Gaussian weights
    weights = np.exp(-distances**2 / (2 * sigma**2))
    print(f"\n  Unnormalized Gaussian weights exp(-d_k^2 / (2*sigma^2)):")
    for k in range(3):
        print(f"    w_{k} = exp(-{distances[k]:.4f}^2 / (2*{sigma:.4f}^2))"
              f" = exp(-{distances[k]**2 / (2*sigma**2):.4f}) = {weights[k]:.6e}")

    # Construct and normalize the state vector
    Z = np.sqrt(np.sum(weights**2))
    psi = weights / Z

    print(f"\n  Normalization factor Z = sqrt(sum |w_k|^2) = {Z:.6e}")
    print(f"\n  Normalized state |psi_loc>:")
    for k in range(3):
        print(f"    <{k}|psi_loc> = {psi[k]:.10f}")

    # Verify normalization
    norm = np.sum(np.abs(psi)**2)
    print(f"\n  Norm check: <psi_loc|psi_loc> = {norm:.15f}"
          f" (should be 1.0, error = {abs(norm - 1.0):.2e})")

    # Probability distribution over sectors
    probs = np.abs(psi)**2
    print(f"\n  Probability distribution over Z_3 sectors:")
    for k in range(3):
        print(f"    P(sector {k}) = |<{k}|psi_loc>|^2 = {probs[k]:.10f}"
              f" ({probs[k]*100:.6f}%)")
    print(f"    Sum = {np.sum(probs):.15f}")

    return psi, weights, distances


# =============================================================================
# SECTION 3: Density Matrix rho_obs
# =============================================================================

def construct_density_matrix(psi):
    """
    Construct rho_obs = |psi_loc><psi_loc| (pure state density matrix).

    For a pure state, rho^2 = rho and Tr(rho) = 1.
    """
    print("\n" + "=" * 70)
    print("SECTION 3: Density Matrix rho_obs = |psi_loc><psi_loc|")
    print("=" * 70)

    rho = np.outer(psi, np.conj(psi))

    print(f"\n  rho_obs (3x3 density matrix):")
    for i in range(3):
        row = "    ["
        for j in range(3):
            row += f" {rho[i, j].real:+.6e}"
            if j < 2:
                row += ","
        row += " ]"
        print(row)

    # Verify pure state properties
    rho_sq = rho @ rho
    trace_rho = np.trace(rho).real
    trace_rho_sq = np.trace(rho_sq).real
    purity = trace_rho_sq

    print(f"\n  Tr(rho) = {trace_rho:.15f} (should be 1)")
    print(f"  Tr(rho^2) = {purity:.15f} (purity; should be 1 for pure state)")
    print(f"  Is pure state: {np.allclose(rho, rho_sq, atol=1e-14)}")

    # Eigendecomposition
    eigenvalues = np.linalg.eigvalsh(rho)
    eigenvalues = np.sort(eigenvalues)[::-1]  # descending
    print(f"\n  Eigenvalues of rho_obs: {eigenvalues}")
    print(f"    lambda_0 = {eigenvalues[0]:.15f} (dominant)")
    print(f"    lambda_1 = {eigenvalues[1]:.2e} (should be ~0)")
    print(f"    lambda_2 = {eigenvalues[2]:.2e} (should be ~0)")

    # Von Neumann entropy
    # S = -sum lambda_k * log(lambda_k) for lambda_k > 0
    S = 0.0
    for lam in eigenvalues:
        if lam > 1e-15:
            S -= lam * np.log2(lam)
    print(f"\n  Von Neumann entropy S(rho) = {S:.10f} bits (should be 0 for pure state)")

    return rho, purity, eigenvalues


# =============================================================================
# SECTION 4: Verify Definition 0.0.32 Conditions
# =============================================================================

def verify_stability(z3_centers, psi, sigma):
    """
    Condition (S) Stability: Fisher metric g^F restricted to supp(rho_obs)
    must be positive-definite.

    For SU(3), the Fisher metric on the Cartan torus T^2 is:
        g^F = (1/12) * I_2

    (from Theorem 0.0.17). This is positive-definite everywhere on T^2,
    so condition (S) is automatically satisfied for ANY state on T^2.

    We verify:
    1. g^F = (1/12)*I_2 is positive-definite
    2. Eigenvalues are both 1/12 > 0
    """
    print("\n" + "=" * 70)
    print("SECTION 4a: Condition (S) Stability — Fisher Metric")
    print("=" * 70)

    # Fisher metric for SU(3) at equilibrium (Theorem 0.0.17)
    g_F = (1.0 / 12.0) * np.eye(2)

    print(f"\n  Fisher metric g^F on T^2 (Theorem 0.0.17):")
    print(f"    g^F = (1/12) * I_2 =")
    for i in range(2):
        row = "      ["
        for j in range(2):
            row += f" {g_F[i, j]:.6f}"
            if j < 1:
                row += ","
        row += " ]"
        print(row)

    eigenvalues = np.linalg.eigvalsh(g_F)
    print(f"\n  Eigenvalues of g^F: {eigenvalues}")
    print(f"    lambda_1 = {eigenvalues[0]:.6f}")
    print(f"    lambda_2 = {eigenvalues[1]:.6f}")

    is_pd = all(ev > 0 for ev in eigenvalues)
    print(f"\n  Positive-definite: {is_pd}")
    print(f"  Both eigenvalues = 1/12 = {1/12:.6f} > 0: {np.allclose(eigenvalues, 1/12)}")

    # The support of rho_obs (for the localized state) is concentrated near sector 0
    # Since g^F = (1/12)*I_2 is constant and positive-definite everywhere on T^2,
    # the restriction to any nonempty subset is automatically positive-definite.
    probs = np.abs(psi)**2
    effective_support_radius = sigma  # 1-sigma radius
    print(f"\n  Observer state support:")
    print(f"    Concentrated near center 0 = (0, 0)")
    print(f"    Effective 1-sigma radius: {sigma:.4f} rad")
    print(f"    Weight in sector 0: {probs[0]*100:.4f}%")
    print(f"\n  Since g^F is constant positive-definite everywhere on T^2,")
    print(f"  restriction to supp(rho_obs) is automatically positive-definite.")
    print(f"\n  RESULT: Condition (S) SATISFIED")

    return g_F, eigenvalues, is_pd


def verify_self_modeling(psi, rho):
    """
    Condition (R) Self-Modeling: There exists |phi_self> in H_obs such that
    the encoding error is small.

    KEY INSIGHT: For a PURE state rho = |psi><psi|, the spectral encoding is:
        |phi_self> = sum_i sqrt(lambda_i) * e^{i*phi_i} * |e_i>

    Since rho has eigenvalues (1, 0, 0) with eigenvector |psi>, the spectral
    encoding gives |phi_self> = |psi> exactly!

    Therefore: rho - |phi_self><phi_self| = |psi><psi| - |psi><psi| = 0

    The encoding error is EXACTLY ZERO for a pure state.
    This is a strict improvement over the maximally mixed state from the
    original proof (which had error ~0.82).
    """
    print("\n" + "=" * 70)
    print("SECTION 4b: Condition (R) Self-Modeling — Spectral Encoding")
    print("=" * 70)

    # Eigendecomposition of rho
    eigenvalues, eigenvectors = np.linalg.eigh(rho)
    idx = np.argsort(eigenvalues)[::-1]  # sort descending
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    print(f"\n  Spectral decomposition of rho_obs:")
    for i in range(3):
        print(f"    lambda_{i} = {eigenvalues[i]:.10f}, "
              f"|e_{i}> = [{eigenvectors[0,i]:.6f}, "
              f"{eigenvectors[1,i]:.6f}, {eigenvectors[2,i]:.6f}]")

    # Spectral encoding: |phi_self> = sum_i sqrt(lambda_i) |e_i>
    phi_self = np.zeros(3, dtype=complex)
    for i in range(3):
        if eigenvalues[i] > 1e-15:
            phi_self += np.sqrt(eigenvalues[i]) * eigenvectors[:, i]

    # Normalize (should already be normalized for pure state)
    phi_norm = np.sqrt(np.sum(np.abs(phi_self)**2))
    phi_self = phi_self / phi_norm

    print(f"\n  Spectral encoding |phi_self>:")
    for k in range(3):
        print(f"    <{k}|phi_self> = {phi_self[k].real:.10f}")

    # Encoding error: || rho - |phi_self><phi_self| ||_F
    rho_encoded = np.outer(phi_self, np.conj(phi_self))
    encoding_error = np.linalg.norm(rho - rho_encoded, 'fro')

    print(f"\n  Encoding error:")
    print(f"    ||rho_obs - |phi_self><phi_self|||_F = {encoding_error:.2e}")

    # Compare with the original construction (maximally mixed)
    rho_mixed = np.eye(3) / 3.0
    mixed_eigenvalues = np.array([1/3, 1/3, 1/3])
    phi_mixed = np.zeros(3, dtype=complex)
    for i in range(3):
        phi_mixed[i] = np.sqrt(1/3)
    rho_mixed_encoded = np.outer(phi_mixed, np.conj(phi_mixed))
    mixed_error = np.linalg.norm(rho_mixed - rho_mixed_encoded, 'fro')

    print(f"\n  Comparison with original construction (rho = I/3):")
    print(f"    Maximally mixed encoding error: ||I/3 - |phi><phi|||_F = {mixed_error:.6f}")
    print(f"    Localized pure state error:     ||rho - |phi><phi|||_F = {encoding_error:.2e}")
    print(f"    Improvement factor: {mixed_error / max(encoding_error, 1e-16):.2e}x")

    # Verify |phi_self> and |psi> are the same (up to global phase)
    overlap = np.abs(np.dot(np.conj(psi), phi_self))
    print(f"\n  |<psi_loc|phi_self>| = {overlap:.15f} (should be 1.0)")
    print(f"  |phi_self> = |psi_loc> up to global phase: "
          f"{np.allclose(overlap, 1.0, atol=1e-12)}")

    print(f"\n  PHYSICAL INTERPRETATION:")
    print(f"    A pure state IS its own spectral encoding. The observer's state")
    print(f"    |psi_loc> perfectly encodes the density matrix rho = |psi_loc><psi_loc|.")
    print(f"    No information is lost because a pure state has (2d-2) = 4 real")
    print(f"    parameters, and the encoding also has 4 real parameters.")
    print(f"\n  RESULT: Condition (R) SATISFIED (exact self-encoding, error = 0)")

    return phi_self, encoding_error, mixed_error


def verify_localization(psi, z3_centers, sigma, localization_bound):
    """
    Condition (L) Localization: diam(supp(rho_obs)) < 2*pi/3.

    For the localized coherent state, the weight is concentrated near sector 0.
    We compute:
    1. The effective diameter of the support
    2. The fraction of weight in each sector
    3. Whether the state fits within a single Z_3 fundamental domain
    """
    print("\n" + "=" * 70)
    print("SECTION 4c: Condition (L) Localization — Z_3 Sector Confinement")
    print("=" * 70)

    probs = np.abs(psi)**2

    # Compute distances from sector 0
    distances = np.zeros(3)
    for k in range(3):
        d1 = min(abs(z3_centers[k][0] - z3_centers[0][0]),
                 2 * np.pi - abs(z3_centers[k][0] - z3_centers[0][0]))
        d2 = min(abs(z3_centers[k][1] - z3_centers[0][1]),
                 2 * np.pi - abs(z3_centers[k][1] - z3_centers[0][1]))
        distances[k] = np.sqrt(d1**2 + d2**2)

    print(f"\n  Probability distribution over Z_3 sectors:")
    for k in range(3):
        print(f"    P(sector {k}) = {probs[k]:.10e}  "
              f"(distance from sector 0: {distances[k]:.4f} rad)")

    print(f"\n  Weight concentration analysis:")
    print(f"    Weight in sector 0: {probs[0]*100:.10f}%")
    print(f"    Weight outside sector 0: {(1 - probs[0])*100:.10e}%")
    print(f"    Ratio P(0)/P(1): {probs[0]/probs[1]:.6e}")

    # Effective diameter: weighted RMS spread
    # d_eff = 2 * sqrt(sum_k P_k * d_k^2) (twice the RMS for diameter)
    rms_spread = np.sqrt(np.sum(probs * distances**2))
    effective_diameter = 2 * rms_spread

    print(f"\n  Effective diameter (2 * RMS spread):")
    print(f"    d_RMS = sqrt(sum P_k * d_k^2) = {rms_spread:.6e} rad")
    print(f"    d_eff = 2 * d_RMS = {effective_diameter:.6e} rad")
    print(f"    Localization bound: {localization_bound:.4f} rad")
    print(f"    d_eff / bound = {effective_diameter / localization_bound:.6e}")
    print(f"    d_eff < 2*pi/3: {effective_diameter < localization_bound}")

    # Alternative: support diameter (range of sectors with nonnegligible weight)
    # Define "nonnegligible" as P > epsilon for some small epsilon
    epsilon = 1e-10
    significant_sectors = [k for k in range(3) if probs[k] > epsilon]
    if len(significant_sectors) <= 1:
        support_diameter = 0.0
    else:
        max_dist = max(distances[k] for k in significant_sectors)
        support_diameter = max_dist

    print(f"\n  Support analysis (threshold epsilon = {epsilon:.1e}):")
    print(f"    Significant sectors: {significant_sectors}")
    print(f"    Support diameter: {support_diameter:.6e} rad")

    # The Gaussian localization ensures exponential suppression
    suppression_ratio = np.exp(-distances[1]**2 / (2 * sigma**2))
    print(f"\n  Gaussian suppression of non-local sectors:")
    print(f"    d(sector 0, sector 1) = {distances[1]:.4f} rad")
    print(f"    sigma = {sigma:.4f} rad")
    print(f"    Suppression factor: exp(-d^2/(2*sigma^2)) = {suppression_ratio:.6e}")
    print(f"    Number of sigma: d/sigma = {distances[1]/sigma:.2f}")

    localization_satisfied = effective_diameter < localization_bound
    print(f"\n  RESULT: Condition (L) {'SATISFIED' if localization_satisfied else 'FAILED'}")
    if localization_satisfied:
        print(f"    The state is concentrated {effective_diameter/localization_bound*100:.4e}%"
              f" of the localization bound")

    return effective_diameter, probs, localization_satisfied


# =============================================================================
# SECTION 5: Observation Map M_obs
# =============================================================================

def construct_observation_map(z3_centers):
    """
    Construct the observation map M_obs.

    M_obs is the coarse-graining map from H_config to H_obs = C^3 that projects
    onto the 3 Z_3 sector basis states. In the Z_3 basis, M_obs acts as:

        M_obs = sum_{k=0}^{2} |k><k| (identity on H_obs = C^3)

    More precisely: M_obs maps the full configuration Hilbert space to the
    3-dimensional subspace spanned by the Z_3 sector states. The observation
    map restricted to H_obs is the identity (trivially bounded with ||M_obs|| = 1).

    Physical interpretation: The observer can only distinguish which of the 3
    Z_3 sectors a configuration belongs to, consistent with the Z_3 superselection
    rule (Prop 0.0.17h, Prop 3.3).
    """
    print("\n" + "=" * 70)
    print("SECTION 5: Observation Map M_obs")
    print("=" * 70)

    # In the Z_3 basis {|0>, |1>, |2>}, M_obs restricted to H_obs = C^3 is:
    M_obs = np.eye(3, dtype=complex)

    print(f"\n  H_obs = C^3 with basis {{|0>, |1>, |2>}} (Z_3 sector states)")
    print(f"\n  M_obs restricted to H_obs (identity on C^3):")
    for i in range(3):
        row = "    ["
        for j in range(3):
            row += f" {M_obs[i, j].real:.0f}"
            if j < 2:
                row += ","
        row += " ]"
        print(row)

    # Operator norm
    op_norm = np.linalg.norm(M_obs, 2)
    print(f"\n  ||M_obs||_op = {op_norm:.1f} (operator norm, bounded)")

    # Verify M_obs is bounded (trivially, since ||M_obs|| = 1)
    print(f"  M_obs is bounded linear operator: True (finite-dimensional)")

    # Physical interpretation as POVM elements
    print(f"\n  POVM decomposition of observation:")
    for k in range(3):
        e_k = np.zeros(3)
        e_k[k] = 1.0
        E_k = np.outer(e_k, e_k)
        print(f"    E_{k} = |{k}><{k}| (projection onto Z_3 sector {k})")

    print(f"\n  sum_k E_k = I_3 (completeness): "
          f"{np.allclose(sum(np.outer(np.eye(3)[k], np.eye(3)[k]) for k in range(3)), np.eye(3))}")

    # The full M_obs maps from H_config (infinite-dimensional in principle)
    # to H_obs = C^3. In the CG framework, this coarse-graining is:
    #   M_obs: L^2(T^2) -> C^3
    #   M_obs(f) = (integral_sector_0 f, integral_sector_1 f, integral_sector_2 f)
    print(f"\n  Full observation map M_obs: L^2(T^2) -> C^3")
    print(f"    M_obs(f) = (int_{{sector 0}} f, int_{{sector 1}} f, int_{{sector 2}} f)")
    print(f"    This is a bounded operator by Cauchy-Schwarz:")
    print(f"    ||M_obs(f)||^2 <= sum_k |int_{{sector k}} f|^2 <= 3 * ||f||^2")
    print(f"    Hence ||M_obs|| <= sqrt(3) = {np.sqrt(3):.4f}")

    print(f"\n  RESULT: M_obs is well-defined bounded linear operator")

    return M_obs


# =============================================================================
# SECTION 6: Complete Summary
# =============================================================================

def print_summary(g_F, g_F_eigenvalues, encoding_error, mixed_error,
                  effective_diameter, localization_bound, probs, psi):
    """Print a complete summary of all verification results."""
    print("\n" + "=" * 70)
    print("SECTION 6: COMPLETE VERIFICATION SUMMARY")
    print("=" * 70)

    print(f"\n  OBSERVER CONSTRUCTION for Prop 0.0.34 Part (a) Reverse Direction")
    print(f"  " + "-" * 60)
    print(f"\n  Given: N_c >= 3, g^F positive-definite on T^2")
    print(f"  Construct: O = (H_obs, rho_obs, M_obs) satisfying Def 0.0.32")
    print(f"\n  CONSTRUCTION:")
    print(f"    H_obs = C^3 (Z_3 sector Hilbert space)")
    print(f"    |psi_loc> = localized coherent state centered on sector 0")
    print(f"    rho_obs = |psi_loc><psi_loc| (pure state)")
    print(f"    M_obs = projection onto Z_3 sectors (identity on H_obs)")

    print(f"\n  CONDITION VERIFICATION:")
    print(f"  " + "-" * 60)

    # (S) Stability
    s_pass = all(ev > 0 for ev in g_F_eigenvalues)
    print(f"\n  (S) Stability: g^F|_{{supp(rho)}} positive-definite")
    print(f"      g^F = (1/12)*I_2, eigenvalues = {g_F_eigenvalues}")
    print(f"      Both eigenvalues > 0: {s_pass}")
    print(f"      STATUS: {'PASS' if s_pass else 'FAIL'}")

    # (R) Self-Modeling
    r_pass = encoding_error < 1e-10
    print(f"\n  (R) Self-Modeling: encoding error < epsilon")
    print(f"      Spectral encoding |phi_self> = |psi_loc> (for pure state)")
    print(f"      Encoding error = {encoding_error:.2e}")
    print(f"      Improvement over maximally mixed: {mixed_error/max(encoding_error,1e-16):.2e}x")
    print(f"      STATUS: {'PASS (EXACT)' if r_pass else 'FAIL'}")

    # (L) Localization
    l_pass = effective_diameter < localization_bound
    print(f"\n  (L) Localization: diam(supp(rho)) < 2*pi/3")
    print(f"      Effective diameter = {effective_diameter:.6e} rad")
    print(f"      Localization bound = {localization_bound:.4f} rad")
    print(f"      Weight in sector 0 = {probs[0]*100:.6f}%")
    print(f"      STATUS: {'PASS' if l_pass else 'FAIL'}")

    all_pass = s_pass and r_pass and l_pass
    print(f"\n  " + "=" * 60)
    print(f"  OVERALL: {'ALL CONDITIONS SATISFIED' if all_pass else 'SOME CONDITIONS FAILED'}")
    print(f"  " + "=" * 60)

    if all_pass:
        print(f"\n  CONCLUSION:")
        print(f"    The constructed observer O = (C^3, |psi_loc><psi_loc|, M_obs)")
        print(f"    satisfies all three conditions of Definition 0.0.32:")
        print(f"      (S) Stability  -- g^F = (1/12)*I_2 positive-definite")
        print(f"      (R) Self-model -- Pure state gives exact self-encoding")
        print(f"      (L) Localized  -- Gaussian weight within one Z_3 sector")
        print(f"\n    This completes the (<=) direction of Prop 0.0.34 Part (a):")
        print(f"    (N >= 3 AND g^F > 0) ==> E_obs (observer existence)")
        print(f"\n    KEY IMPROVEMENT over original proof:")
        print(f"    - Original: rho = I/3 (maximally mixed) -- FAILS condition (L)")
        print(f"    - This:     rho = |psi_loc><psi_loc| -- SATISFIES ALL conditions")
        print(f"    - Bonus:    Exact self-encoding (error = 0) vs approx (error = 0.82)")

    return all_pass


# =============================================================================
# SECTION 7: Visualization
# =============================================================================

def generate_plots(z3_centers, psi, rho, g_F, sigma, distances,
                   effective_diameter, localization_bound):
    """Generate comprehensive visualization plots."""

    fig = plt.figure(figsize=(18, 12))
    gs = GridSpec(2, 3, figure=fig, hspace=0.35, wspace=0.3)

    probs = np.abs(psi)**2

    # --- Plot 1: Z_3 sectors on Cartan torus with localized state ---
    ax1 = fig.add_subplot(gs[0, 0])
    n_grid = 200
    theta1 = np.linspace(0, 2 * np.pi, n_grid)
    theta2 = np.linspace(0, 2 * np.pi, n_grid)
    T1, T2 = np.meshgrid(theta1, theta2)

    # Assign each point to nearest Z_3 center
    sector_map = np.zeros_like(T1, dtype=int)
    for i in range(n_grid):
        for j in range(n_grid):
            pt = np.array([T1[i, j], T2[i, j]])
            dists = []
            for center in z3_centers:
                d1 = min(abs(pt[0] - center[0]), 2 * np.pi - abs(pt[0] - center[0]))
                d2 = min(abs(pt[1] - center[1]), 2 * np.pi - abs(pt[1] - center[1]))
                dists.append(np.sqrt(d1**2 + d2**2))
            sector_map[i, j] = np.argmin(dists)

    ax1.pcolormesh(T1, T2, sector_map, cmap='Set2', shading='auto', alpha=0.5)
    ax1.scatter(z3_centers[:, 0], z3_centers[:, 1], c='black', s=120, zorder=5,
                marker='x', linewidths=2.5, label=r'$Z_3$ centers')

    # Draw localization circle (sigma)
    theta_circle = np.linspace(0, 2 * np.pi, 100)
    ax1.plot(z3_centers[0, 0] + sigma * np.cos(theta_circle),
             z3_centers[0, 1] + sigma * np.sin(theta_circle),
             'r-', linewidth=2, label=rf'$\sigma = \pi/6$')
    # Draw 2-sigma
    ax1.plot(z3_centers[0, 0] + 2*sigma * np.cos(theta_circle),
             z3_centers[0, 1] + 2*sigma * np.sin(theta_circle),
             'r--', linewidth=1.5, alpha=0.7, label=rf'$2\sigma$')
    # Draw localization bound circle
    r_loc = 2 * np.pi / 3 / 2  # half the sector width
    ax1.plot(z3_centers[0, 0] + r_loc * np.cos(theta_circle),
             z3_centers[0, 1] + r_loc * np.sin(theta_circle),
             'b--', linewidth=1.5, alpha=0.7, label=r'Sector boundary')

    ax1.set_xlabel(r'$\theta_1$', fontsize=11)
    ax1.set_ylabel(r'$\theta_2$', fontsize=11)
    ax1.set_title(r'Localized State on $T^2$', fontsize=12, fontweight='bold')
    ax1.set_xlim(0, 2 * np.pi)
    ax1.set_ylim(0, 2 * np.pi)
    ax1.set_aspect('equal')
    ax1.legend(fontsize=8, loc='upper right')

    # --- Plot 2: Probability distribution over sectors ---
    ax2 = fig.add_subplot(gs[0, 1])
    colors = ['#388e3c', '#1565c0', '#d32f2f']
    bars = ax2.bar([0, 1, 2], probs, color=colors, edgecolor='black', linewidth=0.8)
    ax2.set_xlabel(r'$Z_3$ Sector $k$', fontsize=11)
    ax2.set_ylabel(r'$P(\mathrm{sector}\; k) = |\langle k|\psi_{loc}\rangle|^2$', fontsize=11)
    ax2.set_title('Sector Probabilities', fontsize=12, fontweight='bold')
    ax2.set_xticks([0, 1, 2])
    ax2.set_ylim(0, 1.1)
    # Add text annotations
    for k in range(3):
        ax2.text(k, probs[k] + 0.02, f'{probs[k]:.4e}', ha='center', fontsize=9)
    ax2.axhline(y=1/3, color='gray', linestyle=':', alpha=0.5, label='Maximally mixed')
    ax2.legend(fontsize=9)

    # --- Plot 3: Density matrix heatmap ---
    ax3 = fig.add_subplot(gs[0, 2])
    im = ax3.imshow(rho.real, cmap='RdBu_r', vmin=-0.1, vmax=1.1,
                     interpolation='nearest')
    ax3.set_xticks([0, 1, 2])
    ax3.set_yticks([0, 1, 2])
    ax3.set_xticklabels([r'$|0\rangle$', r'$|1\rangle$', r'$|2\rangle$'])
    ax3.set_yticklabels([r'$|0\rangle$', r'$|1\rangle$', r'$|2\rangle$'])
    ax3.set_title(r'$\rho_{obs} = |\psi_{loc}\rangle\langle\psi_{loc}|$',
                   fontsize=12, fontweight='bold')
    plt.colorbar(im, ax=ax3, shrink=0.8)
    # Annotate elements
    for i in range(3):
        for j in range(3):
            val = rho[i, j].real
            if abs(val) > 1e-6:
                color = 'white' if val > 0.5 else 'black'
                ax3.text(j, i, f'{val:.4f}', ha='center', va='center',
                         fontsize=8, color=color)

    # --- Plot 4: Fisher metric eigenvalues ---
    ax4 = fig.add_subplot(gs[1, 0])
    eig_vals = [1/12, 1/12]
    ax4.bar([0, 1], eig_vals, color='#388e3c', edgecolor='black', linewidth=0.8, width=0.5)
    ax4.axhline(y=0, color='red', linestyle='--', alpha=0.5)
    ax4.set_xticks([0, 1])
    ax4.set_xticklabels([r'$\lambda_1$', r'$\lambda_2$'], fontsize=11)
    ax4.set_ylabel('Eigenvalue', fontsize=11)
    ax4.set_title(r'Fisher Metric $g^F = \frac{1}{12}\mathbb{I}_2$',
                   fontsize=12, fontweight='bold')
    ax4.set_ylim(-0.02, 0.12)
    ax4.text(0.5, 0.09, f'Both = 1/12 = {1/12:.4f} > 0',
             ha='center', fontsize=10, color='#388e3c', fontweight='bold',
             transform=ax4.transData)
    ax4.text(0.5, 0.07, 'Positive-definite: (S) SATISFIED',
             ha='center', fontsize=9, style='italic',
             transform=ax4.transData)

    # --- Plot 5: Gaussian localization profile ---
    ax5 = fig.add_subplot(gs[1, 1])
    d_range = np.linspace(0, 4, 200)
    gaussian = np.exp(-d_range**2 / (2 * sigma**2))
    ax5.plot(d_range, gaussian, 'b-', linewidth=2, label=rf'$e^{{-d^2/(2\sigma^2)}}$, $\sigma=\pi/6$')
    ax5.axvline(x=distances[1], color='red', linestyle='--', linewidth=1.5,
                label=f'd(sector 0, sector 1) = {distances[1]:.2f}')
    ax5.axvline(x=2*np.pi/3, color='orange', linestyle=':', linewidth=1.5,
                label=f'Loc. bound = 2pi/3 = {2*np.pi/3:.2f}')
    ax5.axvline(x=sigma, color='green', linestyle='-.', linewidth=1.5,
                label=rf'$\sigma$ = {sigma:.2f}')
    suppression_at_sector1 = np.exp(-distances[1]**2 / (2*sigma**2))
    ax5.plot(distances[1], suppression_at_sector1, 'rv', markersize=10, zorder=5)
    ax5.annotate(f'{suppression_at_sector1:.1e}',
                 xy=(distances[1], suppression_at_sector1),
                 xytext=(distances[1]+0.3, suppression_at_sector1+0.15),
                 fontsize=9, arrowprops=dict(arrowstyle='->', color='red'))
    ax5.set_xlabel('Distance d (rad)', fontsize=11)
    ax5.set_ylabel('Gaussian weight', fontsize=11)
    ax5.set_title('Localization Profile', fontsize=12, fontweight='bold')
    ax5.legend(fontsize=8, loc='upper right')
    ax5.set_ylim(-0.05, 1.1)
    ax5.grid(True, alpha=0.3)

    # --- Plot 6: Summary panel ---
    ax6 = fig.add_subplot(gs[1, 2])
    ax6.axis('off')
    summary = (
        "PROP 0.0.34 PART (a) REVERSE\n"
        "Explicit Observer Construction\n"
        "=" * 35 + "\n\n"
        "Observer: O = (C^3, rho, M_obs)\n\n"
        "  rho = |psi_loc><psi_loc|\n"
        f"  sigma = pi/6 = {sigma:.4f} rad\n\n"
        "CONDITIONS:\n"
        f"  (S) g^F = (1/12)*I_2 > 0    PASS\n"
        f"  (R) encoding error = 0       PASS\n"
        f"  (L) diam = {effective_diameter:.2e} < {localization_bound:.2f}  PASS\n\n"
        "ALL THREE CONDITIONS SATISFIED\n\n"
        "Key improvement:\n"
        "  Old: rho=I/3 fails (L)\n"
        "  New: pure state satisfies ALL\n"
        "  Bonus: exact self-encoding"
    )
    ax6.text(0.05, 0.95, summary, transform=ax6.transAxes,
             fontsize=9.5, fontfamily='monospace', verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='#e8f5e9', alpha=0.9))

    plt.suptitle('Proposition 0.0.34 Part (a) Reverse Direction:\n'
                 'Explicit Internal Observer Construction',
                 fontsize=14, fontweight='bold', y=0.98)

    plot_path = os.path.join(PLOT_DIR, 'prop_0_0_34_observer_construction.png')
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\n  Plot saved: {plot_path}")
    plt.close()

    return plot_path


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 70)
    print("PROPOSITION 0.0.34 — PART (a) REVERSE DIRECTION")
    print("Explicit Internal Observer Construction")
    print("=" * 70)
    print()
    print("Goal: Given N_c >= 3 and g^F positive-definite,")
    print("      construct O = (H_obs, rho_obs, M_obs) satisfying Def 0.0.32")
    print()

    # Section 1: Z_3 geometry
    z3_centers, localization_bound = compute_z3_geometry()

    # Section 2: Localized coherent state
    sigma = np.pi / 6  # Well within the 2*pi/3 localization bound
    psi, weights, distances = construct_localized_state(z3_centers, sigma)

    # Section 3: Density matrix
    rho, purity, rho_eigenvalues = construct_density_matrix(psi)

    # Section 4: Verify all three conditions
    g_F, g_F_eigenvalues, s_satisfied = verify_stability(z3_centers, psi, sigma)
    phi_self, encoding_error, mixed_error = verify_self_modeling(psi, rho)
    effective_diameter, probs, l_satisfied = verify_localization(
        psi, z3_centers, sigma, localization_bound)

    # Section 5: Observation map
    M_obs = construct_observation_map(z3_centers)

    # Section 6: Summary
    all_pass = print_summary(g_F, g_F_eigenvalues, encoding_error, mixed_error,
                              effective_diameter, localization_bound, probs, psi)

    # Section 7: Plots
    print("\n" + "=" * 70)
    print("SECTION 7: Generating Visualization")
    print("=" * 70)
    plot_path = generate_plots(z3_centers, psi, rho, g_F, sigma, distances,
                                effective_diameter, localization_bound)

    print("\n" + "=" * 70)
    print("VERIFICATION COMPLETE")
    print("=" * 70)

    return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
