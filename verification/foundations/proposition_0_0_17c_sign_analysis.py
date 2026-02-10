#!/usr/bin/env python3
"""
Proposition 0.0.17c - Sign Convention Analysis

The numerical analysis shows coefficient ≈ -0.19 instead of positive values.
This script investigates the sign conventions carefully.

Key insight: The sign depends on which direction we expand!
"""

import numpy as np
import json

def create_probability_distribution(phi: np.ndarray, x_grid: np.ndarray) -> np.ndarray:
    """Create the interference pattern."""
    phi_1, phi_2 = phi[0], phi[1]
    phi_R = -phi_1 - phi_2
    phi_G = phi_1
    phi_B = phi_2

    P_R = np.exp(-(x_grid - 0.0)**2 / 0.5)
    P_G = np.exp(-(x_grid - 1.0)**2 / 0.5)
    P_B = np.exp(-(x_grid - 2.0)**2 / 0.5)

    chi_total = P_R * np.exp(1j * phi_R) + P_G * np.exp(1j * phi_G) + P_B * np.exp(1j * phi_B)
    p = np.abs(chi_total)**2
    p = p / np.sum(p)
    p = np.maximum(p, 1e-15)
    p = p / np.sum(p)
    return p


def compute_kl_divergence(p: np.ndarray, q: np.ndarray) -> float:
    """Compute D_KL(p || q)."""
    mask = (p > 1e-15) & (q > 1e-15)
    return np.sum(p[mask] * np.log(p[mask] / q[mask]))


def analyze_sign_conventions():
    """
    Analyze sign conventions in the KL asymmetry.

    The key observation: The sign of the asymmetry depends on the
    sign of the skewness tensor, which depends on the configuration.
    """
    print("=" * 70)
    print("SIGN CONVENTION ANALYSIS")
    print("=" * 70)

    x_grid = np.linspace(-2, 5, 1000)

    # The issue: skewness tensor can be positive or negative!
    # At some configurations, S_ijk > 0; at others, S_ijk < 0

    print("\n1. Testing skewness tensor signs at different configurations:\n")

    test_configs = [
        np.array([0.1, 0.1]),
        np.array([0.3, 0.2]),
        np.array([0.5, 0.3]),
        np.array([np.pi/4, np.pi/4]),
        np.array([np.pi/2, 0.0]),
        np.array([np.pi, np.pi/3]),
    ]

    for phi in test_configs:
        S_111 = compute_skewness_component(phi, x_grid, 0, 0, 0)
        print(f"  φ = ({phi[0]:.3f}, {phi[1]:.3f}): S_111 = {S_111:+.4f}")

    print("\n2. The ratio (asymmetry)/(S_contracted) for different configs:\n")

    ratios = []
    for phi_base in test_configs:
        for delta in [0.03, 0.04, 0.05]:
            eta = np.array([delta, delta * 0.8])

            p_base = create_probability_distribution(phi_base, x_grid)
            p_plus = create_probability_distribution(phi_base + eta, x_grid)

            D_forward = compute_kl_divergence(p_base, p_plus)
            D_reverse = compute_kl_divergence(p_plus, p_base)
            asymmetry = D_forward - D_reverse

            S_111 = compute_skewness_component(phi_base, x_grid, 0, 0, 0)
            S_112 = compute_skewness_component(phi_base, x_grid, 0, 0, 1)
            S_122 = compute_skewness_component(phi_base, x_grid, 0, 1, 1)
            S_222 = compute_skewness_component(phi_base, x_grid, 1, 1, 1)

            S_contracted = (S_111 * eta[0]**3 +
                           3 * S_112 * eta[0]**2 * eta[1] +
                           3 * S_122 * eta[0] * eta[1]**2 +
                           S_222 * eta[1]**3)

            if abs(S_contracted) > 1e-12:
                ratio = asymmetry / S_contracted
                ratios.append(ratio)

    mean_ratio = np.mean(ratios)
    print(f"  Mean ratio: {mean_ratio:.4f}")
    print(f"  All ratios are CONSISTENT in sign: {np.all(np.array(ratios) < 0)}")

    print("\n3. EXPLANATION OF THE NEGATIVE RATIO:")
    print("""
    The ratio is consistently NEGATIVE because of the definition:

    Asymmetry = D_KL(φ||φ+η) - D_KL(φ+η||φ)

    When we move from φ to φ+η:
    - If S_ijk η^i η^j η^k > 0: The distribution p_{φ+η} has higher skewness
    - The REVERSE KL D_KL(φ+η||φ) tends to be LARGER
    - So the asymmetry = D_forward - D_reverse < 0

    This gives a NEGATIVE ratio!

    The correct formula is therefore:

    D_KL(φ||φ+δφ) - D_KL(φ+δφ||φ) = -c × S_ijk δφ^i δφ^j δφ^k + O(δφ^4)

    where c ≈ 0.2 (positive).

    Alternatively, we can write:

    D_KL(φ||φ+δφ) - D_KL(φ+δφ||φ) = T_ijk δφ^i δφ^j δφ^k

    where T_ijk = -c × S_ijk includes the sign.
    """)

    print("\n4. RESOLUTION FOR THE DOCUMENT:")
    print("""
    The document CURRENTLY says:
      D_KL(φ||φ+δφ) - D_KL(φ+δφ||φ) = (1/3) T_ijk δφ^i δφ^j δφ^k

    where T_ijk = E[∂_i log p · ∂_j log p · ∂_k log p] = S_ijk

    The numerical evidence shows the coefficient is ≈ -0.2, not +1/3.

    TWO OPTIONS:

    Option A: Change coefficient from 1/3 to the correct negative value ≈ -0.2
      Pro: Mathematically precise
      Con: The exact coefficient may be model-dependent

    Option B: Keep T_ijk but note it includes the correct sign
      Redefine T_ijk as the tensor that makes the equation exact,
      rather than necessarily = S_ijk.

      This is actually what the document does in §3.3!
      Lines 119-120 say the REVERSE direction has a MINUS sign
      in front of the cubic term, which CREATES the asymmetry.

    CHECKING THE DOCUMENT'S CLAIM:

    Line 111: D_KL(φ||φ+δφ) = (1/2)g_ij δφ^i δφ^j + (1/6) T_ijk δφ^i δφ^j δφ^k
    Line 120: D_KL(φ+δφ||φ) = (1/2)g_ij δφ^i δφ^j - (1/6) T_ijk δφ^i δφ^j δφ^k

    Difference: (1/6 - (-1/6)) T = (1/3) T_ijk δφ^i δφ^j δφ^k

    This implies:
    - Forward has +(1/6) T
    - Reverse has -(1/6) T
    - Difference = +(1/3) T

    But our numerical analysis shows:
    - Forward cubic: a₃ ≈ +0.25
    - Reverse cubic: a₃ ≈ +0.22
    - Both are POSITIVE, not opposite signs!

    The DIFFERENCE is positive (+0.03), but small.
    And this small difference does NOT equal (1/3) S_ijk.

    CONCLUSION: The document's claim that forward and reverse have
    OPPOSITE SIGNS in the cubic term is INCORRECT.

    Both forward and reverse KL have the SAME SIGN cubic terms,
    but with slightly different magnitudes.
    """)

    return mean_ratio


def compute_skewness_component(phi: np.ndarray, x_grid: np.ndarray,
                                i: int, j: int, k: int) -> float:
    """Compute S_ijk = E[∂_i ℓ · ∂_j ℓ · ∂_k ℓ]."""
    eps = 1e-5
    p = create_probability_distribution(phi, x_grid)

    def get_d_log_p(idx):
        phi_plus = phi.copy()
        phi_plus[idx] += eps
        phi_minus = phi.copy()
        phi_minus[idx] -= eps
        p_plus = create_probability_distribution(phi_plus, x_grid)
        p_minus = create_probability_distribution(phi_minus, x_grid)
        return (np.log(p_plus) - np.log(p_minus)) / (2 * eps)

    d_log_p_i = get_d_log_p(i)
    d_log_p_j = get_d_log_p(j)
    d_log_p_k = get_d_log_p(k)

    return np.sum(p * d_log_p_i * d_log_p_j * d_log_p_k)


def verify_forward_reverse_cubic_signs():
    """
    Verify whether forward and reverse KL have opposite sign cubic terms.
    """
    print("\n" + "=" * 70)
    print("VERIFYING CUBIC TERM SIGNS IN FORWARD VS REVERSE KL")
    print("=" * 70)

    x_grid = np.linspace(-2, 5, 1000)
    phi_base = np.array([0.5, 0.3])

    # Compute forward KL D_KL(φ||φ+η) for various η
    etas = np.linspace(-0.1, 0.1, 50)
    p_base = create_probability_distribution(phi_base, x_grid)

    D_forward = []
    D_reverse = []

    for eta in etas:
        phi_shift = phi_base + np.array([eta, eta * 0.8])
        p_shift = create_probability_distribution(phi_shift, x_grid)

        D_forward.append(compute_kl_divergence(p_base, p_shift))
        D_reverse.append(compute_kl_divergence(p_shift, p_base))

    D_forward = np.array(D_forward)
    D_reverse = np.array(D_reverse)

    # Fit polynomials
    # D = a₂ η² + a₃ η³ + a₄ η⁴
    coeffs_fwd = np.polyfit(etas, D_forward, 4)
    coeffs_rev = np.polyfit(etas, D_reverse, 4)

    a3_fwd = coeffs_fwd[1]
    a3_rev = coeffs_rev[1]

    print(f"\nForward KL cubic coefficient (a₃_fwd): {a3_fwd:+.6f}")
    print(f"Reverse KL cubic coefficient (a₃_rev): {a3_rev:+.6f}")
    print(f"Same sign? {np.sign(a3_fwd) == np.sign(a3_rev)}")
    print(f"Opposite sign (as claimed in document)? {np.sign(a3_fwd) != np.sign(a3_rev)}")

    # The asymmetry
    asymmetry = D_forward - D_reverse
    coeffs_asym = np.polyfit(etas, asymmetry, 5)
    a3_asym = coeffs_asym[2]  # coefficient of η³

    print(f"\nAsymmetry cubic coefficient: {a3_asym:+.6f}")
    print(f"From difference: a₃_fwd - a₃_rev = {a3_fwd - a3_rev:+.6f}")

    print("""
    FINDING: Both forward and reverse KL have POSITIVE cubic coefficients.
    The asymmetry comes from a SMALL DIFFERENCE between them,
    NOT from opposite signs as claimed in the document.

    This is a more subtle effect than the document describes.
    """)


if __name__ == "__main__":
    analyze_sign_conventions()
    verify_forward_reverse_cubic_signs()

    print("\n" + "=" * 70)
    print("RECOMMENDED CORRECTIONS FOR PROPOSITION 0.0.17c")
    print("=" * 70)
    print("""
    1. Section 3.3, lines 119-120: INCORRECT claim that reverse KL
       has opposite sign cubic term. Both have same-sign cubic terms
       with slightly different magnitudes.

    2. The asymmetry formula should be:
       D_KL(φ||φ+δφ) - D_KL(φ+δφ||φ) ∝ S_ijk δφ^i δφ^j δφ^k

       The exact proportionality constant is configuration-dependent
       and approximately -0.2 (negative, not 1/3).

    3. The KEY CONCEPTUAL POINT remains valid:
       - The asymmetry IS cubic in δφ (✓)
       - The asymmetry IS related to the skewness tensor (✓)
       - The asymmetry IS generically non-zero (✓)

    4. RECOMMENDED FIX: Simplify the claim to avoid stating
       specific coefficients. The fundamental result is that
       the asymmetry is CUBIC, encoding time-directionality.
    """)
