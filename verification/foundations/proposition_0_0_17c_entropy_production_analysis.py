#!/usr/bin/env python3
"""
Proposition 0.0.17c - Entropy Production Discrepancy Analysis

This script investigates the discrepancy between:
- Theorem 2.2.3: σ = 3K/4 (from 2D Jacobian)
- Theorem 2.2.5: σ = 3K/2 (claimed)
- Theorem 2.2.6: σ = 3K (from 3D Jacobian?)

Key question: What is the correct entropy production rate, and why
do different theorems use different values?
"""

import numpy as np
from typing import Tuple

# ============================================================================
# SYSTEM PARAMETERS
# ============================================================================

K = 1.0  # Coupling strength (normalized)
alpha = 2 * np.pi / 3  # Phase shift

# ============================================================================
# PART 1: 2D REDUCED SYSTEM (ψ₁, ψ₂)
# ============================================================================

def f_2d(psi: np.ndarray) -> np.ndarray:
    """
    RHS of the 2D reduced system.

    ψ₁ = φ_G - φ_R
    ψ₂ = φ_B - φ_G

    From Theorem 2.2.3 equations.
    """
    psi1, psi2 = psi[0], psi[1]

    # Equations from Theorem 2.2.3, Step 2
    f1 = -K * np.sin(psi1) * np.cos(alpha) - (K/2) * np.sin(alpha - psi2) - (K/2) * np.sin(psi1 + psi2 - alpha)
    f2 = -K * np.sin(psi2) * np.cos(alpha) + (K/2) * np.sin(alpha + psi1) - (K/2) * np.sin(alpha + psi1 + psi2)

    return np.array([f1, f2])


def jacobian_2d(psi: np.ndarray, eps: float = 1e-7) -> np.ndarray:
    """Compute Jacobian of 2D system numerically."""
    n = len(psi)
    J = np.zeros((n, n))

    for j in range(n):
        psi_plus = psi.copy()
        psi_minus = psi.copy()
        psi_plus[j] += eps
        psi_minus[j] -= eps

        J[:, j] = (f_2d(psi_plus) - f_2d(psi_minus)) / (2 * eps)

    return J


def analyze_2d_system():
    """Analyze the 2D reduced system."""
    print("=" * 70)
    print("PART 1: 2D REDUCED SYSTEM (ψ₁, ψ₂)")
    print("=" * 70)

    # Forward fixed point
    psi_forward = np.array([2*np.pi/3, 2*np.pi/3])

    # Verify it's a fixed point
    f_at_fp = f_2d(psi_forward)
    print(f"\nForward fixed point: ψ* = ({psi_forward[0]:.4f}, {psi_forward[1]:.4f})")
    print(f"f(ψ*) = ({f_at_fp[0]:.2e}, {f_at_fp[1]:.2e}) ≈ 0 ✓")

    # Jacobian at forward fixed point
    J = jacobian_2d(psi_forward)
    print(f"\nJacobian at forward FP:")
    print(f"  J = [{J[0,0]:+.4f}  {J[0,1]:+.4f}]")
    print(f"      [{J[1,0]:+.4f}  {J[1,1]:+.4f}]")

    # Trace and eigenvalues
    trace = np.trace(J)
    eigenvalues = np.linalg.eigvals(J)

    print(f"\n  Tr(J) = {trace:.4f}")
    print(f"  Expected: -3K/4 = {-3*K/4:.4f}")

    print(f"\n  Eigenvalues: {eigenvalues[0]:.4f}, {eigenvalues[1]:.4f}")
    print(f"  Expected: -3K/8 ± i√3K/4 = {-3*K/8:.4f} ± {np.sqrt(3)*K/4:.4f}i")

    # Entropy production (phase-space contraction rate)
    sigma_2d = -trace
    print(f"\n  Phase-space contraction rate: σ = -Tr(J) = {sigma_2d:.4f}")
    print(f"  This matches Theorem 2.2.3: σ = 3K/4 = {3*K/4:.4f}")

    return sigma_2d


# ============================================================================
# PART 2: 3D FULL SYSTEM (φ_R, φ_G, φ_B)
# ============================================================================

def f_3d(phi: np.ndarray) -> np.ndarray:
    """
    RHS of the 3D full system.

    From Theorem 2.2.3 equations.
    """
    phi_R, phi_G, phi_B = phi[0], phi[1], phi[2]
    omega = 1.0  # Natural frequency (doesn't affect Jacobian)

    dphi_R = omega + (K/2) * (np.sin(phi_G - phi_R - alpha) + np.sin(phi_B - phi_R - alpha))
    dphi_G = omega + (K/2) * (np.sin(phi_R - phi_G - alpha) + np.sin(phi_B - phi_G - alpha))
    dphi_B = omega + (K/2) * (np.sin(phi_R - phi_B - alpha) + np.sin(phi_G - phi_B - alpha))

    return np.array([dphi_R, dphi_G, dphi_B])


def jacobian_3d(phi: np.ndarray, eps: float = 1e-7) -> np.ndarray:
    """Compute Jacobian of 3D system numerically."""
    n = len(phi)
    J = np.zeros((n, n))

    for j in range(n):
        phi_plus = phi.copy()
        phi_minus = phi.copy()
        phi_plus[j] += eps
        phi_minus[j] -= eps

        J[:, j] = (f_3d(phi_plus) - f_3d(phi_minus)) / (2 * eps)

    return J


def analyze_3d_system():
    """Analyze the 3D full system."""
    print("\n" + "=" * 70)
    print("PART 2: 3D FULL SYSTEM (φ_R, φ_G, φ_B)")
    print("=" * 70)

    # Forward fixed point (phases locked at 120° separation, rotating)
    # At t=0, take φ_R = 0, φ_G = 2π/3, φ_B = 4π/3
    phi_forward = np.array([0.0, 2*np.pi/3, 4*np.pi/3])

    # Verify it's on the limit cycle (f should give ω for all components)
    f_at_fp = f_3d(phi_forward)
    print(f"\nForward configuration: φ = ({phi_forward[0]:.4f}, {phi_forward[1]:.4f}, {phi_forward[2]:.4f})")
    print(f"f(φ) = ({f_at_fp[0]:.4f}, {f_at_fp[1]:.4f}, {f_at_fp[2]:.4f})")
    print("(All should be equal to ω = 1.0, confirming uniform rotation)")

    # Jacobian at this point
    J = jacobian_3d(phi_forward)
    print(f"\nJacobian in 3D:")
    print(f"  J = [{J[0,0]:+.4f}  {J[0,1]:+.4f}  {J[0,2]:+.4f}]")
    print(f"      [{J[1,0]:+.4f}  {J[1,1]:+.4f}  {J[1,2]:+.4f}]")
    print(f"      [{J[2,0]:+.4f}  {J[2,1]:+.4f}  {J[2,2]:+.4f}]")

    # Trace and eigenvalues
    trace = np.trace(J)
    eigenvalues = np.linalg.eigvals(J)

    print(f"\n  Tr(J_3D) = {trace:.4f}")
    print(f"  Eigenvalues: {eigenvalues[0]:.4f}, {eigenvalues[1]:.4f}, {eigenvalues[2]:.4f}")

    # One eigenvalue should be 0 (corresponding to direction along limit cycle)
    sorted_eigs = sorted(eigenvalues, key=lambda x: abs(x.real))
    print(f"\n  One eigenvalue ≈ 0: {sorted_eigs[0]:.4f} (direction along limit cycle)")
    print(f"  Other two: {sorted_eigs[1]:.4f}, {sorted_eigs[2]:.4f} (transverse directions)")

    # Entropy production in 3D
    sigma_3d = -trace
    print(f"\n  Phase-space contraction rate: σ = -Tr(J_3D) = {sigma_3d:.4f}")

    return sigma_3d


# ============================================================================
# PART 3: RECONCILIATION
# ============================================================================

def reconcile_values():
    """Explain the relationship between different σ values."""
    print("\n" + "=" * 70)
    print("PART 3: RECONCILIATION OF ENTROPY PRODUCTION VALUES")
    print("=" * 70)

    sigma_2d = 3*K/4
    sigma_3d_limit_cycle = 3*K/4  # Same! (one eigenvalue is 0)

    print(f"""
    KEY FINDING: The 2D and 3D systems give the SAME σ = 3K/4

    2D Reduced System (ψ₁, ψ₂):
    - Tr(J_2D) = -3K/4
    - σ_2D = 3K/4 ✓

    3D Full System (φ_R, φ_G, φ_B):
    - Tr(J_3D) = -3K/4 (numerically verified above)
    - σ_3D = 3K/4 ✓

    The 3D Jacobian has:
    - One zero eigenvalue (direction along limit cycle)
    - Two eigenvalues with Re = -3K/8 (same as 2D)

    Since Tr(J) = sum of eigenvalues = 0 + (-3K/8) + (-3K/8 + small imaginary) ≈ -3K/4

    THE DISCREPANCY IN THE DOCUMENTS:

    1. Theorem 2.2.3 says σ = 3K/4 ← CORRECT (computed from Jacobian)

    2. Theorem 2.2.5 says σ = 3K/2 ← NEEDS INVESTIGATION
       - References Theorem 2.2.3, but claims 3K/2
       - This is a factor of 2 error OR a different definition

    3. Theorem 2.2.6 says σ = 3K ← DIFFERENT CALCULATION
       - Claims Tr(J) = -3K/2 - 3K/2 = -3K
       - This appears to be INCORRECT (our calculation gives -3K/4)
    """)


def investigate_theorem_2_2_6_claim():
    """
    Theorem 2.2.6 claims Tr(J) = -3K/2 - 3K/2 = -3K.
    Let's see if there's any interpretation that makes this correct.
    """
    print("\n" + "=" * 70)
    print("INVESTIGATING THEOREM 2.2.6 CLAIM")
    print("=" * 70)

    print("""
    Theorem 2.2.6 line 125 says:
    "The factor of 3 comes from the Jacobian trace: σ = -Tr(J) = -(-3K/2 - 3K/2) = 3K"

    This would require diagonal elements J_11 = J_22 = -3K/2.

    But our 2D Jacobian is:
    J = [[0, 3K/4], [-3K/4, -3K/4]]

    With J_11 = 0 and J_22 = -3K/4, giving Tr = -3K/4.

    POSSIBLE EXPLANATIONS:

    1. DIFFERENT COORDINATE SYSTEM
       Perhaps Theorem 2.2.6 uses a different parameterization of the phase space.

    2. DIFFERENT MODEL VARIANT
       The "target-specific" vs "symmetric" Sakaguchi-Kuramoto models might differ.

    3. TYPOGRAPHICAL ERROR
       The formula Tr(J) = -3K/2 - 3K/2 appears to be incorrect.

    4. FACTOR COUNTING ISSUE
       Perhaps the "3" factor refers to something else (3 color phases?).

    MOST LIKELY: The value in Theorem 2.2.3 (σ = 3K/4) is correct, and
    Theorem 2.2.5 and 2.2.6 have propagated an error from an earlier version.
    """)


def compute_analytical_jacobian():
    """Compute the Jacobian analytically to verify."""
    print("\n" + "=" * 70)
    print("ANALYTICAL JACOBIAN COMPUTATION")
    print("=" * 70)

    print("""
    For the 2D system with:
    f₁ = -K sin(ψ₁) cos(α) - (K/2) sin(α - ψ₂) - (K/2) sin(ψ₁ + ψ₂ - α)
    f₂ = -K sin(ψ₂) cos(α) + (K/2) sin(α + ψ₁) - (K/2) sin(α + ψ₁ + ψ₂)

    At the fixed point (ψ₁*, ψ₂*) = (2π/3, 2π/3) with α = 2π/3:

    ∂f₁/∂ψ₁ = -K cos(ψ₁) cos(α) - (K/2) cos(ψ₁ + ψ₂ - α)
            = -K cos(2π/3) cos(2π/3) - (K/2) cos(2π/3)
            = -K(-1/2)(-1/2) - (K/2)(-1/2)
            = -K/4 + K/4 = 0 ✓

    ∂f₁/∂ψ₂ = (K/2) cos(α - ψ₂) - (K/2) cos(ψ₁ + ψ₂ - α)
            = (K/2) cos(0) - (K/2) cos(2π/3)
            = K/2 - (K/2)(-1/2)
            = K/2 + K/4 = 3K/4 ✓

    ∂f₂/∂ψ₁ = (K/2) cos(α + ψ₁) - (K/2) cos(α + ψ₁ + ψ₂)
            = (K/2) cos(4π/3) - (K/2) cos(2π)
            = (K/2)(-1/2) - (K/2)(1)
            = -K/4 - K/2 = -3K/4 ✓

    ∂f₂/∂ψ₂ = -K cos(ψ₂) cos(α) - (K/2) cos(α + ψ₁ + ψ₂)
            = -K cos(2π/3) cos(2π/3) - (K/2) cos(2π)
            = -K(-1/2)(-1/2) - (K/2)(1)
            = -K/4 - K/2 = -3K/4 ✓

    Therefore:
    J = [[0, 3K/4], [-3K/4, -3K/4]]

    Tr(J) = 0 + (-3K/4) = -3K/4

    σ = -Tr(J) = 3K/4 ← THIS IS CORRECT
    """)


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    print("ENTROPY PRODUCTION DISCREPANCY ANALYSIS")
    print("Investigating σ = 3K/4 vs 3K/2 vs 3K")
    print("=" * 70)

    sigma_2d = analyze_2d_system()
    sigma_3d = analyze_3d_system()

    reconcile_values()
    investigate_theorem_2_2_6_claim()
    compute_analytical_jacobian()

    print("\n" + "=" * 70)
    print("FINAL CONCLUSION")
    print("=" * 70)
    print(f"""
    VERIFIED: σ = 3K/4 is CORRECT

    The discrepancy arises from:
    1. Theorem 2.2.3: σ = 3K/4 ← CORRECT (rigorous derivation)
    2. Theorem 2.2.5: Claims σ = 3K/2 ← ERROR (factor of 2 too large)
    3. Theorem 2.2.6: Claims σ = 3K ← ERROR (factor of 4 too large)

    Proposition 0.0.17c uses σ = 3K/2 from Theorem 2.2.5, which is incorrect.

    RECOMMENDATION:
    - Update Proposition 0.0.17c to use σ = 3K/4
    - Update Theorem 2.2.5 to reference the correct value from Theorem 2.2.3
    - Update Theorem 2.2.6 to fix the Jacobian trace calculation
    """)
