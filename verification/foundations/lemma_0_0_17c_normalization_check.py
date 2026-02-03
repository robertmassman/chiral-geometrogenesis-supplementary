#!/usr/bin/env python3
"""
Lemma 0.0.17c Normalization Check

Verify the normalization conventions for the Killing metric and Fisher metric.
This addresses the factor of 2 discrepancy between 1/(2N) and 1/12 for N=3.

Key question: In which coordinate system is g^K = (1/2N) I and when is it (1/12) I?
"""

import numpy as np

def killing_form_cartan_subalgebra():
    """
    Compute the Killing form on the Cartan subalgebra of su(N).

    For su(N), the Cartan subalgebra consists of traceless diagonal matrices:
        H = diag(h_1, h_2, ..., h_N) with sum(h_i) = 0

    The Killing form is B(H, H') = Tr(ad_H ∘ ad_H')

    For su(N): B(H, H') = 2N * sum_i h_i h'_i
    """

    print("=" * 70)
    print("KILLING FORM ON CARTAN SUBALGEBRA OF SU(N)")
    print("=" * 70)

    for N in [2, 3, 4]:
        print(f"\n--- N = {N} (SU({N})) ---")

        # Compute Killing form by explicit adjoint representation
        # The root system of SU(N) has N(N-1) roots
        # For H = diag(h_1, ..., h_N), ad_H acts on root vector E_ij by:
        #   [H, E_ij] = (h_i - h_j) E_ij

        # B(H, H') = sum_{i≠j} (h_i - h_j)(h'_i - h'_j)
        #          = sum_{i≠j} (h_i h'_i + h_j h'_j - h_i h'_j - h_j h'_i)
        #          = 2(N-1) sum_i h_i h'_i - 2 sum_{i≠j} h_i h'_j
        #          = 2(N-1) sum_i h_i h'_i - 2 (sum_i h_i)(sum_j h'_j) + 2 sum_i h_i h'_i
        #          = 2N sum_i h_i h'_i - 2 (sum_i h_i)(sum_j h'_j)
        # For traceless: sum h = sum h' = 0, so B(H,H') = 2N sum h_i h'_i

        print(f"  Killing form: B(H, H') = 2N × Σ h_i h'_i = {2*N} × Σ h_i h'_i")
        print(f"  For compact groups, B < 0, so metric g = -B/c for normalization c")

        # Standard convention: g^K such that the metric tensor is g^K_ij = (1/2N) δ_ij
        # This means we use g = -B / (4N^2)... let me verify

        # Actually, the convention is:
        # g^K_ij = (1/2N) δ_ij on the Cartan torus
        # This comes from choosing normalization such that the longest root has length^2 = 2

        print(f"  Standard normalization: g^K = (1/{2*N}) I on weight coordinates")
        print(f"    → g^K = (1/{4*N}) I on root coordinates (factor √2 rescaling)")


def coordinate_conventions():
    """
    Explain the different coordinate conventions.
    """

    print("\n" + "=" * 70)
    print("COORDINATE CONVENTIONS")
    print("=" * 70)

    print("""
For SU(3), the Cartan torus is 2-dimensional with constraint Σφ_c = 0.

1. WEIGHT COORDINATES (ψ_1, ψ_2):
   - ψ_1 = φ_2 - φ_1
   - ψ_2 = φ_3 - φ_1
   - The metric in these coordinates: g^K = (1/6) I_2

2. SIMPLE ROOT COORDINATES (α_1, α_2):
   - Related to weight coordinates by the Cartan matrix
   - For SU(3): A = [[2, -1], [-1, 2]]
   - Roots α_1, α_2 are at 120° angle
   - Metric is NOT diagonal in these coordinates

3. ORTHONORMAL ROOT COORDINATES (normalized):
   - Rescaled to make metric = I
   - φ = (√6/2) × original

4. THEOREM 0.0.17 CONVENTION:
   - Uses h_1, h_2 with constraint h_1 + h_2 + h_3 = 0
   - Where h_i are eigenvalues of diagonal Cartan elements
   - With Tr(T_a T_b) = (1/2) delta_ab normalization
   - The metric: g = (1/12) I_2

   This is (1/6) × (1/2) = (1/12)
   The extra 1/2 comes from the Tr(T_a T_b) = 1/2 normalization
   vs the natural Killing form normalization
""")


def verify_factor_of_2():
    """
    Verify where the factor of 2 comes from.
    """

    print("\n" + "=" * 70)
    print("THE FACTOR OF 2 EXPLANATION")
    print("=" * 70)

    N = 3

    print(f"""
For SU({N}):

1. KILLING FORM on Cartan subalgebra:
   B(H, H') = 2N x sum_i h_i h'_i = {2*N} x sum_i h_i h'_i

2. INDUCED METRIC from Killing form:
   g^K_ij = (1/4N^2) x (-B_ij) x normalization

3. WITH STANDARD NORMALIZATION Tr(Ta Tb) = 1/2 delta_ab:
   - The Cartan generators Ta (a = 1,2 for SU(3)) have:
   - For SU(3): T3 = (1/2)diag(1,-1,0), T8 = (1/2sqrt3)diag(1,1,-2)
   - These satisfy Tr(Ta Tb) = (1/2) delta_ab

4. THE KILLING METRIC in this basis:
   - g^K(Ta, Tb) = Tr(ad_Ta ad_Tb)
   - For SU(N), with the 1/2 normalization: g^K_ab = (1/2) delta_ab
   - On the Cartan subalgebra: g^K = (1/2) I_2

5. BUT we want metric in COORDINATE space (h_1, h_2):
   - H = h_1 T3 + h_2 T8 (in Cartan-Weyl basis)
   - Jacobian factor from (T3, T8) to (h_1, h_2) coordinates

Actually, let me just compute directly...
""")

    # Direct computation for SU(3)
    print("\nDirect computation for SU(3):")
    print("-" * 40)

    # Cartan generators with Tr(T_a T_b) = 1/2 delta_ab
    T3 = np.diag([1, -1, 0]) / 2
    T8 = np.diag([1, 1, -2]) / (2 * np.sqrt(3))

    print(f"T^3 = (1/2)diag(1,-1,0)")
    print(f"T^8 = (1/2√3)diag(1,1,-2)")

    print(f"\nTr(T^3 T^3) = {np.trace(T3 @ T3):.4f}  (should be 1/2)")
    print(f"Tr(T^8 T^8) = {np.trace(T8 @ T8):.4f}  (should be 1/2)")
    print(f"Tr(T^3 T^8) = {np.trace(T3 @ T8):.4f}  (should be 0)")

    # Killing form on these generators
    # For su(N), B(X,Y) = 2N Tr(XY)
    B_33 = 2 * N * np.trace(T3 @ T3)
    B_88 = 2 * N * np.trace(T8 @ T8)
    B_38 = 2 * N * np.trace(T3 @ T8)

    print(f"\nKilling form B(T_a, T_b) = 2N × Tr(T_a T_b):")
    print(f"B(T^3, T^3) = {B_33:.4f}")
    print(f"B(T^8, T^8) = {B_88:.4f}")
    print(f"B(T^3, T^8) = {B_38:.4f}")

    # The induced metric (positive definite, so -B for compact groups)
    g_K = np.array([[B_33, B_38], [B_38, B_88]]) * (-1)  # Negative for compact
    # But actually, for the standard convention, we use g = B/(-2N)
    g_K_normalized = np.array([[B_33, B_38], [B_38, B_88]]) / (-2*N)

    print(f"\nKilling metric g^K = -B / (normalization):")
    print(f"If we use g = -B directly: g = {-B_33:.4f} I_2")
    print(f"If we use g = -B/(2N): g = {-B_33/(2*N):.4f} I_2")

    # What Theorem 0.0.17 uses
    print(f"\n" + "=" * 70)
    print("THEOREM 0.0.17 CONVENTION")
    print("=" * 70)

    print("""
Theorem 0.0.17 works in h-coordinates where H = diag(h_1, h_2, h_3)
with h_1 + h_2 + h_3 = 0.

Independent coordinates: (h_1, h_2) with h_3 = -h_1 - h_2.

The metric on this space:
- From B(H,H') = 2N Σ h_i h'_i with constraint
- In (h_1, h_2) coordinates:
  g_11 = 2N × (∂h/∂h_1)·(∂h/∂h_1) = 2N × [1 + (∂h_3/∂h_1)²] = 2N × [1 + 1] = 4N
  Wait, this isn't right...

Let me reconsider. If B(H,H') = 2N Σ h_i h'_i, then in the basis
(h_1, h_2) with h_3 = -h_1 - h_2:

B(H,H') = 2N × [h_1 h'_1 + h_2 h'_2 + (-h_1-h_2)(-h'_1-h'_2)]
        = 2N × [h_1 h'_1 + h_2 h'_2 + h_1 h'_1 + h_1 h'_2 + h_2 h'_1 + h_2 h'_2]
        = 2N × [2h_1 h'_1 + 2h_2 h'_2 + h_1 h'_2 + h_2 h'_1]

So B_11 = 4N, B_22 = 4N, B_12 = 2N

This is NOT diagonal! The metric is:
g = (-1/normalization) × [[4N, 2N], [2N, 4N]]

For g^K = (1/12) I_2, we need normalization such that
(1/normalization) × [[4N, 2N], [2N, 4N]] = (1/12) I_2

For N=3: [[12, 6], [6, 12]] / normalization = (1/12) I_2

This doesn't work directly - the matrix [[12, 6], [6, 12]] isn't a multiple of I!

The resolution: COORDINATE TRANSFORMATION to diagonalize.
""")

    # Eigenvalues of [[4N, 2N], [2N, 4N]]
    for N in [3]:
        M = np.array([[4*N, 2*N], [2*N, 4*N]])
        eigvals, eigvecs = np.linalg.eigh(M)
        print(f"\nFor N={N}, matrix [[4N, 2N], [2N, 4N]] = {M.tolist()}")
        print(f"Eigenvalues: {eigvals}")
        print(f"Ratio: {eigvals[1]/eigvals[0]:.2f}")

        # Eigenvectors are (1,1)/√2 and (1,-1)/√2
        # These correspond to:
        # - (1,1) direction: h_1 + h_2 = -h_3 direction
        # - (1,-1) direction: h_1 - h_2 direction

        print(f"\nEigenvectors:")
        print(f"  λ = {eigvals[0]}: v = {eigvecs[:,0]} ≈ (1,-1)/√2")
        print(f"  λ = {eigvals[1]}: v = {eigvecs[:,1]} ≈ (1,1)/√2")

        print(f"\n→ In diagonal coordinates, g_K ∝ diag({eigvals[0]}, {eigvals[1]})")
        print(f"→ This is NOT proportional to I_2!")

    print("""
RESOLUTION OF THE DISCREPANCY:

The Killing metric in the (h_1, h_2) coordinates is NOT proportional to I_2!
It has the form g = [[2/3, 1/3], [1/3, 2/3]] × (some constant).

Theorem 0.0.17's claim that g^K = (1/12) I_2 must be using a DIFFERENT
coordinate system - likely the orthogonal simple root coordinates or
weight coordinates where the metric IS diagonal.

The factor of (1/6) vs (1/12) depends on which coordinates are used.
""")


def correct_normalization():
    """
    Derive the correct normalization convention.
    """

    print("\n" + "=" * 70)
    print("CORRECT NORMALIZATION CONVENTION")
    print("=" * 70)

    print("""
For SU(3), there are several common coordinate systems:

1. CARTAN-WEYL coordinates (T^3, T^8 basis):
   With Tr(T_a T_b) = (1/2) delta_ab, the metric is g = (1/2) I_2
   (This is the "fundamental representation" normalization)

2. WEIGHT coordinates (ψ_1 = φ_2-φ_1, ψ_2 = φ_3-φ_1):
   The metric is g = (1/2) × [[2, 1], [1, 2]] / 3 = (1/3) × [[2, 1], [1, 2]]

3. SIMPLE ROOT coordinates (α_1, α_2 at 120°):
   The metric reflects the Cartan matrix A = [[2,-1],[-1,2]]

4. ORTHONORMAL coordinates:
   By construction, g = c × I_2 for some c

The statement "g^K = (1/12) I_2" is only valid in orthonormal coordinates.

For Lemma 0.0.17c, the key claim is g^F ∝ g^K, which is TRUE regardless
of coordinate system. The proportionality constant depends on conventions.

RECOMMENDED STATEMENT:
"g^F = c_N × g^K where c_N depends on amplitude and generator normalizations"

For the specific values:
- In fundamental rep normalization: g^K eigenvalues are (1/6, 1/2) in (h_1, h_2)
- After diagonalization: both eigenvalues can be set to 1/(2N) by appropriate rescaling
""")

    # Verify numerically
    N = 3

    # The Killing form in (h_1, h_2) coordinates
    B = np.array([[4*N, 2*N], [2*N, 4*N]])  # B(H,H') = 2N Σ h_i h'_i with constraint

    # Metric is -B / normalization
    # Standard: g = -B / (4N^2) gives eigenvalues 1/(2N), 1/(6N)

    eigvals_B = np.linalg.eigvalsh(B)
    print(f"\nNumerical check for N={N}:")
    print(f"Killing form B in (h_1, h_2): eigenvalues = {eigvals_B}")

    for norm in [1, 2*N, 4*N**2]:
        g = B / norm
        eigvals_g = np.linalg.eigvalsh(g)
        print(f"  g = B/{norm}: eigenvalues = {eigvals_g}")


if __name__ == "__main__":
    killing_form_cartan_subalgebra()
    coordinate_conventions()
    verify_factor_of_2()
    correct_normalization()
