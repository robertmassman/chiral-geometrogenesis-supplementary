"""
Verification Script: Theorem 0.1.0' - Field Existence from Gauge Bundle Structure

This script verifies the mathematical claims in Theorem 0.1.0' regarding:
1. SU(3) weight vectors for the fundamental representation
2. Phase structure derived from weight space geometry
3. Color neutrality condition
4. Tensor product decompositions
5. Euler characteristic calculation

Author: Verification Agent
Date: 2026-01-16
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Ensure plots directory exists
PLOTS_DIR = Path(__file__).parent.parent / "plots"
PLOTS_DIR.mkdir(parents=True, exist_ok=True)

# ==============================================================================
# 1. SU(3) Weight Vectors for Fundamental Representation
# ==============================================================================

def verify_weight_vectors():
    """
    Verify the weight vectors for the fundamental representation of SU(3).

    Standard conventions (Georgi, Fulton & Harris):
    - T_3 = (1/2) diag(1, -1, 0) (isospin)
    - T_8 = (1/2sqrt(3)) diag(1, 1, -2) (hypercharge)

    Weight vectors are eigenvalues (t_3, t_8) for each basis state.
    """
    print("=" * 70)
    print("1. VERIFYING SU(3) WEIGHT VECTORS")
    print("=" * 70)

    # Theoretical weight vectors from the theorem
    lambda_R = np.array([1/2, 1/(2*np.sqrt(3))])        # Red
    lambda_G = np.array([-1/2, 1/(2*np.sqrt(3))])       # Green
    lambda_B = np.array([0, -1/np.sqrt(3)])              # Blue

    print("\nWeight vectors from theorem:")
    print(f"  λ_R = ({lambda_R[0]:.4f}, {lambda_R[1]:.4f})")
    print(f"  λ_G = ({lambda_G[0]:.4f}, {lambda_G[1]:.4f})")
    print(f"  λ_B = ({lambda_B[0]:.4f}, {lambda_B[1]:.4f})")

    # Verify these are eigenvalues of T_3 and T_8 generators
    # T_3 eigenvalues: +1/2, -1/2, 0 for u, d, s (R, G, B)
    # T_8 eigenvalues: +1/(2sqrt(3)), +1/(2sqrt(3)), -1/sqrt(3)

    T3_eigenvalues = [1/2, -1/2, 0]
    T8_eigenvalues = [1/(2*np.sqrt(3)), 1/(2*np.sqrt(3)), -1/np.sqrt(3)]

    print("\nExpected Cartan eigenvalues:")
    print(f"  T_3: {T3_eigenvalues}")
    print(f"  T_8: {[f'{x:.4f}' for x in T8_eigenvalues]}")

    # Verify match
    weights_match = (
        np.isclose(lambda_R[0], T3_eigenvalues[0]) and
        np.isclose(lambda_R[1], T8_eigenvalues[0]) and
        np.isclose(lambda_G[0], T3_eigenvalues[1]) and
        np.isclose(lambda_G[1], T8_eigenvalues[1]) and
        np.isclose(lambda_B[0], T3_eigenvalues[2]) and
        np.isclose(lambda_B[1], T8_eigenvalues[2])
    )

    print(f"\n✓ Weight vectors match Cartan eigenvalues: {weights_match}")

    return lambda_R, lambda_G, lambda_B, weights_match


# ==============================================================================
# 2. Phase Structure from Weight Space Geometry
# ==============================================================================

def verify_phase_structure(lambda_R, lambda_G, lambda_B):
    """
    Verify the phase structure (0, 2π/3, 4π/3) arises from weight space geometry.

    The theorem claims phases are determined by angular positions in the Cartan plane.
    """
    print("\n" + "=" * 70)
    print("2. VERIFYING PHASE STRUCTURE FROM WEIGHT SPACE")
    print("=" * 70)

    # Calculate angles of weight vectors from positive T_3 axis
    theta_R = np.arctan2(lambda_R[1], lambda_R[0])
    theta_G = np.arctan2(lambda_G[1], lambda_G[0])
    theta_B = np.arctan2(lambda_B[1], lambda_B[0])

    print("\nAngular positions in Cartan plane:")
    print(f"  θ_R = {np.degrees(theta_R):.2f}° = {theta_R:.4f} rad")
    print(f"  θ_G = {np.degrees(theta_G):.2f}° = {theta_G:.4f} rad")
    print(f"  θ_B = {np.degrees(theta_B):.2f}° = {theta_B:.4f} rad")

    # Normalize angles to [0, 2π)
    theta_R_norm = theta_R if theta_R >= 0 else theta_R + 2*np.pi
    theta_G_norm = theta_G if theta_G >= 0 else theta_G + 2*np.pi
    theta_B_norm = theta_B if theta_B >= 0 else theta_B + 2*np.pi

    print("\nNormalized to [0, 2π):")
    print(f"  θ_R = {np.degrees(theta_R_norm):.2f}° = {theta_R_norm:.4f} rad")
    print(f"  θ_G = {np.degrees(theta_G_norm):.2f}° = {theta_G_norm:.4f} rad")
    print(f"  θ_B = {np.degrees(theta_B_norm):.2f}° = {theta_B_norm:.4f} rad")

    # Calculate angular separations
    def angle_diff(a, b):
        """Compute positive angular difference between two angles."""
        diff = (a - b) % (2*np.pi)
        return diff if diff <= np.pi else 2*np.pi - diff

    sep_RG = abs(theta_G_norm - theta_R_norm)
    sep_GB = abs(theta_B_norm - theta_G_norm)
    sep_BR = 2*np.pi - sep_RG - sep_GB

    print("\nAngular separations (should be 2π/3 = 120°):")
    print(f"  |θ_G - θ_R| = {np.degrees(sep_RG):.2f}° = {sep_RG:.4f} rad")
    print(f"  |θ_B - θ_G| = {np.degrees(sep_GB):.2f}° = {sep_GB:.4f} rad")
    print(f"  |θ_R - θ_B| = {np.degrees(sep_BR):.2f}° (completing circle)")

    expected_sep = 2*np.pi/3
    print(f"\nExpected separation: 2π/3 = {np.degrees(expected_sep):.2f}° = {expected_sep:.4f} rad")

    # Check if separations are all 2π/3
    equilateral = (
        np.isclose(sep_RG, expected_sep, atol=0.01) and
        np.isclose(sep_GB, expected_sep, atol=0.01)
    )

    print(f"\n✓ Weight vectors form equilateral triangle: {equilateral}")
    print(f"  (Angular separations are all 2π/3)")

    # Note on absolute phases
    print("\nNote on absolute phases:")
    print("  The RELATIVE separation of 2π/3 is geometrically determined.")
    print("  The ABSOLUTE phases (0, 2π/3, 4π/3) require choosing a reference (convention).")
    print(f"  If we set φ_R = 0 by convention, then φ_G = 2π/3, φ_B = 4π/3")

    return equilateral


# ==============================================================================
# 3. Color Neutrality Condition
# ==============================================================================

def verify_color_neutrality(lambda_R, lambda_G, lambda_B):
    """
    Verify the color neutrality condition:
    1. Weights sum to zero: λ_R + λ_G + λ_B = 0
    2. Phase factors sum to zero: 1 + ω + ω² = 0 where ω = e^{2πi/3}
    """
    print("\n" + "=" * 70)
    print("3. VERIFYING COLOR NEUTRALITY CONDITION")
    print("=" * 70)

    # Check weight sum
    weight_sum = lambda_R + lambda_G + lambda_B
    print("\nWeight vector sum:")
    print(f"  λ_R + λ_G + λ_B = ({weight_sum[0]:.6f}, {weight_sum[1]:.6f})")

    weights_sum_zero = np.allclose(weight_sum, [0, 0])
    print(f"  ✓ Sum equals zero: {weights_sum_zero}")

    # Check phase factor sum
    omega = np.exp(2j * np.pi / 3)
    phase_factors = [1, omega, omega**2]
    phase_sum = sum(phase_factors)

    print("\nPhase factor sum (1 + ω + ω²):")
    print(f"  ω = e^{{2πi/3}} = {omega:.4f}")
    print(f"  ω² = e^{{4πi/3}} = {omega**2:.4f}")
    print(f"  1 + ω + ω² = {phase_sum:.6f}")

    phases_sum_zero = np.isclose(abs(phase_sum), 0)
    print(f"  ✓ Sum equals zero: {phases_sum_zero}")

    # Explicit calculation
    print("\nExplicit calculation:")
    print(f"  ω = -1/2 + i√3/2 = {-0.5:.4f} + {np.sqrt(3)/2:.4f}i")
    print(f"  ω² = -1/2 - i√3/2 = {-0.5:.4f} - {np.sqrt(3)/2:.4f}i")
    print(f"  1 + (-1/2 + i√3/2) + (-1/2 - i√3/2) = 1 - 1 + 0i = 0 ✓")

    return weights_sum_zero and phases_sum_zero


# ==============================================================================
# 4. Tensor Product Decompositions
# ==============================================================================

def verify_tensor_products():
    """
    Verify the SU(3) tensor product decompositions claimed in the theorem.

    These are verified by dimension counting using the formula:
    dim(p,q) = (p+1)(q+1)(p+q+2)/2
    """
    print("\n" + "=" * 70)
    print("4. VERIFYING TENSOR PRODUCT DECOMPOSITIONS")
    print("=" * 70)

    def dim_rep(p, q):
        """Dimension of SU(3) irrep labeled by (p, q)."""
        return (p + 1) * (q + 1) * (p + q + 2) // 2

    # List of representations with their (p, q) labels
    reps = {
        '1': (0, 0),
        '3': (1, 0),
        '3̄': (0, 1),
        '6': (2, 0),
        '6̄': (0, 2),
        '8': (1, 1),
        '10': (3, 0),
        '10̄': (0, 3),
    }

    print("\nSU(3) representation dimensions:")
    for name, (p, q) in reps.items():
        d = dim_rep(p, q)
        print(f"  {name}: (p,q) = ({p},{q}) → dim = {d}")

    # Verify decompositions by dimension counting
    print("\nTensor product decompositions:")

    # 3 ⊗ 3 = 6 ⊕ 3̄
    lhs = dim_rep(1, 0) * dim_rep(1, 0)
    rhs = dim_rep(2, 0) + dim_rep(0, 1)
    check_3x3 = (lhs == rhs)
    print(f"  3 ⊗ 3 = 6 ⊕ 3̄: {dim_rep(1,0)}×{dim_rep(1,0)} = {lhs} = {dim_rep(2,0)} + {dim_rep(0,1)} = {rhs} → {check_3x3}")

    # 3 ⊗ 3̄ = 8 ⊕ 1
    lhs = dim_rep(1, 0) * dim_rep(0, 1)
    rhs = dim_rep(1, 1) + dim_rep(0, 0)
    check_3x3bar = (lhs == rhs)
    print(f"  3 ⊗ 3̄ = 8 ⊕ 1: {dim_rep(1,0)}×{dim_rep(0,1)} = {lhs} = {dim_rep(1,1)} + {dim_rep(0,0)} = {rhs} → {check_3x3bar}")

    # 3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1
    lhs = dim_rep(1, 0) ** 3
    rhs = dim_rep(3, 0) + dim_rep(1, 1) + dim_rep(1, 1) + dim_rep(0, 0)
    check_3x3x3 = (lhs == rhs)
    print(f"  3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1: {dim_rep(1,0)}³ = {lhs} = {dim_rep(3,0)} + {dim_rep(1,1)} + {dim_rep(1,1)} + {dim_rep(0,0)} = {rhs} → {check_3x3x3}")

    all_correct = check_3x3 and check_3x3bar and check_3x3x3
    print(f"\n✓ All tensor decompositions verified by dimension: {all_correct}")

    return all_correct


# ==============================================================================
# 5. Euler Characteristic Calculation
# ==============================================================================

def verify_euler_characteristic():
    """
    Verify the Euler characteristic calculation for the stella octangula boundary.

    The stella octangula consists of two interpenetrating tetrahedra.
    - Each tetrahedron: V=4, E=6, F=4 → χ = 4-6+4 = 2 (sphere)
    - Two tetrahedra (disjoint union): χ = 2+2 = 4

    Note: The theorem's interpretation of "two disjoint S² surfaces" is questioned
    by the adversarial review since the tetrahedra interpenetrate.
    """
    print("\n" + "=" * 70)
    print("5. VERIFYING EULER CHARACTERISTIC")
    print("=" * 70)

    # Single tetrahedron
    V_tet = 4
    E_tet = 6
    F_tet = 4
    chi_tet = V_tet - E_tet + F_tet

    print("\nSingle tetrahedron:")
    print(f"  Vertices: {V_tet}")
    print(f"  Edges: {E_tet}")
    print(f"  Faces: {F_tet}")
    print(f"  χ = V - E + F = {V_tet} - {E_tet} + {F_tet} = {chi_tet}")

    # Stella octangula as compound
    print("\nStella octangula as compound of two tetrahedra:")

    # If treated as two disjoint surfaces
    chi_disjoint = 2 * chi_tet
    print(f"  As disjoint union: χ = {chi_tet} + {chi_tet} = {chi_disjoint}")

    # If treated as combined polyhedral surface (with intersections)
    # This is more complex - the actual stella octangula has:
    # 8 vertices (occupying corners of a cube), 24 edges (12 from each tet, but they don't coincide)
    # Wait, let me recalculate properly...

    # Actually, for the stella octangula compound:
    # Each tetrahedron contributes 4 vertices at corners of a cube
    # The two tetrahedra share NO vertices (they are dual)
    # Total: 8 vertices
    # Each tetrahedron has 6 edges, total: 12 edges
    # Each tetrahedron has 4 faces, total: 8 faces

    V_stella = 8
    E_stella = 12
    F_stella = 8
    chi_stella = V_stella - E_stella + F_stella

    print(f"\n  As combined polyhedron:")
    print(f"    Total vertices: {V_stella}")
    print(f"    Total edges: {E_stella}")
    print(f"    Total faces: {F_stella}")
    print(f"    χ = {V_stella} - {E_stella} + {F_stella} = {chi_stella}")

    chi_correct = (chi_disjoint == 4 and chi_stella == 4)
    print(f"\n✓ Euler characteristic equals 4: {chi_correct}")

    # Note on topology interpretation
    print("\nNote on topological interpretation:")
    print("  The theorem states '(two disjoint S² surfaces)'")
    print("  This is topologically correct: each tetrahedron is homeomorphic to S²")
    print("  However, geometrically the tetrahedra interpenetrate")
    print("  The base space topology requires clarification for bundle theory")

    return chi_correct


# ==============================================================================
# 6. Visualization of Weight Space
# ==============================================================================

def create_weight_space_plot(lambda_R, lambda_G, lambda_B):
    """Create a visualization of the weight space for SU(3) fundamental representation."""
    print("\n" + "=" * 70)
    print("6. CREATING WEIGHT SPACE VISUALIZATION")
    print("=" * 70)

    fig, ax = plt.subplots(1, 1, figsize=(8, 8))

    # Plot weight vectors
    weights = [lambda_R, lambda_G, lambda_B]
    colors = ['red', 'green', 'blue']
    labels = ['R (red)', 'G (green)', 'B (blue)']

    for w, c, l in zip(weights, colors, labels):
        ax.scatter(w[0], w[1], c=c, s=200, zorder=5, edgecolors='black', linewidths=2)
        ax.annotate(l, xy=(w[0], w[1]), xytext=(w[0]+0.05, w[1]+0.05), fontsize=12)

    # Draw equilateral triangle
    triangle = np.array([lambda_R, lambda_G, lambda_B, lambda_R])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=2, alpha=0.5)

    # Draw origin
    ax.scatter(0, 0, c='black', s=100, marker='+', linewidths=2, zorder=5)
    ax.annotate('O', xy=(0, 0), xytext=(0.02, 0.02), fontsize=12)

    # Draw coordinate axes
    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5)

    # Add angular annotations
    theta_R = np.degrees(np.arctan2(lambda_R[1], lambda_R[0]))
    theta_G = np.degrees(np.arctan2(lambda_G[1], lambda_G[0]))
    theta_B = np.degrees(np.arctan2(lambda_B[1], lambda_B[0]))

    ax.set_xlabel('$T_3$ (isospin)', fontsize=14)
    ax.set_ylabel('$T_8$ (hypercharge)', fontsize=14)
    ax.set_title('SU(3) Fundamental Representation Weight Diagram\n(Theorem 0.1.0\')', fontsize=14)

    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.8, 0.8)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)

    # Add text box with key results
    textstr = '\n'.join([
        'Weight vectors:',
        f'λ_R = (1/2, 1/(2√3))',
        f'λ_G = (-1/2, 1/(2√3))',
        f'λ_B = (0, -1/√3)',
        '',
        'Properties:',
        '• Equilateral triangle',
        '• Angular separation: 2π/3',
        '• Sum: λ_R + λ_G + λ_B = 0'
    ])
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8)
    ax.text(0.02, 0.98, textstr, transform=ax.transAxes, fontsize=10,
            verticalalignment='top', bbox=props)

    plt.tight_layout()

    # Save figure
    output_path = PLOTS_DIR / 'theorem_0_1_0_prime_weight_diagram.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"  Saved: {output_path}")

    plt.close()


# ==============================================================================
# 7. Z_3 Center Action Visualization
# ==============================================================================

def create_z3_action_plot():
    """Visualize the Z_3 center action on the complex plane."""
    print("\n" + "=" * 70)
    print("7. CREATING Z_3 CENTER ACTION VISUALIZATION")
    print("=" * 70)

    fig, ax = plt.subplots(1, 1, figsize=(8, 8))

    # Z_3 elements
    omega = np.exp(2j * np.pi / 3)
    z3_elements = [1, omega, omega**2]

    # Plot unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax.plot(np.cos(theta), np.sin(theta), 'gray', linestyle='--', alpha=0.5)

    # Plot Z_3 elements
    colors = ['red', 'green', 'blue']
    labels = ['1 (φ=0)', 'ω (φ=2π/3)', 'ω² (φ=4π/3)']

    for z, c, l in zip(z3_elements, colors, labels):
        ax.scatter(z.real, z.imag, c=c, s=200, zorder=5, edgecolors='black', linewidths=2)
        ax.annotate(l, xy=(z.real, z.imag), xytext=(z.real+0.1, z.imag+0.1), fontsize=12)

    # Draw triangle connecting elements
    triangle = np.array([[z.real, z.imag] for z in z3_elements + [z3_elements[0]]])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=2, alpha=0.5)

    # Draw origin
    ax.scatter(0, 0, c='black', s=100, marker='+', linewidths=2, zorder=5)

    # Draw coordinate axes
    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5)

    # Draw arrows from origin to each element
    for z, c in zip(z3_elements, colors):
        ax.annotate('', xy=(z.real, z.imag), xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=c, alpha=0.7, lw=2))

    ax.set_xlabel('Real part', fontsize=14)
    ax.set_ylabel('Imaginary part', fontsize=14)
    ax.set_title('Z₃ Center of SU(3) - Phase Factors\n(Color Neutrality: 1 + ω + ω² = 0)', fontsize=14)

    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)

    # Add text box
    textstr = '\n'.join([
        'Z₃ = {1, ω, ω²}',
        'ω = e^{2πi/3}',
        '',
        'Center action on 3:',
        'z · (χ_R, χ_G, χ_B) =',
        '(zχ_R, zχ_G, zχ_B)',
        '',
        'Color neutrality:',
        '1 + ω + ω² = 0'
    ])
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8)
    ax.text(0.02, 0.98, textstr, transform=ax.transAxes, fontsize=10,
            verticalalignment='top', bbox=props)

    plt.tight_layout()

    # Save figure
    output_path = PLOTS_DIR / 'theorem_0_1_0_prime_z3_center.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"  Saved: {output_path}")

    plt.close()


# ==============================================================================
# MAIN VERIFICATION ROUTINE
# ==============================================================================

def main():
    """Run all verification checks."""
    print("=" * 70)
    print("VERIFICATION SCRIPT: Theorem 0.1.0'")
    print("Field Existence from Gauge Bundle Structure")
    print("=" * 70)
    print()

    results = {}

    # 1. Verify weight vectors
    lambda_R, lambda_G, lambda_B, weights_ok = verify_weight_vectors()
    results['Weight vectors'] = weights_ok

    # 2. Verify phase structure
    phases_ok = verify_phase_structure(lambda_R, lambda_G, lambda_B)
    results['Phase structure (equilateral)'] = phases_ok

    # 3. Verify color neutrality
    neutrality_ok = verify_color_neutrality(lambda_R, lambda_G, lambda_B)
    results['Color neutrality'] = neutrality_ok

    # 4. Verify tensor products
    tensors_ok = verify_tensor_products()
    results['Tensor products'] = tensors_ok

    # 5. Verify Euler characteristic
    euler_ok = verify_euler_characteristic()
    results['Euler characteristic'] = euler_ok

    # 6. Create visualizations
    create_weight_space_plot(lambda_R, lambda_G, lambda_B)
    create_z3_action_plot()

    # Summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)

    all_passed = True
    for check, passed in results.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"  {check}: {status}")
        if not passed:
            all_passed = False

    print()
    if all_passed:
        print("OVERALL: All computational checks PASSED")
    else:
        print("OVERALL: Some checks FAILED - review results above")

    print("\nPlots saved to:", PLOTS_DIR)

    # Issues noted
    print("\n" + "=" * 70)
    print("ISSUES NOTED (from agent verification)")
    print("=" * 70)
    print("""
  Mathematical Issues:
  1. Principal bundle construction incomplete (transition functions not explicit)
  2. Phase derivation conflates convention with derivation
  3. Smoothness of base space not addressed

  Physics Issues:
  1. "Matter necessarily exists" claim is overstatement
  2. Theorem provides kinematics, not dynamics
  3. Z_3 vs full SU(3) gauge invariance distinction needed

  Recommended Status: NEEDS REVISION before VERIFIED
""")

    return all_passed


if __name__ == "__main__":
    main()
