"""
Theorem 2.4.2: Topological Chirality from Stella Orientation
Verification Script

This script verifies the key mathematical calculations in Theorem 2.4.2:
1. Winding number calculation for color phase cycle R → G → B → R
2. SU(3) root structure and weight vector angles
3. Anomaly coefficient cancellation for Standard Model
4. Visualization of the topological winding

Author: Multi-agent verification system
Date: December 26, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Create plots directory if needed
PLOT_DIR = Path(__file__).parent / "plots"
PLOT_DIR.mkdir(exist_ok=True)


def verify_winding_number():
    """
    Verify the winding number calculation for the color phase cycle.

    The color phases are: φ_R = 0, φ_G = 2π/3, φ_B = 4π/3
    The cycle R → G → B → R should give winding number w = +1.
    """
    print("=" * 60)
    print("1. WINDING NUMBER VERIFICATION")
    print("=" * 60)

    # Color phase values (in radians)
    phi_R = 0
    phi_G = 2 * np.pi / 3
    phi_B = 4 * np.pi / 3

    print(f"\nColor phases:")
    print(f"  φ_R = {phi_R:.4f} rad = {np.degrees(phi_R):.1f}°")
    print(f"  φ_G = {phi_G:.4f} rad = {np.degrees(phi_G):.1f}°")
    print(f"  φ_B = {phi_B:.4f} rad = {np.degrees(phi_B):.1f}°")

    # Phase differences along R → G → B → R cycle
    delta_RG = phi_G - phi_R
    delta_GB = phi_B - phi_G
    # For the return B → R, we need to account for the 2π winding
    delta_BR = (phi_R + 2*np.pi) - phi_B

    print(f"\nPhase changes along cycle:")
    print(f"  Δφ(R→G) = {delta_RG:.4f} rad = {np.degrees(delta_RG):.1f}° = 2π/3")
    print(f"  Δφ(G→B) = {delta_GB:.4f} rad = {np.degrees(delta_GB):.1f}° = 2π/3")
    print(f"  Δφ(B→R) = {delta_BR:.4f} rad = {np.degrees(delta_BR):.1f}° = 2π/3")

    # Total phase change
    total_phase = delta_RG + delta_GB + delta_BR

    print(f"\nTotal phase change:")
    print(f"  ∮ dφ = {total_phase:.4f} rad = {np.degrees(total_phase):.1f}° = 2π")

    # Winding number
    w = total_phase / (2 * np.pi)

    print(f"\nWinding number:")
    print(f"  w = (1/2π) ∮ dφ = {w:.4f}")

    # Verification
    expected_w = 1.0
    tolerance = 1e-10
    verified = abs(w - expected_w) < tolerance

    print(f"\n✅ VERIFIED: w = +1" if verified else f"\n❌ FAILED: w = {w}")

    return verified, w


def verify_su3_weight_structure():
    """
    Verify that SU(3) weight vectors give 2π/3 = 120° separation.

    The fundamental representation weights in Cartan-Weyl basis:
    - μ_R = (1/2, 1/(2√3))
    - μ_G = (-1/2, 1/(2√3))
    - μ_B = (0, -1/√3)
    """
    print("\n" + "=" * 60)
    print("2. SU(3) WEIGHT STRUCTURE VERIFICATION")
    print("=" * 60)

    # Weight vectors for fundamental representation
    mu_R = np.array([1/2, 1/(2*np.sqrt(3))])
    mu_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    mu_B = np.array([0, -1/np.sqrt(3)])

    print(f"\nWeight vectors:")
    print(f"  μ_R = ({mu_R[0]:.4f}, {mu_R[1]:.4f})")
    print(f"  μ_G = ({mu_G[0]:.4f}, {mu_G[1]:.4f})")
    print(f"  μ_B = ({mu_B[0]:.4f}, {mu_B[1]:.4f})")

    # Verify tracelessness (weights sum to zero)
    weight_sum = mu_R + mu_G + mu_B
    traceless = np.allclose(weight_sum, [0, 0])
    print(f"\nTracelessness check (μ_R + μ_G + μ_B = 0):")
    print(f"  Sum = ({weight_sum[0]:.2e}, {weight_sum[1]:.2e})")
    print(f"  ✅ VERIFIED" if traceless else "  ❌ FAILED")

    # Compute norms
    norm_R = np.linalg.norm(mu_R)
    norm_G = np.linalg.norm(mu_G)
    norm_B = np.linalg.norm(mu_B)

    print(f"\nWeight norms:")
    print(f"  |μ_R| = {norm_R:.4f} = 1/√3")
    print(f"  |μ_G| = {norm_G:.4f} = 1/√3")
    print(f"  |μ_B| = {norm_B:.4f} = 1/√3")

    # Compute angles between weights
    cos_RG = np.dot(mu_R, mu_G) / (norm_R * norm_G)
    cos_GB = np.dot(mu_G, mu_B) / (norm_G * norm_B)
    cos_BR = np.dot(mu_B, mu_R) / (norm_B * norm_R)

    angle_RG = np.arccos(cos_RG)
    angle_GB = np.arccos(cos_GB)
    angle_BR = np.arccos(cos_BR)

    print(f"\nAngles between weights:")
    print(f"  θ(R,G) = {np.degrees(angle_RG):.1f}° (expected: 120°)")
    print(f"  θ(G,B) = {np.degrees(angle_GB):.1f}° (expected: 120°)")
    print(f"  θ(B,R) = {np.degrees(angle_BR):.1f}° (expected: 120°)")

    # Verification
    expected_angle = 2 * np.pi / 3  # 120 degrees
    tolerance = 1e-10
    verified = (abs(angle_RG - expected_angle) < tolerance and
                abs(angle_GB - expected_angle) < tolerance and
                abs(angle_BR - expected_angle) < tolerance)

    print(f"\n✅ VERIFIED: All angles = 2π/3 = 120°" if verified
          else "\n❌ FAILED: Angles do not match")

    return verified, (mu_R, mu_G, mu_B)


def verify_anomaly_cancellation():
    """
    Verify Standard Model anomaly cancellation for one generation.

    Fermion content (left-handed Weyl spinors):
    - Q_L: (3, 2)_{1/6} - 6 states
    - u_R^c → ū_L: (3̄, 1)_{-2/3} - 3 states
    - d_R^c → d̄_L: (3̄, 1)_{1/3} - 3 states
    - L_L: (1, 2)_{-1/2} - 2 states
    - e_R^c → ē_L: (1, 1)_{1} - 1 state

    Note: Right-handed fermions contribute with opposite sign hypercharge
    when treated as left-handed antifermions.
    """
    print("\n" + "=" * 60)
    print("3. ANOMALY CANCELLATION VERIFICATION")
    print("=" * 60)

    # Hypercharges and multiplicities for one SM generation
    # Format: (hypercharge Y, color multiplicity, weak multiplicity, chirality_sign)
    # chirality_sign = +1 for L, -1 for R (treated as ψ̄_L)
    fermions = {
        'Q_L': {'Y': 1/6, 'N_c': 3, 'N_w': 2, 'sign': +1},
        'u_R': {'Y': 2/3, 'N_c': 3, 'N_w': 1, 'sign': -1},
        'd_R': {'Y': -1/3, 'N_c': 3, 'N_w': 1, 'sign': -1},
        'L_L': {'Y': -1/2, 'N_c': 1, 'N_w': 2, 'sign': +1},
        'e_R': {'Y': -1, 'N_c': 1, 'N_w': 1, 'sign': -1},
    }

    print("\nFermion content (one generation):")
    print("-" * 55)
    print(f"{'Fermion':<8} {'Y':>8} {'N_c':>5} {'N_w':>5} {'Chirality':>10}")
    print("-" * 55)

    for name, f in fermions.items():
        chir = 'L' if f['sign'] > 0 else 'R'
        print(f"{name:<8} {f['Y']:>8.4f} {f['N_c']:>5} {f['N_w']:>5} {chir:>10}")

    # Calculate [U(1)_Y]^3 anomaly
    # A = Σ (sign) × N_c × N_w × Y^3
    A_Y3 = sum(f['sign'] * f['N_c'] * f['N_w'] * f['Y']**3
               for f in fermions.values())

    print(f"\n[U(1)_Y]³ anomaly:")
    print(f"  A = Σ (±1) × N_c × N_w × Y³")
    for name, f in fermions.items():
        contrib = f['sign'] * f['N_c'] * f['N_w'] * f['Y']**3
        sign = '+' if f['sign'] > 0 else '-'
        print(f"    {sign} {f['N_c']} × {f['N_w']} × ({f['Y']:.4f})³ = {contrib:+.6f}")
    print(f"  Total: A_Y³ = {A_Y3:.6f}")

    # Calculate [grav]² U(1)_Y anomaly (mixed gravitational)
    # A = Σ (sign) × N_c × N_w × Y
    A_grav = sum(f['sign'] * f['N_c'] * f['N_w'] * f['Y']
                 for f in fermions.values())

    print(f"\n[grav]² U(1)_Y anomaly:")
    print(f"  A = Σ (±1) × N_c × N_w × Y")
    for name, f in fermions.items():
        contrib = f['sign'] * f['N_c'] * f['N_w'] * f['Y']
        sign = '+' if f['sign'] > 0 else '-'
        print(f"    {sign} {f['N_c']} × {f['N_w']} × ({f['Y']:.4f}) = {contrib:+.4f}")
    print(f"  Total: A_grav = {A_grav:.6f}")

    # Calculate [SU(3)_c]² U(1)_Y anomaly
    # A = Σ (sign) × T(R_c) × N_w × Y where T(fund) = 1/2
    A_SU3 = sum(f['sign'] * (f['N_c']/2 if f['N_c'] == 3 else 0) * f['N_w'] * f['Y']
                for f in fermions.values())

    print(f"\n[SU(3)_c]² U(1)_Y anomaly:")
    print(f"  A = Σ (±1) × T(R_c) × N_w × Y")
    print(f"  Total: A_SU3 = {A_SU3:.6f}")

    # Verification
    tolerance = 1e-10
    Y3_verified = abs(A_Y3) < tolerance
    grav_verified = abs(A_grav) < tolerance
    SU3_verified = abs(A_SU3) < tolerance

    print(f"\nVerification:")
    print(f"  [U(1)_Y]³ = 0:     {'✅ VERIFIED' if Y3_verified else '❌ FAILED'}")
    print(f"  [grav]² U(1) = 0:  {'✅ VERIFIED' if grav_verified else '❌ FAILED'}")
    print(f"  [SU(3)]² U(1) = 0: {'✅ VERIFIED' if SU3_verified else '❌ FAILED'}")

    all_verified = Y3_verified and grav_verified and SU3_verified
    return all_verified, {'Y3': A_Y3, 'grav': A_grav, 'SU3': A_SU3}


def create_winding_visualization():
    """
    Create a visualization of the color phase winding on the stella octangula.
    """
    print("\n" + "=" * 60)
    print("4. CREATING VISUALIZATIONS")
    print("=" * 60)

    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Left plot: Color phase cycle in complex plane
    ax1 = axes[0]
    phases = [0, 2*np.pi/3, 4*np.pi/3, 2*np.pi]
    colors_list = ['red', 'green', 'blue', 'red']
    labels = ['R (φ=0)', 'G (φ=2π/3)', 'B (φ=4π/3)', 'R (φ=2π)']

    # Draw unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3)

    # Plot phase points
    for i, (phi, col, lab) in enumerate(zip(phases, colors_list, labels)):
        x, y = np.cos(phi), np.sin(phi)
        ax1.scatter(x, y, c=col, s=200, zorder=5, edgecolors='black', linewidth=2)
        offset = 0.15
        ax1.annotate(lab, (x + offset*np.cos(phi), y + offset*np.sin(phi)),
                    fontsize=10, ha='center')

    # Draw arrows showing the cycle
    for i in range(3):
        phi1, phi2 = phases[i], phases[i+1]
        # Parametric arc
        t = np.linspace(phi1, phi2, 20)
        ax1.plot(np.cos(t), np.sin(t), color=colors_list[i], linewidth=2.5)
        # Add arrowhead at midpoint
        mid_phi = (phi1 + phi2) / 2
        ax1.annotate('', xy=(np.cos(mid_phi + 0.1), np.sin(mid_phi + 0.1)),
                    xytext=(np.cos(mid_phi - 0.1), np.sin(mid_phi - 0.1)),
                    arrowprops=dict(arrowstyle='->', color=colors_list[i], lw=2))

    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.axhline(y=0, color='k', linewidth=0.5)
    ax1.axvline(x=0, color='k', linewidth=0.5)
    ax1.set_xlabel('Re(e^{iφ})')
    ax1.set_ylabel('Im(e^{iφ})')
    ax1.set_title('Color Phase Cycle: R → G → B → R\nWinding number w = +1')
    ax1.grid(True, alpha=0.3)

    # Right plot: SU(3) weight diagram
    ax2 = axes[1]

    # Weight vectors
    mu_R = np.array([1/2, 1/(2*np.sqrt(3))])
    mu_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    mu_B = np.array([0, -1/np.sqrt(3)])

    # Plot weights
    weights = [mu_R, mu_G, mu_B]
    colors = ['red', 'green', 'blue']
    labels = ['R (μ_R)', 'G (μ_G)', 'B (μ_B)']

    for w, c, l in zip(weights, colors, labels):
        ax2.scatter(w[0], w[1], c=c, s=200, zorder=5, edgecolors='black', linewidth=2)
        ax2.annotate(l, (w[0], w[1] + 0.1), fontsize=10, ha='center')

    # Draw triangle connecting weights
    triangle = plt.Polygon([mu_R, mu_G, mu_B], fill=False, edgecolor='black',
                          linewidth=1.5, linestyle='--')
    ax2.add_patch(triangle)

    # Draw arrows from origin to weights
    for w, c in zip(weights, colors):
        ax2.annotate('', xy=w, xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=c, lw=2))

    # Add angle annotation
    arc = plt.matplotlib.patches.Arc((0, 0), 0.4, 0.4, angle=0,
                                      theta1=np.degrees(np.arctan2(mu_G[1], mu_G[0])),
                                      theta2=np.degrees(np.arctan2(mu_R[1], mu_R[0])),
                                      color='gray')
    ax2.add_patch(arc)
    ax2.annotate('120°', (0.1, 0.25), fontsize=9, color='gray')

    ax2.set_xlim(-0.8, 0.8)
    ax2.set_ylim(-0.8, 0.6)
    ax2.set_aspect('equal')
    ax2.axhline(y=0, color='k', linewidth=0.5)
    ax2.axvline(x=0, color='k', linewidth=0.5)
    ax2.set_xlabel('T₃ eigenvalue')
    ax2.set_ylabel('T₈ eigenvalue (× √3)')
    ax2.set_title('SU(3) Fundamental Weights\nAngular separation: 2π/3 = 120°')
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()

    # Save figure
    output_path = PLOT_DIR / "theorem_2_4_2_winding_and_weights.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"\nSaved visualization to: {output_path}")
    plt.close()

    return True


def main():
    """Run all verifications."""
    print("\n" + "=" * 60)
    print("THEOREM 2.4.2 VERIFICATION SCRIPT")
    print("Topological Chirality from Stella Orientation")
    print("=" * 60)

    results = {}

    # Run verifications
    results['winding'], _ = verify_winding_number()
    results['weights'], _ = verify_su3_weight_structure()
    results['anomalies'], _ = verify_anomaly_cancellation()
    results['visualization'] = create_winding_visualization()

    # Summary
    print("\n" + "=" * 60)
    print("VERIFICATION SUMMARY")
    print("=" * 60)

    all_passed = all(results.values())

    for test, passed in results.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"  {test.capitalize():20s}: {status}")

    print("\n" + "-" * 60)
    if all_passed:
        print("OVERALL: ✅ ALL VERIFICATIONS PASSED")
    else:
        failed = [k for k, v in results.items() if not v]
        print(f"OVERALL: ❌ FAILED: {', '.join(failed)}")
    print("-" * 60)

    return all_passed


if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
