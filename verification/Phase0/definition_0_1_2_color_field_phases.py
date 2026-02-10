#!/usr/bin/env python3
"""
Numerical Verification: Definition 0.1.2 - Three Color Fields with Relative Phases

This script verifies the mathematical claims in Definition 0.1.2 regarding
the phase structure of the three color fields χ_R, χ_G, χ_B.

Tests verify:
1. Cube roots of unity sum to zero
2. Product of phase factors equals 1
3. Phases are equally spaced (120° apart)
4. Weight vector geometry (equal magnitudes, 120° angles)
5. Color neutrality with equal amplitudes
6. Z3 cyclic symmetry
7. Anti-color phase relations
8. Phase factors form equilateral triangle in complex plane
9. Total field cancellation at center
10. Explicit complex values match formulas

Author: Verification Suite
Date: December 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from matplotlib.colors import to_rgba
import sys

# Tolerance for numerical comparisons
TOL = 1e-10

# Fundamental phase values
PHI_R = 0
PHI_G = 2 * np.pi / 3
PHI_B = 4 * np.pi / 3

# Cube root of unity
OMEGA = np.exp(2j * np.pi / 3)


def get_phase_factors():
    """Return the three phase factors as complex numbers."""
    return {
        'R': np.exp(1j * PHI_R),  # = 1
        'G': np.exp(1j * PHI_G),  # = ω
        'B': np.exp(1j * PHI_B),  # = ω²
    }


def test_cube_roots_sum_to_zero():
    """Test 1: 1 + ω + ω² = 0 (cube roots of unity sum to zero)."""
    omega = OMEGA
    total = 1 + omega + omega**2

    assert abs(total) < TOL, f"1 + ω + ω² = {total}, expected 0"

    # Also test via phase factors
    phases = get_phase_factors()
    sum_phases = phases['R'] + phases['G'] + phases['B']

    assert abs(sum_phases) < TOL, f"Sum of phase factors = {sum_phases}, expected 0"

    print("✓ Test 1 PASSED: 1 + ω + ω² = 0 (cube roots of unity sum to zero)")
    return True


def test_product_equals_one():
    """Test 2: e^{iφ_R} · e^{iφ_G} · e^{iφ_B} = 1."""
    phases = get_phase_factors()
    product = phases['R'] * phases['G'] * phases['B']

    # Also compute via sum of angles
    total_phase = PHI_R + PHI_G + PHI_B  # = 0 + 2π/3 + 4π/3 = 2π
    expected = np.exp(1j * total_phase)

    assert abs(product - 1) < TOL, f"Product of phases = {product}, expected 1"
    assert abs(expected - 1) < TOL, f"e^{i(φ_R+φ_G+φ_B)} = {expected}, expected 1"

    print("✓ Test 2 PASSED: Product of phase factors = 1")
    return True


def test_equal_spacing():
    """Test 3: Phases are equally spaced (Δφ = 2π/3 = 120°)."""
    diff_GR = PHI_G - PHI_R
    diff_BG = PHI_B - PHI_G
    diff_RB = (PHI_R - PHI_B) % (2 * np.pi)

    expected_diff = 2 * np.pi / 3

    assert abs(diff_GR - expected_diff) < TOL, f"φ_G - φ_R = {diff_GR}, expected {expected_diff}"
    assert abs(diff_BG - expected_diff) < TOL, f"φ_B - φ_G = {diff_BG}, expected {expected_diff}"
    assert abs(diff_RB - expected_diff) < TOL, f"φ_R - φ_B (mod 2π) = {diff_RB}, expected {expected_diff}"

    print(f"✓ Test 3 PASSED: All phase differences = 2π/3 = {np.degrees(expected_diff):.1f}°")
    return True


def test_weight_vector_geometry():
    """Test 4: SU(3) weight vectors have equal magnitudes and 120° angles."""
    # Weight vectors from Section 2.2 of Definition 0.1.2
    # Using T_3, T_8 basis with Tr(T_a T_b) = 1/2 δ_ab normalization
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    # Check magnitudes
    mag_R = np.linalg.norm(w_R)
    mag_G = np.linalg.norm(w_G)
    mag_B = np.linalg.norm(w_B)

    expected_mag = 1 / np.sqrt(3)

    assert abs(mag_R - expected_mag) < TOL, f"|w_R| = {mag_R}, expected {expected_mag}"
    assert abs(mag_G - expected_mag) < TOL, f"|w_G| = {mag_G}, expected {expected_mag}"
    assert abs(mag_B - expected_mag) < TOL, f"|w_B| = {mag_B}, expected {expected_mag}"

    # Check angles between pairs
    cos_RG = np.dot(w_R, w_G) / (mag_R * mag_G)
    cos_GB = np.dot(w_G, w_B) / (mag_G * mag_B)
    cos_BR = np.dot(w_B, w_R) / (mag_B * mag_R)

    expected_cos = -1/2  # cos(120°) = -1/2

    assert abs(cos_RG - expected_cos) < TOL, f"cos(θ_RG) = {cos_RG}, expected {expected_cos}"
    assert abs(cos_GB - expected_cos) < TOL, f"cos(θ_GB) = {cos_GB}, expected {expected_cos}"
    assert abs(cos_BR - expected_cos) < TOL, f"cos(θ_BR) = {cos_BR}, expected {expected_cos}"

    print(f"✓ Test 4 PASSED: Weight vectors have |w| = 1/√3 and angles of 120°")
    return True


def test_color_neutrality_equal_amplitudes():
    """Test 5: With equal amplitudes, total field vanishes."""
    phases = get_phase_factors()

    # Equal amplitudes a_R = a_G = a_B = a
    a = 1.0  # arbitrary amplitude

    total = a * (phases['R'] + phases['G'] + phases['B'])

    assert abs(total) < TOL, f"Total field with equal amplitudes = {total}, expected 0"

    # Test with different common amplitude
    a = 3.7
    total = a * (phases['R'] + phases['G'] + phases['B'])

    assert abs(total) < TOL, f"Total field with a={a} = {total}, expected 0"

    print("✓ Test 5 PASSED: Color neutrality: a(1 + ω + ω²) = 0 for any amplitude a")
    return True


def test_z3_cyclic_symmetry():
    """Test 6: Z3 cyclic symmetry under R → G → B → R permutation."""
    phases = get_phase_factors()

    # The cyclic permutation R → G → B → R is equivalent to multiplying by ω
    # i.e., σ(e^{iφ_R}) = e^{iφ_G}, σ(e^{iφ_G}) = e^{iφ_B}, σ(e^{iφ_B}) = e^{iφ_R}

    # This is the same as: σ(z) = ω * z followed by relabeling
    # Or equivalently: the set {1, ω, ω²} is closed under multiplication by ω

    omega = OMEGA

    # After multiplying by ω:
    # 1 → ω → ω² → ω³ = 1
    assert abs(1 * omega - omega) < TOL
    assert abs(omega * omega - omega**2) < TOL
    assert abs(omega**2 * omega - 1) < TOL

    # The sum is invariant under this transformation
    original_sum = phases['R'] + phases['G'] + phases['B']
    transformed_sum = (phases['R'] * omega) + (phases['G'] * omega) + (phases['B'] * omega)

    assert abs(transformed_sum - omega * original_sum) < TOL

    print("✓ Test 6 PASSED: Z₃ cyclic symmetry preserved (phases form closed orbit under ω multiplication)")
    return True


def test_anticolor_phase_relations():
    """Test 7: Anti-color phases satisfy e^{iφ_c̄} = e^{-iφ_c}."""
    phases = get_phase_factors()

    # Anti-color phases are complex conjugates (negatives in phase)
    phi_Rbar = -PHI_R  # = 0
    phi_Gbar = -PHI_G  # = -2π/3 ≡ 4π/3
    phi_Bbar = -PHI_B  # = -4π/3 ≡ 2π/3

    e_Rbar = np.exp(1j * phi_Rbar)
    e_Gbar = np.exp(1j * phi_Gbar)
    e_Bbar = np.exp(1j * phi_Bbar)

    # These should be conjugates of the color phases
    assert abs(e_Rbar - np.conj(phases['R'])) < TOL, f"e^{{iφ_R̄}} ≠ conj(e^{{iφ_R}})"
    assert abs(e_Gbar - np.conj(phases['G'])) < TOL, f"e^{{iφ_Ḡ}} ≠ conj(e^{{iφ_G}})"
    assert abs(e_Bbar - np.conj(phases['B'])) < TOL, f"e^{{iφ_B̄}} ≠ conj(e^{{iφ_B}})"

    # Note: φ_R̄ = 0 same as φ_R, but φ_Ḡ = 4π/3 = φ_B and φ_B̄ = 2π/3 = φ_G
    assert abs(e_Gbar - phases['B']) < TOL, "e^{iφ_Ḡ} = e^{iφ_B}"
    assert abs(e_Bbar - phases['G']) < TOL, "e^{iφ_B̄} = e^{iφ_G}"

    print("✓ Test 7 PASSED: Anti-color phases are complex conjugates (e^{iφ_c̄} = e^{-iφ_c})")
    return True


def test_equilateral_triangle_in_complex_plane():
    """Test 8: Phase factors form equilateral triangle centered at origin."""
    phases = get_phase_factors()

    # Get complex coordinates
    z_R = phases['R']
    z_G = phases['G']
    z_B = phases['B']

    # Check all lie on unit circle
    assert abs(abs(z_R) - 1) < TOL, f"|z_R| = {abs(z_R)}"
    assert abs(abs(z_G) - 1) < TOL, f"|z_G| = {abs(z_G)}"
    assert abs(abs(z_B) - 1) < TOL, f"|z_B| = {abs(z_B)}"

    # Check equal distances (equilateral triangle)
    d_RG = abs(z_R - z_G)
    d_GB = abs(z_G - z_B)
    d_BR = abs(z_B - z_R)

    assert abs(d_RG - d_GB) < TOL, f"d_RG = {d_RG}, d_GB = {d_GB}"
    assert abs(d_GB - d_BR) < TOL, f"d_GB = {d_GB}, d_BR = {d_BR}"

    # Expected side length for equilateral triangle inscribed in unit circle
    expected_side = np.sqrt(3)

    assert abs(d_RG - expected_side) < TOL, f"Side length = {d_RG}, expected √3 = {expected_side}"

    # Check centroid at origin
    centroid = (z_R + z_G + z_B) / 3

    assert abs(centroid) < TOL, f"Centroid = {centroid}, expected 0"

    print(f"✓ Test 8 PASSED: Equilateral triangle in complex plane (side = √3 ≈ {expected_side:.4f})")
    return True


def test_total_field_at_center():
    """Test 9: Total field cancellation when all colors have equal amplitude."""
    # When at the center of the stella octangula, all pressure functions are equal
    # So a_R = a_G = a_B = a_center

    # The pressure function at center (from Definition 0.1.3)
    epsilon = 0.5  # regularization parameter
    # At center x=0, all vertices are at distance 1/√3 from origin
    # Actually vertices are on unit sphere, so distance from origin to each vertex = 1

    # For equal pressures, P_R(0) = P_G(0) = P_B(0) = 1/(1 + ε²)
    P_center = 1 / (1 + epsilon**2)

    phases = get_phase_factors()

    # Total field at center
    chi_total = P_center * (phases['R'] + phases['G'] + phases['B'])

    assert abs(chi_total) < TOL, f"Total field at center = {chi_total}, expected 0"

    print("✓ Test 9 PASSED: Total field vanishes at center (equal pressures)")
    return True


def test_explicit_complex_values():
    """Test 10: Verify explicit complex values of phase factors."""
    omega = OMEGA

    # Explicit formulas from Section 3.1
    omega_real_expected = -1/2
    omega_imag_expected = np.sqrt(3)/2

    assert abs(omega.real - omega_real_expected) < TOL, \
        f"Re(ω) = {omega.real}, expected {omega_real_expected}"
    assert abs(omega.imag - omega_imag_expected) < TOL, \
        f"Im(ω) = {omega.imag}, expected {omega_imag_expected}"

    # ω² = conjugate of ω
    omega2 = omega**2
    omega2_expected = np.conj(omega)

    assert abs(omega2 - omega2_expected) < TOL, f"ω² = {omega2}, expected conj(ω) = {omega2_expected}"

    # Verify ω³ = 1
    omega3 = omega**3

    assert abs(omega3 - 1) < TOL, f"ω³ = {omega3}, expected 1"

    # Verify specific values
    phases = get_phase_factors()

    assert abs(phases['R'] - 1) < TOL, f"e^{{iφ_R}} = {phases['R']}, expected 1"
    assert abs(phases['G'] - omega) < TOL, f"e^{{iφ_G}} = {phases['G']}, expected ω"
    assert abs(phases['B'] - omega**2) < TOL, f"e^{{iφ_B}} = {phases['B']}, expected ω²"

    print("✓ Test 10 PASSED: Explicit complex values verified")
    print(f"    ω = -1/2 + i√3/2 = {omega:.6f}")
    print(f"    ω² = -1/2 - i√3/2 = {omega**2:.6f}")
    return True


def create_visualization():
    """Create visualization of color field phases."""
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    # Plot 1: Phase factors in complex plane
    ax1 = axes[0]
    phases = get_phase_factors()

    # Draw unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1)

    # Draw phase vectors
    colors = {'R': 'red', 'G': 'green', 'B': 'blue'}
    for name, z in phases.items():
        ax1.arrow(0, 0, z.real*0.95, z.imag*0.95, head_width=0.08, head_length=0.05,
                  fc=colors[name], ec=colors[name], linewidth=2)
        ax1.plot(z.real, z.imag, 'o', color=colors[name], markersize=12)
        angle = np.angle(z)
        ax1.annotate(f'{name}\n({np.degrees(angle):.0f}°)',
                     (z.real*1.15, z.imag*1.15), ha='center', va='center', fontsize=11)

    # Draw triangle connecting phase points
    pts = [phases['R'], phases['G'], phases['B'], phases['R']]
    ax1.plot([z.real for z in pts], [z.imag for z in pts], 'k-', linewidth=1.5, alpha=0.5)

    ax1.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
    ax1.axvline(x=0, color='gray', linestyle='-', alpha=0.3)
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.set_xlabel('Real', fontsize=11)
    ax1.set_ylabel('Imaginary', fontsize=11)
    ax1.set_title('Phase Factors in Complex Plane\n(Cube Roots of Unity)', fontsize=12)
    ax1.grid(True, alpha=0.3)

    # Plot 2: SU(3) Weight diagram
    ax2 = axes[1]

    # Weight vectors
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    # Draw vectors
    for w, name, color in [(w_R, 'R', 'red'), (w_G, 'G', 'green'), (w_B, 'B', 'blue')]:
        ax2.arrow(0, 0, w[0]*0.9, w[1]*0.9, head_width=0.04, head_length=0.03,
                  fc=color, ec=color, linewidth=2)
        ax2.plot(w[0], w[1], 'o', color=color, markersize=12)
        ax2.annotate(name, (w[0]*1.15, w[1]*1.15), ha='center', va='center', fontsize=12, fontweight='bold')

    # Draw triangle
    weights = [w_R, w_G, w_B, w_R]
    ax2.plot([w[0] for w in weights], [w[1] for w in weights], 'k-', linewidth=1.5, alpha=0.5)
    ax2.fill([w_R[0], w_G[0], w_B[0]], [w_R[1], w_G[1], w_B[1]], alpha=0.1, color='purple')

    ax2.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
    ax2.axvline(x=0, color='gray', linestyle='-', alpha=0.3)
    ax2.set_xlim(-0.8, 0.8)
    ax2.set_ylim(-0.8, 0.8)
    ax2.set_aspect('equal')
    ax2.set_xlabel('T₃ (Isospin)', fontsize=11)
    ax2.set_ylabel('T₈ (Related to Hypercharge)', fontsize=11)
    ax2.set_title('SU(3) Weight Diagram\n(Fundamental Representation)', fontsize=12)
    ax2.grid(True, alpha=0.3)

    # Plot 3: Color neutrality demonstration
    ax3 = axes[2]

    # Show how colors sum to zero
    # Start at origin, add R, then G, then B
    path_re = [0, 1, 1 + phases['G'].real, 1 + phases['G'].real + phases['B'].real]
    path_im = [0, 0, phases['G'].imag, phases['G'].imag + phases['B'].imag]

    # Draw arrows for each step
    ax3.arrow(0, 0, 1, 0, head_width=0.08, head_length=0.05,
              fc='red', ec='red', linewidth=3, alpha=0.7, label='R (= 1)')
    ax3.arrow(1, 0, phases['G'].real, phases['G'].imag, head_width=0.08, head_length=0.05,
              fc='green', ec='green', linewidth=3, alpha=0.7, label='G (= ω)')
    ax3.arrow(1 + phases['G'].real, phases['G'].imag,
              phases['B'].real, phases['B'].imag, head_width=0.08, head_length=0.05,
              fc='blue', ec='blue', linewidth=3, alpha=0.7, label='B (= ω²)')

    # Mark origin (start and end)
    ax3.plot(0, 0, 'ko', markersize=15, zorder=5)
    ax3.annotate('Start\n= End', (0.1, -0.2), fontsize=10, ha='left')

    # Draw unit circle for reference
    ax3.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.2, linewidth=1)

    ax3.set_xlim(-1.5, 1.5)
    ax3.set_ylim(-1.5, 1.5)
    ax3.set_aspect('equal')
    ax3.set_xlabel('Real', fontsize=11)
    ax3.set_ylabel('Imaginary', fontsize=11)
    ax3.set_title('Color Neutrality\n1 + ω + ω² = 0', fontsize=12)
    ax3.legend(loc='upper right', fontsize=10)
    ax3.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('verification/plots/definition_0_1_2_color_field_phases.png', dpi=150, bbox_inches='tight')
    plt.close()

    print("\n📊 Visualization saved: verification/plots/definition_0_1_2_color_field_phases.png")


def run_all_tests():
    """Run all verification tests."""
    print("=" * 70)
    print("DEFINITION 0.1.2 VERIFICATION: Three Color Fields with Relative Phases")
    print("=" * 70)
    print()

    tests = [
        ("Cube roots sum to zero", test_cube_roots_sum_to_zero),
        ("Product equals one", test_product_equals_one),
        ("Equal phase spacing", test_equal_spacing),
        ("Weight vector geometry", test_weight_vector_geometry),
        ("Color neutrality", test_color_neutrality_equal_amplitudes),
        ("Z3 cyclic symmetry", test_z3_cyclic_symmetry),
        ("Anti-color phase relations", test_anticolor_phase_relations),
        ("Equilateral triangle", test_equilateral_triangle_in_complex_plane),
        ("Total field at center", test_total_field_at_center),
        ("Explicit complex values", test_explicit_complex_values),
    ]

    passed = 0
    failed = 0

    for name, test_func in tests:
        try:
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"✗ Test '{name}' FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ Test '{name}' ERROR: {e}")
            failed += 1

    print()
    print("=" * 70)
    print(f"RESULTS: {passed}/{len(tests)} tests passed")
    print("=" * 70)

    # Create visualization
    import os
    os.makedirs('verification/plots', exist_ok=True)
    create_visualization()

    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
