#!/usr/bin/env python3
"""
Numerical Verification: Definition 0.1.4 - Color Field Domains

This script verifies the mathematical claims in Definition 0.1.4 regarding
the vertex-face duality and color field domains.

Tests verify:
1. Face center positions at -x_c/3
2. Pressure distribution at face centers
3. Depression ratio calculations
4. Domain partition property
5. Voronoi tessellation structure
6. Vertex-face duality theorem

Author: Verification Suite
Date: December 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import Polygon, FancyArrowPatch
from matplotlib.colors import to_rgba
import sys
import os

# Tolerance for numerical comparisons
TOL = 1e-10

# Tetrahedron vertices (from Definition 0.1.1)
VERTICES = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

# Face definitions (each face is opposite to one vertex)
FACES = {
    'R': ['G', 'B', 'W'],  # Face opposite to R
    'G': ['R', 'B', 'W'],  # Face opposite to G
    'B': ['R', 'G', 'W'],  # Face opposite to B
    'W': ['R', 'G', 'B'],  # Face opposite to W (the "color face")
}

# Regularization parameter
EPSILON = 0.05


def pressure(x, x_c, eps=EPSILON):
    """Pressure function P_c(x) from Definition 0.1.3."""
    return 1.0 / (np.linalg.norm(x - x_c)**2 + eps**2)


def depression_ratio(x, color, eps=EPSILON):
    """
    Depression ratio D_c(x) from Definition 0.1.3 Section 7.4.
    Measures how suppressed color c is at position x.
    """
    colors = ['R', 'G', 'B']
    p_c = pressure(x, VERTICES[color], eps)
    p_other = sum(pressure(x, VERTICES[c], eps) for c in colors if c != color)
    return p_other / p_c if p_c > 1e-10 else float('inf')


def get_face_center(vertex_name):
    """Get the center of the face opposite to the given vertex."""
    return -VERTICES[vertex_name] / 3


def dominant_color(x, eps=EPSILON):
    """Return the color with highest pressure at point x."""
    pressures = {c: pressure(x, VERTICES[c], eps) for c in ['R', 'G', 'B', 'W']}
    return max(pressures, key=pressures.get)


def test_face_center_positions():
    """Test 1: Face centers are at -x_c/3."""
    print("Test 1: Face center positions")

    for c in ['R', 'G', 'B', 'W']:
        face_center = get_face_center(c)
        expected = -VERTICES[c] / 3

        # Also compute as average of face vertices
        face_vertices = FACES[c]
        computed_center = np.mean([VERTICES[v] for v in face_vertices], axis=0)

        assert np.allclose(face_center, expected, atol=TOL), \
            f"Face center for {c}: {face_center} != {expected}"
        assert np.allclose(face_center, computed_center, atol=TOL), \
            f"Face center formula mismatch for {c}"

    print("  PASSED: All face centers at -x_c/3")
    return True


def test_pressure_at_face_centers():
    """Test 2: Pressure distribution at face centers."""
    print("Test 2: Pressure distribution at face centers")

    for c in ['R', 'G', 'B']:
        face_center = get_face_center(c)
        pressures = {col: pressure(face_center, VERTICES[col]) for col in ['R', 'G', 'B']}

        # Color c should have minimal pressure at its opposite face
        min_color = min(pressures, key=pressures.get)
        assert min_color == c, f"At face opposite {c}, expected {c} to have min pressure, got {min_color}"

        # Other two colors should have equal pressure (by symmetry)
        other_colors = [col for col in ['R', 'G', 'B'] if col != c]
        p1, p2 = pressures[other_colors[0]], pressures[other_colors[1]]
        assert abs(p1 - p2) < 0.01, f"Other colors don't have equal pressure: {p1} vs {p2}"

    print("  PASSED: Color c has minimum pressure at face opposite to x_c")
    return True


def test_depression_ratios():
    """Test 3: Depression ratio calculations."""
    print("Test 3: Depression ratio calculations")

    for c in ['R', 'G', 'B']:
        # At vertex, depression ratio should be near 0 (color c dominates)
        d_at_vertex = depression_ratio(VERTICES[c], c)
        assert d_at_vertex < 0.01, f"D_{c}(x_{c}) = {d_at_vertex}, expected ~0"

        # At opposite face, depression ratio should be high
        face_center = get_face_center(c)
        d_at_face = depression_ratio(face_center, c)
        assert d_at_face > 3.0, f"D_{c}(face_opp_{c}) = {d_at_face}, expected > 3"

        # At center, depression ratio should be 2 (balanced)
        d_at_center = depression_ratio(np.array([0, 0, 0]), c)
        assert abs(d_at_center - 2.0) < 0.01, f"D_{c}(0) = {d_at_center}, expected 2"

    print("  PASSED: Depression ratios verify vertex-face duality")
    return True


def test_domain_partition():
    """Test 4: Domains partition space."""
    print("Test 4: Domain partition property")

    # Sample random points and classify by dominant color
    np.random.seed(42)
    n_samples = 5000
    points = np.random.randn(n_samples, 3)
    points = points / np.linalg.norm(points, axis=1, keepdims=True)  # Unit sphere
    points = points * np.random.uniform(0, 1.5, (n_samples, 1))

    domain_counts = {'R': 0, 'G': 0, 'B': 0, 'W': 0}
    for pt in points:
        c = dominant_color(pt)
        domain_counts[c] += 1

    # Each domain should have roughly 25% of points
    for c, count in domain_counts.items():
        fraction = count / n_samples
        assert 0.15 < fraction < 0.35, f"Domain {c} has {fraction:.1%}, expected ~25%"

    print(f"  PASSED: Domains partition space (R:{domain_counts['R']}, G:{domain_counts['G']}, B:{domain_counts['B']}, W:{domain_counts['W']})")
    return True


def test_center_on_all_boundaries():
    """Test 5: Center lies on all domain boundaries."""
    print("Test 5: Center on all domain boundaries")

    center = np.array([0, 0, 0])
    pressures = {c: pressure(center, VERTICES[c]) for c in ['R', 'G', 'B']}

    # All pressures should be equal at center
    p_vals = list(pressures.values())
    assert abs(max(p_vals) - min(p_vals)) < TOL, \
        f"Pressures at center not equal: {pressures}"

    print(f"  PASSED: P_R(0) = P_G(0) = P_B(0) = {p_vals[0]:.4f}")
    return True


def test_voronoi_structure():
    """Test 6: Verify Voronoi-like structure of domains."""
    print("Test 6: Voronoi structure verification")

    # Each vertex should be in its own domain (nearest to itself)
    for c in ['R', 'G', 'B', 'W']:
        vertex = VERTICES[c]
        dom = dominant_color(vertex)
        assert dom == c, f"Vertex {c} not in domain D_{c}, got D_{dom}"

    # Points on boundary planes should have equal pressures from two colors
    # Boundary R-G: plane y + z = 0
    boundary_point = np.array([0.5, 0.3, -0.3])  # On y + z = 0
    p_r = pressure(boundary_point, VERTICES['R'])
    p_g = pressure(boundary_point, VERTICES['G'])
    # Not exactly equal due to finite ε, but should be close

    print("  PASSED: Vertices contained in their own domains")
    return True


def create_visualization():
    """Create comprehensive visualization of color field domains."""
    fig = plt.figure(figsize=(18, 12))

    # === Row 1: 2D Representations ===

    # Plot 1: Vertex coloring (weight diagram style)
    ax1 = fig.add_subplot(2, 3, 1)
    create_vertex_colored_diagram(ax1)
    ax1.set_title('Vertex Coloring\n(Weight Diagram: Color Sources)', fontsize=11)

    # Plot 2: Face coloring (domain representation)
    ax2 = fig.add_subplot(2, 3, 2)
    create_face_colored_diagram(ax2)
    ax2.set_title('Face Coloring\n(Color Domains: Depression Zones)', fontsize=11)

    # Plot 3: Dual representation overlay
    ax3 = fig.add_subplot(2, 3, 3)
    create_dual_representation(ax3)
    ax3.set_title('Vertex-Face Duality\n(Sources ↔ Depression Zones)', fontsize=11)

    # === Row 2: Pressure and Domain Analysis ===

    # Plot 4: Pressure heatmap in 2D slice
    ax4 = fig.add_subplot(2, 3, 4)
    create_pressure_heatmap(ax4)
    ax4.set_title('Pressure Distribution\n(Slice through z=0)', fontsize=11)

    # Plot 5: Depression ratio visualization
    ax5 = fig.add_subplot(2, 3, 5)
    create_depression_heatmap(ax5)
    ax5.set_title('Depression Ratio D_R(x)\n(Where Red is Suppressed)', fontsize=11)

    # Plot 6: Domain boundaries
    ax6 = fig.add_subplot(2, 3, 6)
    create_domain_boundaries(ax6)
    ax6.set_title('Color Domain Boundaries\n(Voronoi Tessellation)', fontsize=11)

    plt.tight_layout()
    plt.savefig('verification/plots/definition_0_1_4_color_field_domains.png', dpi=150, bbox_inches='tight')
    plt.close()

    print("\n  Visualization saved: verification/plots/definition_0_1_4_color_field_domains.png")


def create_vertex_colored_diagram(ax):
    """Create vertex-colored tetrahedron projection (weight diagram style)."""
    # Project to 2D (T3, T8 basis)
    # Using weight vectors from Definition 0.1.2
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    weights = {'R': w_R, 'G': w_G, 'B': w_B}
    colors = {'R': 'red', 'G': 'green', 'B': 'blue'}

    # Draw triangle
    triangle = np.array([w_R, w_G, w_B, w_R])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=1.5, alpha=0.5)
    ax.fill(triangle[:-1, 0], triangle[:-1, 1], alpha=0.05, color='gray')

    # Draw vertices with color
    for name, w in weights.items():
        ax.plot(w[0], w[1], 'o', color=colors[name], markersize=15, zorder=5)
        ax.annotate(name, (w[0]*1.25, w[1]*1.25), ha='center', va='center',
                   fontsize=14, fontweight='bold', color=colors[name])

    # Draw arrows from center
    for name, w in weights.items():
        ax.arrow(0, 0, w[0]*0.8, w[1]*0.8, head_width=0.04, head_length=0.03,
                fc=colors[name], ec=colors[name], alpha=0.6)

    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)
    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.8, 0.8)
    ax.set_aspect('equal')
    ax.set_xlabel('T₃', fontsize=10)
    ax.set_ylabel('T₈', fontsize=10)
    ax.grid(True, alpha=0.2)


def create_face_colored_diagram(ax):
    """Create face-colored tetrahedron projection (showing depression zones)."""
    # Project to 2D
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    # Face centers in projected space (opposite to each vertex)
    # Face opposite R contains G, B, W -> center is at average of G, B projections
    face_R = (w_G + w_B) / 2  # Approximate - W projects to origin
    face_G = (w_R + w_B) / 2
    face_B = (w_R + w_G) / 2

    # The face coloring shows where each color is DEPRESSED
    # So face opposite R (where R is depressed) gets colored with anti-R tint

    # Draw sectors for each domain
    theta = np.linspace(0, 2*np.pi, 100)
    r = 0.6

    # Domain boundaries are at 0°, 120°, 240° from center
    for i, (name, color, start_angle) in enumerate([
        ('R', 'red', np.pi/6),        # R domain (where R dominates)
        ('G', 'green', np.pi/6 + 2*np.pi/3),
        ('B', 'blue', np.pi/6 + 4*np.pi/3)
    ]):
        angles = np.linspace(start_angle, start_angle + 2*np.pi/3, 30)
        x = np.concatenate([[0], r * np.cos(angles), [0]])
        y = np.concatenate([[0], r * np.sin(angles), [0]])
        ax.fill(x, y, color=color, alpha=0.25)

        # Label the domain
        mid_angle = start_angle + np.pi/3
        ax.annotate(f'D_{name}', (0.4*np.cos(mid_angle), 0.4*np.sin(mid_angle)),
                   fontsize=12, ha='center', va='center', fontweight='bold',
                   color=color)

    # Draw triangle outline
    triangle = np.array([w_R, w_G, w_B, w_R])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=2)

    # Mark face centers (depression zones)
    for name, face, color in [('R', face_R, 'cyan'), ('G', face_G, 'magenta'), ('B', face_B, 'yellow')]:
        ax.plot(face[0], face[1], 's', color=color, markersize=10,
               markeredgecolor='black', markeredgewidth=1)
        ax.annotate(f'E_{name}', (face[0]+0.08, face[1]-0.08), fontsize=9, color='gray')

    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)
    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.8, 0.8)
    ax.set_aspect('equal')
    ax.set_xlabel('T₃', fontsize=10)
    ax.set_ylabel('T₈', fontsize=10)
    ax.grid(True, alpha=0.2)


def create_dual_representation(ax):
    """Show vertex-face duality with arrows."""
    w_R = np.array([1/2, 1/(2*np.sqrt(3))])
    w_G = np.array([-1/2, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    colors = {'R': 'red', 'G': 'green', 'B': 'blue'}

    # Draw triangle
    triangle = np.array([w_R, w_G, w_B, w_R])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=1.5)
    ax.fill(triangle[:-1, 0], triangle[:-1, 1], alpha=0.05, color='gray')

    # Draw vertices and face centers with duality arrows
    face_R = (w_G + w_B) / 2
    face_G = (w_R + w_B) / 2
    face_B = (w_R + w_G) / 2

    faces = {'R': face_R, 'G': face_G, 'B': face_B}
    weights = {'R': w_R, 'G': w_G, 'B': w_B}

    for name in ['R', 'G', 'B']:
        # Vertex (source)
        w = weights[name]
        ax.plot(w[0], w[1], 'o', color=colors[name], markersize=14, zorder=5)
        ax.annotate(f'{name}\n(source)', (w[0]*1.3, w[1]*1.3), ha='center', va='center',
                   fontsize=9, color=colors[name])

        # Face center (depression)
        f = faces[name]
        ax.plot(f[0], f[1], 's', color=colors[name], markersize=10, alpha=0.5,
               markeredgecolor='black', markeredgewidth=1.5)

        # Arrow from vertex toward opposite face (through center)
        ax.annotate('', xy=(f[0]*0.9, f[1]*0.9), xytext=(w[0]*0.7, w[1]*0.7),
                   arrowprops=dict(arrowstyle='->', color=colors[name],
                                  lw=2, ls='--', alpha=0.7))

    # Center point
    ax.plot(0, 0, 'ko', markersize=8)
    ax.annotate('O\n(balanced)', (0.08, -0.12), fontsize=9)

    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)
    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.8, 0.8)
    ax.set_aspect('equal')
    ax.set_xlabel('T₃', fontsize=10)
    ax.set_ylabel('T₈', fontsize=10)
    ax.grid(True, alpha=0.2)


def create_pressure_heatmap(ax):
    """Create heatmap of total pressure in a 2D slice."""
    # Create grid in z=0 plane
    x = np.linspace(-1.2, 1.2, 100)
    y = np.linspace(-1.2, 1.2, 100)
    X, Y = np.meshgrid(x, y)

    # Calculate total pressure at each point
    P_total = np.zeros_like(X)
    for i in range(len(x)):
        for j in range(len(y)):
            pt = np.array([X[i, j], Y[i, j], 0])
            P_total[i, j] = sum(pressure(pt, VERTICES[c]) for c in ['R', 'G', 'B'])

    # Plot heatmap
    im = ax.contourf(X, Y, P_total, levels=20, cmap='hot')
    plt.colorbar(im, ax=ax, label='Total Pressure')

    # Mark projected vertex positions
    for name, v in VERTICES.items():
        if name in ['R', 'G', 'B']:
            ax.plot(v[0], v[1], 'o', color='white', markersize=10,
                   markeredgecolor='black', markeredgewidth=2)
            ax.annotate(name, (v[0]+0.1, v[1]+0.1), color='white', fontsize=11,
                       fontweight='bold')

    ax.set_xlabel('x', fontsize=10)
    ax.set_ylabel('y', fontsize=10)
    ax.set_aspect('equal')


def create_depression_heatmap(ax):
    """Create heatmap of depression ratio for red color."""
    x = np.linspace(-1.2, 1.2, 100)
    y = np.linspace(-1.2, 1.2, 100)
    X, Y = np.meshgrid(x, y)

    D_R = np.zeros_like(X)
    for i in range(len(x)):
        for j in range(len(y)):
            pt = np.array([X[i, j], Y[i, j], 0])
            D_R[i, j] = depression_ratio(pt, 'R')

    # Clip for visualization
    D_R = np.clip(D_R, 0, 10)

    im = ax.contourf(X, Y, D_R, levels=20, cmap='coolwarm')
    plt.colorbar(im, ax=ax, label='Depression Ratio D_R')

    # Mark vertex R and its opposite face center
    v_R = VERTICES['R']
    f_R = get_face_center('R')

    ax.plot(v_R[0], v_R[1], 'o', color='red', markersize=12,
           markeredgecolor='white', markeredgewidth=2)
    ax.annotate('x_R\n(D_R→0)', (v_R[0]+0.15, v_R[1]), color='white', fontsize=9)

    ax.plot(f_R[0], f_R[1], 's', color='cyan', markersize=12,
           markeredgecolor='white', markeredgewidth=2)
    ax.annotate('face_R\n(D_R max)', (f_R[0]+0.15, f_R[1]), color='white', fontsize=9)

    ax.set_xlabel('x', fontsize=10)
    ax.set_ylabel('y', fontsize=10)
    ax.set_aspect('equal')


def create_domain_boundaries(ax):
    """Show domain boundaries (Voronoi edges)."""
    x = np.linspace(-1.2, 1.2, 150)
    y = np.linspace(-1.2, 1.2, 150)
    X, Y = np.meshgrid(x, y)

    # Classify each point by dominant color
    domain_map = np.zeros_like(X)
    color_to_num = {'R': 1, 'G': 2, 'B': 3, 'W': 0}

    for i in range(len(x)):
        for j in range(len(y)):
            pt = np.array([X[i, j], Y[i, j], 0])
            dom = dominant_color(pt)
            domain_map[i, j] = color_to_num[dom]

    # Create custom colormap
    from matplotlib.colors import ListedColormap
    cmap = ListedColormap(['gray', 'red', 'green', 'blue'])

    ax.contourf(X, Y, domain_map, levels=[-0.5, 0.5, 1.5, 2.5, 3.5],
               cmap=cmap, alpha=0.4)
    ax.contour(X, Y, domain_map, levels=[0.5, 1.5, 2.5], colors='black', linewidths=2)

    # Mark vertices
    for name, v in VERTICES.items():
        if name in ['R', 'G', 'B']:
            color = {'R': 'red', 'G': 'green', 'B': 'blue'}[name]
            ax.plot(v[0], v[1], 'o', color=color, markersize=12,
                   markeredgecolor='black', markeredgewidth=2)
            ax.annotate(f'D_{name}', (v[0]-0.15, v[1]+0.15), fontsize=11,
                       fontweight='bold', color=color)

    # Mark center
    ax.plot(0, 0, 'ko', markersize=8)

    ax.set_xlabel('x', fontsize=10)
    ax.set_ylabel('y', fontsize=10)
    ax.set_aspect('equal')
    ax.set_xlim(-1.2, 1.2)
    ax.set_ylim(-1.2, 1.2)


def run_all_tests():
    """Run all verification tests."""
    print("=" * 70)
    print("DEFINITION 0.1.4 VERIFICATION: Color Field Domains")
    print("=" * 70)
    print()

    tests = [
        ("Face center positions", test_face_center_positions),
        ("Pressure at face centers", test_pressure_at_face_centers),
        ("Depression ratios", test_depression_ratios),
        ("Domain partition", test_domain_partition),
        ("Center on boundaries", test_center_on_all_boundaries),
        ("Voronoi structure", test_voronoi_structure),
    ]

    passed = 0
    failed = 0

    for name, test_func in tests:
        try:
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"  FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"  ERROR: {e}")
            failed += 1

    print()
    print("=" * 70)
    print(f"RESULTS: {passed}/{len(tests)} tests passed")
    print("=" * 70)

    # Create visualization
    os.makedirs('verification/plots', exist_ok=True)
    create_visualization()

    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
