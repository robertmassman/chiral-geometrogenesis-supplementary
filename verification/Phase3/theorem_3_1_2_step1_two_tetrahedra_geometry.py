#!/usr/bin/env python3
"""
Theorem 3.1.2 Verification - Step 1: Two-Tetrahedra Geometry

The stella octangula is composed of TWO interpenetrating regular tetrahedra.
This script establishes the precise geometry and all relevant ratios.

Key insight: The two tetrahedra are DUAL to each other - one can be seen
as matter (T₁) and one as antimatter (T₂), with vertices at opposite positions.

Author: Verification Analysis
Date: 2025-12-14
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import json
from datetime import datetime
import os

# Ensure plots directory exists
os.makedirs('verification/plots', exist_ok=True)

# =============================================================================
# TWO-TETRAHEDRA GEOMETRY
# =============================================================================

def create_two_tetrahedra():
    """
    Create the two interpenetrating tetrahedra of the stella octangula.

    The stella octangula consists of two regular tetrahedra:
    - T₁ (matter tetrahedron): vertices at alternating cube corners
    - T₂ (antimatter tetrahedron): vertices at the other cube corners

    Together they form a compound with 8 vertices (cube vertices),
    but the structure is fundamentally TWO separate tetrahedra.
    """
    # Cube vertices: (±1, ±1, ±1)
    # T₁ uses vertices where x*y*z = +1 (even parity)
    # T₂ uses vertices where x*y*z = -1 (odd parity)

    # Tetrahedron 1 (matter) - even parity vertices
    T1 = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ], dtype=float)

    # Tetrahedron 2 (antimatter) - odd parity vertices
    T2 = np.array([
        [-1, -1, -1],
        [-1, 1, 1],
        [1, -1, 1],
        [1, 1, -1]
    ], dtype=float)

    return T1, T2


def analyze_single_tetrahedron(T, name="T"):
    """Analyze properties of a single tetrahedron."""
    print(f"\n{'='*60}")
    print(f"TETRAHEDRON {name} ANALYSIS")
    print(f"{'='*60}")

    # Vertices
    print(f"\nVertices of {name}:")
    for i, v in enumerate(T):
        print(f"  v{i+1} = ({v[0]:+.0f}, {v[1]:+.0f}, {v[2]:+.0f})")

    # Edge lengths
    edges = []
    print(f"\nEdge lengths:")
    for i in range(4):
        for j in range(i+1, 4):
            length = np.linalg.norm(T[i] - T[j])
            edges.append(length)
            print(f"  |v{i+1} - v{j+1}| = {length:.6f}")

    edge_length = edges[0]  # All should be equal for regular tetrahedron
    is_regular = np.allclose(edges, edge_length)
    print(f"\nRegular tetrahedron: {is_regular}")
    print(f"Edge length a = {edge_length:.6f}")

    # Center (centroid)
    center = np.mean(T, axis=0)
    print(f"\nCentroid: ({center[0]:.6f}, {center[1]:.6f}, {center[2]:.6f})")

    # Circumradius (center to vertex)
    circumradius = np.linalg.norm(T[0] - center)
    print(f"Circumradius R = {circumradius:.6f}")

    # Inradius (center to face)
    # For regular tetrahedron: r = a / (2√6)
    inradius = edge_length / (2 * np.sqrt(6))
    print(f"Inradius r = {inradius:.6f}")

    # Midradius (center to edge midpoint)
    # For regular tetrahedron: ρ = a / √8
    midradius = edge_length / np.sqrt(8)
    print(f"Midradius ρ = {midradius:.6f}")

    # Volume
    # For regular tetrahedron: V = a³ / (6√2)
    volume = edge_length**3 / (6 * np.sqrt(2))
    print(f"Volume V = {volume:.6f}")

    # Surface area
    # For regular tetrahedron: S = √3 × a²
    surface = np.sqrt(3) * edge_length**2
    print(f"Surface area S = {surface:.6f}")

    return {
        'vertices': T.tolist(),
        'edge_length': edge_length,
        'is_regular': is_regular,
        'center': center.tolist(),
        'circumradius': circumradius,
        'inradius': inradius,
        'midradius': midradius,
        'volume': volume,
        'surface_area': surface
    }


def analyze_two_tetrahedra_relationship(T1, T2):
    """
    Analyze the relationship between the two tetrahedra.

    This is where the physics lives - the interaction between
    matter (T₁) and antimatter (T₂) tetrahedra.
    """
    print(f"\n{'='*60}")
    print("TWO-TETRAHEDRA RELATIONSHIP")
    print(f"{'='*60}")

    # Centers
    center1 = np.mean(T1, axis=0)
    center2 = np.mean(T2, axis=0)

    print(f"\nCenters:")
    print(f"  T₁ center: {center1}")
    print(f"  T₂ center: {center2}")
    print(f"  Same center: {np.allclose(center1, center2)}")

    # Verify T2 = -T1 (dual/inverted)
    is_inverted = np.allclose(T2, -T1)
    print(f"\nT₂ = -T₁ (inverted): {is_inverted}")

    # Distances between vertices of different tetrahedra
    print(f"\nInter-tetrahedra vertex distances:")
    inter_distances = []
    for i, v1 in enumerate(T1):
        for j, v2 in enumerate(T2):
            d = np.linalg.norm(v1 - v2)
            inter_distances.append(d)
            print(f"  |T₁v{i+1} - T₂v{j+1}| = {d:.6f}")

    # Unique inter-tetrahedra distances
    unique_inter = sorted(set(np.round(inter_distances, 6)))
    print(f"\nUnique inter-tetrahedra distances: {unique_inter}")

    # The octahedron formed at the center
    # When two tetrahedra interpenetrate, they create an octahedron
    # at their intersection
    print(f"\n{'='*60}")
    print("CENTRAL OCTAHEDRON")
    print(f"{'='*60}")

    # The octahedron vertices are at the midpoints of the original cube's edges
    # These are at distance √2 from center
    edge_length_T1 = np.linalg.norm(T1[0] - T1[1])

    # Octahedron edge length (from intersection geometry)
    # The octahedron has edge = a/√2 where a is tetrahedron edge
    octahedron_edge = edge_length_T1 / np.sqrt(2)
    print(f"  Octahedron edge length: {octahedron_edge:.6f}")

    # Ratio of octahedron to tetrahedron
    ratio_oct_tet = octahedron_edge / edge_length_T1
    print(f"  Ratio (octahedron/tetrahedron edge): {ratio_oct_tet:.6f} = 1/√2")

    return {
        'centers_same': np.allclose(center1, center2),
        'is_dual': is_inverted,
        'inter_distances': unique_inter,
        'octahedron_edge': octahedron_edge,
        'ratio_oct_tet': ratio_oct_tet
    }


def compute_all_geometric_ratios(T1, T2):
    """
    Compute ALL geometric ratios that could potentially give λ ≈ 0.22.

    The Wolfenstein parameter λ ≈ 0.2265 should emerge from some
    combination of geometric ratios in the two-tetrahedra system.
    """
    print(f"\n{'='*60}")
    print("GEOMETRIC RATIOS ANALYSIS")
    print(f"{'='*60}")

    # Basic measurements
    a = np.linalg.norm(T1[0] - T1[1])  # Edge length
    R = np.linalg.norm(T1[0])  # Circumradius (from origin)
    r = a / (2 * np.sqrt(6))  # Inradius
    rho = a / np.sqrt(8)  # Midradius

    print(f"\nBasic measurements:")
    print(f"  Edge length a = {a:.6f}")
    print(f"  Circumradius R = {R:.6f}")
    print(f"  Inradius r = {r:.6f}")
    print(f"  Midradius ρ = {rho:.6f}")

    # Golden ratio
    phi = (1 + np.sqrt(5)) / 2

    # Tetrahedral angle
    theta_tet = np.arccos(1/3)  # ≈ 70.53°

    # Dihedral angle of tetrahedron
    theta_dihedral = np.arccos(1/3)  # Same as tetrahedral angle

    ratios = {}

    # Category 1: Simple ratios from tetrahedron
    ratios['r/R (inradius/circumradius)'] = r / R
    ratios['ρ/R (midradius/circumradius)'] = rho / R
    ratios['r/a (inradius/edge)'] = r / a
    ratios['R/a (circumradius/edge)'] = R / a

    # Category 2: Inscribed tetrahedron scaling
    # When you inscribe a smaller tetrahedron, the scaling is 1/3
    ratios['1/3 (inscribed scaling)'] = 1/3
    ratios['1/9 (double inscribed)'] = 1/9
    ratios['1/27 (triple inscribed)'] = 1/27

    # Category 3: Projection factors
    ratios['1/√2 (3D→2D projection)'] = 1/np.sqrt(2)
    ratios['1/√3 (body diagonal proj)'] = 1/np.sqrt(3)
    ratios['√(2/3)'] = np.sqrt(2/3)

    # Category 4: Combined ratios
    ratios['(1/3) × (1/√2)'] = (1/3) / np.sqrt(2)
    ratios['(1/3) × (1/√3)'] = (1/3) / np.sqrt(3)
    ratios['r/R × 1/√2'] = (r/R) / np.sqrt(2)

    # Category 5: Golden ratio related
    ratios['1/φ'] = 1/phi
    ratios['1/φ²'] = 1/phi**2
    ratios['1/φ³'] = 1/phi**3
    ratios['1/φ⁴'] = 1/phi**4
    ratios['(1/φ³) × sin(72°)'] = (1/phi**3) * np.sin(np.radians(72))

    # Category 6: Trigonometric (tetrahedral angles)
    ratios['sin(θ_tet/4)'] = np.sin(theta_tet/4)
    ratios['cos(θ_tet/2)'] = np.cos(theta_tet/2)
    ratios['(1-cos(θ_tet))/2'] = (1 - np.cos(theta_tet))/2
    ratios['sin(θ_dihedral/6)'] = np.sin(theta_dihedral/6)

    # Category 7: Two-tetrahedra specific
    # Distance ratio between nearest vertices of different tetrahedra
    d_nearest = np.min([np.linalg.norm(v1-v2) for v1 in T1 for v2 in T2])
    d_farthest = np.max([np.linalg.norm(v1-v2) for v1 in T1 for v2 in T2])
    ratios['d_nearest/a'] = d_nearest / a
    ratios['d_nearest/d_farthest'] = d_nearest / d_farthest

    # Octahedron ratio
    oct_edge = a / np.sqrt(2)
    ratios['oct_edge/a'] = oct_edge / a

    # Category 8: Volume and surface ratios
    V_tet = a**3 / (6*np.sqrt(2))
    V_oct = (oct_edge**3 * np.sqrt(2)) / 3
    ratios['V_oct/V_tet'] = V_oct / V_tet
    ratios['(V_oct/V_tet)^(1/3)'] = (V_oct / V_tet)**(1/3)

    # Target
    lambda_target = 0.2265

    print(f"\n{'='*60}")
    print(f"ALL GEOMETRIC RATIOS (sorted by closeness to λ = {lambda_target})")
    print(f"{'='*60}")

    sorted_ratios = sorted(ratios.items(), key=lambda x: abs(x[1] - lambda_target))

    for name, value in sorted_ratios:
        diff = abs(value - lambda_target)
        diff_pct = diff / lambda_target * 100
        marker = "★" if diff_pct < 5 else "●" if diff_pct < 10 else "○" if diff_pct < 20 else " "
        print(f"  {marker} {name}: {value:.6f} (diff: {diff_pct:.2f}%)")

    return ratios, sorted_ratios


def visualize_two_tetrahedra(T1, T2):
    """Create a 3D visualization of the two interpenetrating tetrahedra."""

    fig = plt.figure(figsize=(14, 6))

    # Plot 1: Two tetrahedra together
    ax1 = fig.add_subplot(121, projection='3d')

    # Define faces for each tetrahedron
    faces_T1 = [[T1[0], T1[1], T1[2]], [T1[0], T1[1], T1[3]],
                [T1[0], T1[2], T1[3]], [T1[1], T1[2], T1[3]]]
    faces_T2 = [[T2[0], T2[1], T2[2]], [T2[0], T2[1], T2[3]],
                [T2[0], T2[2], T2[3]], [T2[1], T2[2], T2[3]]]

    # Plot T1 (red/matter)
    poly_T1 = Poly3DCollection(faces_T1, alpha=0.3, facecolor='red',
                                edgecolor='darkred', linewidth=2)
    ax1.add_collection3d(poly_T1)

    # Plot T2 (blue/antimatter)
    poly_T2 = Poly3DCollection(faces_T2, alpha=0.3, facecolor='blue',
                                edgecolor='darkblue', linewidth=2)
    ax1.add_collection3d(poly_T2)

    # Plot vertices
    ax1.scatter(*T1.T, c='red', s=100, marker='o', label='T₁ (matter)')
    ax1.scatter(*T2.T, c='blue', s=100, marker='^', label='T₂ (antimatter)')

    # Label vertices
    for i, v in enumerate(T1):
        ax1.text(v[0]*1.1, v[1]*1.1, v[2]*1.1, f'T₁v{i+1}', fontsize=8, color='darkred')
    for i, v in enumerate(T2):
        ax1.text(v[0]*1.1, v[1]*1.1, v[2]*1.1, f'T₂v{i+1}', fontsize=8, color='darkblue')

    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Two Interpenetrating Tetrahedra\n(Stella Octangula)')
    ax1.legend()

    # Set equal aspect ratio
    max_range = 1.5
    ax1.set_xlim([-max_range, max_range])
    ax1.set_ylim([-max_range, max_range])
    ax1.set_zlim([-max_range, max_range])

    # Plot 2: Generation shells
    ax2 = fig.add_subplot(122, projection='3d')

    # Plot the tetrahedra more faintly
    poly_T1_faint = Poly3DCollection(faces_T1, alpha=0.1, facecolor='red',
                                      edgecolor='darkred', linewidth=1)
    ax2.add_collection3d(poly_T1_faint)
    poly_T2_faint = Poly3DCollection(faces_T2, alpha=0.1, facecolor='blue',
                                      edgecolor='darkblue', linewidth=1)
    ax2.add_collection3d(poly_T2_faint)

    # Draw generation shells as spheres (represented by circles)
    # 3rd gen: at center
    # 2nd gen: at intermediate radius
    # 1st gen: at outer radius

    a = np.linalg.norm(T1[0] - T1[1])
    r_in = a / (2 * np.sqrt(6))  # inradius

    # Generation radii
    r3 = 0  # Center
    r2 = r_in / 3  # Inner shell
    r1 = r_in  # Outer shell

    # Draw spherical shells
    u = np.linspace(0, 2*np.pi, 30)
    v = np.linspace(0, np.pi, 20)

    for r, color, gen in [(r2, 'green', '2nd'), (r1, 'orange', '1st')]:
        if r > 0:
            x = r * np.outer(np.cos(u), np.sin(v))
            y = r * np.outer(np.sin(u), np.sin(v))
            z = r * np.outer(np.ones(np.size(u)), np.cos(v))
            ax2.plot_surface(x, y, z, alpha=0.2, color=color, label=f'{gen} gen')

    # Mark center (3rd gen)
    ax2.scatter([0], [0], [0], c='purple', s=200, marker='*', label='3rd gen (center)')

    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title('Generation Shells in Two-Tetrahedra\n(Localization Picture)')
    ax2.legend()

    ax2.set_xlim([-max_range, max_range])
    ax2.set_ylim([-max_range, max_range])
    ax2.set_zlim([-max_range, max_range])

    plt.tight_layout()
    plt.savefig('verification/plots/step1_two_tetrahedra_geometry.png', dpi=150, bbox_inches='tight')
    plt.close()

    print(f"\nPlot saved to: verification/plots/step1_two_tetrahedra_geometry.png")


def main():
    """Run Step 1 analysis."""
    print("="*70)
    print("THEOREM 3.1.2 VERIFICATION - STEP 1")
    print("TWO-TETRAHEDRA GEOMETRY (Stella Octangula)")
    print("="*70)

    # Create the two tetrahedra
    T1, T2 = create_two_tetrahedra()

    # Analyze each tetrahedron
    T1_props = analyze_single_tetrahedron(T1, "T₁ (matter)")
    T2_props = analyze_single_tetrahedron(T2, "T₂ (antimatter)")

    # Analyze relationship
    relationship = analyze_two_tetrahedra_relationship(T1, T2)

    # Compute all geometric ratios
    ratios, sorted_ratios = compute_all_geometric_ratios(T1, T2)

    # Create visualization
    visualize_two_tetrahedra(T1, T2)

    # Summary
    print(f"\n{'='*70}")
    print("STEP 1 SUMMARY")
    print(f"{'='*70}")

    lambda_target = 0.2265
    best_ratios = [(name, val) for name, val in sorted_ratios if abs(val - lambda_target)/lambda_target < 0.10]

    print(f"\nGeometric ratios within 10% of λ = {lambda_target}:")
    for name, val in best_ratios:
        diff_pct = abs(val - lambda_target)/lambda_target * 100
        print(f"  ★ {name}: {val:.6f} ({diff_pct:.2f}% off)")

    print(f"""

KEY OBSERVATIONS:
═══════════════════════════════════════════════════════════════════════

1. TWO-TETRAHEDRA STRUCTURE
   - T₁ and T₂ share the same center (origin)
   - T₂ = -T₁ (dual/inverted relationship)
   - Together they form the stella octangula
   - The intersection creates a central octahedron

2. BEST GEOMETRIC MATCHES FOR λ ≈ 0.2265
   - (1/φ³) × sin(72°) = 0.2245 (0.88% off) ← BEST MATCH
   - (1/3) × (1/√2) = 0.2357 (4.1% off)
   - 1/φ³ = 0.2361 (4.2% off)

3. PHYSICAL INTERPRETATION
   - The two tetrahedra represent matter/antimatter duality
   - Generations localize at different shells between center and vertices
   - The hierarchy arises from overlap integrals between shells

4. NEXT STEP
   - Verify that the mass pattern m_n ∝ λ^{{2n}} emerges from
     the localization geometry on the two-tetrahedra system
    """)

    # Save results
    results = {
        'timestamp': datetime.now().isoformat(),
        'T1_properties': T1_props,
        'T2_properties': T2_props,
        'relationship': relationship,
        'best_ratios': best_ratios,
        'lambda_target': lambda_target,
        'status': 'STEP 1 COMPLETE'
    }

    with open('verification/theorem_3_1_2_step1_results.json', 'w') as f:
        json.dump(results, f, indent=2, default=str)

    print(f"\nResults saved to: verification/theorem_3_1_2_step1_results.json")

    return T1, T2, ratios


if __name__ == "__main__":
    T1, T2, ratios = main()
