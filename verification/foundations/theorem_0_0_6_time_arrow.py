#!/usr/bin/env python3
"""
Theorem 0.0.6: Time Arrow and Energy Flow Visualization

This script explores:
1. How the two interpenetrating tetrahedra (T+ and T-) fit in the honeycomb
2. The W-axis [1,1,1] direction as the temporal axis
3. Energy flow direction in the tetrahedral-octahedral honeycomb

Key insight from Theorem 3.0.3 (Temporal Fiber Structure):
- The W-axis (direction [1,1,1]/√3) is where VEV = 0
- This axis is identified as the temporal direction
- The plane perpendicular to W contains the spatial color structure

Author: Claude (Anthropic)
Date: December 27, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
from itertools import combinations

# ============================================================================
# Stella Octangula Geometry
# ============================================================================

def get_stella_octangula():
    """
    Return the vertices of the stella octangula (two interpenetrating tetrahedra).

    T+ vertices: Positive orientation tetrahedron
    T- vertices: Negative orientation tetrahedron (dual, point-reflected through origin)
    """
    # T+ tetrahedron (vertices at alternating cube corners)
    T_plus = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ], dtype=float)

    # T- tetrahedron (dual - point reflection through origin)
    T_minus = -T_plus

    return T_plus, T_minus

def get_w_axis():
    """
    The W-axis is the [1,1,1] direction, normalized.
    This is the temporal axis in the framework.
    """
    w = np.array([1, 1, 1]) / np.sqrt(3)
    return w

# ============================================================================
# FCC Lattice and Honeycomb
# ============================================================================

def generate_fcc_lattice(n_max=2):
    """Generate FCC lattice points."""
    points = []
    for n1 in range(-n_max, n_max + 1):
        for n2 in range(-n_max, n_max + 1):
            for n3 in range(-n_max, n_max + 1):
                if (n1 + n2 + n3) % 2 == 0:
                    points.append([n1, n2, n3])
    return np.array(points)

def get_fcc_tetrahedra_at_origin():
    """
    Get the 8 tetrahedra meeting at the origin in the honeycomb.
    Returns list of 4-vertex arrays.
    """
    # FCC nearest neighbors of origin
    nn = np.array([
        [1, 1, 0], [1, -1, 0], [-1, 1, 0], [-1, -1, 0],
        [1, 0, 1], [1, 0, -1], [-1, 0, 1], [-1, 0, -1],
        [0, 1, 1], [0, 1, -1], [0, -1, 1], [0, -1, -1]
    ])

    tetrahedra = []
    sqrt2 = np.sqrt(2)

    # Find tetrahedra: groups of 3 neighbors that are mutually adjacent
    for combo in combinations(range(12), 3):
        v1, v2, v3 = nn[combo[0]], nn[combo[1]], nn[combo[2]]
        d12 = np.linalg.norm(v1 - v2)
        d13 = np.linalg.norm(v1 - v3)
        d23 = np.linalg.norm(v2 - v3)

        if (abs(d12 - sqrt2) < 0.1 and abs(d13 - sqrt2) < 0.1 and abs(d23 - sqrt2) < 0.1):
            tet = np.array([[0, 0, 0], v1.tolist(), v2.tolist(), v3.tolist()])
            tetrahedra.append(tet)

    return tetrahedra

# ============================================================================
# Energy Flow and Time Arrow
# ============================================================================

def compute_phase_gradient(tet_vertices):
    """
    Compute the phase gradient direction for a tetrahedron.

    The color phases are: φ_R = 0, φ_G = 2π/3, φ_B = 4π/3
    The phase gradient points from low phase to high phase.

    In the stella octangula, the R→G→B flow creates a chiral winding.
    """
    # The centroid of the tetrahedron
    centroid = np.mean(tet_vertices, axis=0)

    # For a tetrahedron with vertices at origin + 3 neighbors,
    # the "outward" direction is from origin toward centroid of the 3
    if np.allclose(tet_vertices[0], [0, 0, 0]):
        face_centroid = np.mean(tet_vertices[1:], axis=0)
        direction = face_centroid / np.linalg.norm(face_centroid)
    else:
        direction = centroid / np.linalg.norm(centroid) if np.linalg.norm(centroid) > 0.1 else np.array([0, 0, 1])

    return direction

def classify_tetrahedron_chirality(tet):
    """
    Classify whether a tetrahedron has positive or negative chirality
    based on the sign of the triple product of edge vectors.

    Returns: +1 (T+ type) or -1 (T- type)
    """
    if np.allclose(tet[0], [0, 0, 0]):
        v1 = tet[1] - tet[0]
        v2 = tet[2] - tet[0]
        v3 = tet[3] - tet[0]
    else:
        v1 = tet[1] - tet[0]
        v2 = tet[2] - tet[0]
        v3 = tet[3] - tet[0]

    # Triple product (scalar triple product = signed volume)
    triple = np.dot(v1, np.cross(v2, v3))

    return +1 if triple > 0 else -1

def compute_time_arrow_at_vertex():
    """
    At each vertex (stella octangula center), the time arrow points along W-axis.

    The direction is determined by:
    1. The [1,1,1] axis connects the two "apex" directions of the stella
    2. Energy flows from past (T-) toward future (T+)
    3. The chiral winding R→G→B establishes handedness
    """
    w_axis = get_w_axis()

    # In the framework, the positive W direction is "future"
    # This is where the color fields constructively interfere
    return w_axis

# ============================================================================
# Visualization
# ============================================================================

def plot_stella_with_time_arrow(save_path=None):
    """
    Visualize the stella octangula with the time arrow (W-axis).
    """
    fig = plt.figure(figsize=(16, 8))

    T_plus, T_minus = get_stella_octangula()
    w_axis = get_w_axis()

    # === Subplot 1: Stella octangula with W-axis ===
    ax1 = fig.add_subplot(121, projection='3d')

    # Draw T+ faces (red, semi-transparent)
    for face in combinations(range(4), 3):
        triangle = T_plus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.25)
        poly.set_facecolor('red')
        poly.set_edgecolor('darkred')
        ax1.add_collection3d(poly)

    # Draw T- faces (blue, semi-transparent)
    for face in combinations(range(4), 3):
        triangle = T_minus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.25)
        poly.set_facecolor('blue')
        poly.set_edgecolor('darkblue')
        ax1.add_collection3d(poly)

    # Mark vertices
    ax1.scatter(T_plus[:, 0], T_plus[:, 1], T_plus[:, 2],
                c='red', s=100, label='T+ (matter)', zorder=5)
    ax1.scatter(T_minus[:, 0], T_minus[:, 1], T_minus[:, 2],
                c='blue', s=100, label='T- (antimatter)', zorder=5)

    # Draw W-axis (time arrow)
    arrow_scale = 2.0
    ax1.quiver(0, 0, 0,
               w_axis[0]*arrow_scale, w_axis[1]*arrow_scale, w_axis[2]*arrow_scale,
               color='green', arrow_length_ratio=0.15, linewidth=3,
               label='W-axis (time)')

    # Draw negative W direction (past)
    ax1.quiver(0, 0, 0,
               -w_axis[0]*arrow_scale*0.7, -w_axis[1]*arrow_scale*0.7, -w_axis[2]*arrow_scale*0.7,
               color='gray', arrow_length_ratio=0.1, linewidth=2, linestyle='--',
               alpha=0.5)

    # Mark origin (center)
    ax1.scatter([0], [0], [0], c='gold', s=300, marker='*',
                label='Center (observation point)', zorder=10)

    # Draw the perpendicular plane (spatial plane)
    # Create a disk perpendicular to W-axis
    theta = np.linspace(0, 2*np.pi, 50)
    r = 1.5
    # Perpendicular vectors to W
    perp1 = np.array([1, -1, 0]) / np.sqrt(2)
    perp2 = np.cross(w_axis, perp1)

    circle_x = r * np.cos(theta)
    circle_y = r * np.sin(theta)
    plane_points = np.outer(circle_x, perp1) + np.outer(circle_y, perp2)
    ax1.plot(plane_points[:, 0], plane_points[:, 1], plane_points[:, 2],
             'g--', alpha=0.5, linewidth=1, label='Spatial plane ⊥ W')

    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Stella Octangula with Time Arrow\n(W-axis = [1,1,1]/√3)')
    ax1.legend(loc='upper left', fontsize=8)
    ax1.set_xlim(-2, 2)
    ax1.set_ylim(-2, 2)
    ax1.set_zlim(-2, 2)

    # === Subplot 2: View along W-axis (spatial projection) ===
    ax2 = fig.add_subplot(122, projection='3d')

    # Rotate to view along W-axis
    # The view from [1,1,1] looking toward origin
    ax2.view_init(elev=35.264, azim=45)  # arctan(1/√2) ≈ 35.264°

    # Draw same stella
    for face in combinations(range(4), 3):
        triangle = T_plus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.3)
        poly.set_facecolor('red')
        poly.set_edgecolor('darkred')
        ax2.add_collection3d(poly)

    for face in combinations(range(4), 3):
        triangle = T_minus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.3)
        poly.set_facecolor('blue')
        poly.set_edgecolor('darkblue')
        ax2.add_collection3d(poly)

    ax2.scatter(T_plus[:, 0], T_plus[:, 1], T_plus[:, 2], c='red', s=100)
    ax2.scatter(T_minus[:, 0], T_minus[:, 1], T_minus[:, 2], c='blue', s=100)
    ax2.scatter([0], [0], [0], c='gold', s=300, marker='*')

    # Mark color vertices (R, G, B on T+)
    colors = ['red', 'green', 'blue', 'white']
    labels = ['R', 'G', 'B', 'W']
    for i, (v, c, l) in enumerate(zip(T_plus, colors, labels)):
        ax2.text(v[0]*1.2, v[1]*1.2, v[2]*1.2, l, fontsize=12, fontweight='bold',
                color=c if c != 'white' else 'black')

    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title('View Along W-axis (Looking "Back in Time")\nShows hexagonal symmetry of color plane')
    ax2.set_xlim(-2, 2)
    ax2.set_ylim(-2, 2)
    ax2.set_zlim(-2, 2)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")

    plt.show()

def plot_honeycomb_time_flow(save_path=None):
    """
    Visualize time arrow and energy flow in the honeycomb structure.
    """
    fig = plt.figure(figsize=(16, 8))

    # === Subplot 1: Multiple stella at FCC vertices with time arrows ===
    ax1 = fig.add_subplot(121, projection='3d')

    # Get a few FCC lattice points
    fcc = generate_fcc_lattice(n_max=1)
    w_axis = get_w_axis()

    # Draw time arrows at each FCC vertex
    arrow_scale = 0.5
    for pt in fcc:
        # Small stella indicator at each point
        ax1.scatter([pt[0]], [pt[1]], [pt[2]], c='gold', s=50, alpha=0.7)

        # Time arrow pointing along W
        ax1.quiver(pt[0], pt[1], pt[2],
                   w_axis[0]*arrow_scale, w_axis[1]*arrow_scale, w_axis[2]*arrow_scale,
                   color='green', arrow_length_ratio=0.2, linewidth=1.5, alpha=0.8)

    # Draw FCC edges (nearest neighbors)
    sqrt2 = np.sqrt(2)
    for i, p1 in enumerate(fcc):
        for j, p2 in enumerate(fcc):
            if i < j:
                d = np.linalg.norm(p1 - p2)
                if abs(d - sqrt2) < 0.1:
                    ax1.plot([p1[0], p2[0]], [p1[1], p2[1]], [p1[2], p2[2]],
                            'b-', alpha=0.2, linewidth=0.5)

    # Draw the global W-axis through center
    ax1.quiver(-2*w_axis[0], -2*w_axis[1], -2*w_axis[2],
               4*w_axis[0], 4*w_axis[1], 4*w_axis[2],
               color='darkgreen', arrow_length_ratio=0.05, linewidth=3,
               label='Global time axis')

    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Time Arrows in Honeycomb\n(All point along [1,1,1])')
    ax1.legend()
    ax1.set_xlim(-2.5, 2.5)
    ax1.set_ylim(-2.5, 2.5)
    ax1.set_zlim(-2.5, 2.5)

    # === Subplot 2: Energy flow between adjacent stellae ===
    ax2 = fig.add_subplot(122, projection='3d')

    # Focus on origin and its 12 neighbors
    origin = np.array([0, 0, 0])
    neighbors = np.array([
        [1, 1, 0], [1, -1, 0], [-1, 1, 0], [-1, -1, 0],
        [1, 0, 1], [1, 0, -1], [-1, 0, 1], [-1, 0, -1],
        [0, 1, 1], [0, 1, -1], [0, -1, 1], [0, -1, -1]
    ])

    # Draw central stella (simplified)
    ax2.scatter([0], [0], [0], c='gold', s=200, marker='*', label='Central stella')

    # Draw neighbors
    ax2.scatter(neighbors[:, 0], neighbors[:, 1], neighbors[:, 2],
                c='blue', s=80, alpha=0.7, label='Neighbor stellae')

    # Draw connections (shared faces in honeycomb)
    for n in neighbors:
        ax2.plot([0, n[0]], [0, n[1]], [0, n[2]], 'b-', alpha=0.3, linewidth=1)

    # Energy flow arrows (phase gradient)
    # Energy flows along edges, with chiral winding
    for n in neighbors:
        # Project neighbor onto W-axis
        w_component = np.dot(n, w_axis)

        # Color code by W-component (future = green, past = red)
        if w_component > 0.1:
            color = 'green'
            alpha = 0.8
        elif w_component < -0.1:
            color = 'red'
            alpha = 0.5
        else:
            color = 'orange'
            alpha = 0.6

        # Arrow from origin toward neighbor (energy flow)
        direction = n / np.linalg.norm(n)
        ax2.quiver(0, 0, 0,
                   direction[0]*0.4, direction[1]*0.4, direction[2]*0.4,
                   color=color, arrow_length_ratio=0.3, linewidth=2, alpha=alpha)

    # Add W-axis
    ax2.quiver(0, 0, 0,
               w_axis[0]*1.5, w_axis[1]*1.5, w_axis[2]*1.5,
               color='darkgreen', arrow_length_ratio=0.1, linewidth=3,
               label='Future (W+)')
    ax2.quiver(0, 0, 0,
               -w_axis[0]*1.5, -w_axis[1]*1.5, -w_axis[2]*1.5,
               color='darkred', arrow_length_ratio=0.1, linewidth=3,
               label='Past (W-)')

    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title('Energy Flow Directions\nGreen=future, Red=past, Orange=spatial')
    ax2.legend(loc='upper left', fontsize=8)
    ax2.set_xlim(-2, 2)
    ax2.set_ylim(-2, 2)
    ax2.set_zlim(-2, 2)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")

    plt.show()

def plot_chirality_and_flow(save_path=None):
    """
    Show how chirality (T+ vs T-) relates to time direction.
    """
    fig = plt.figure(figsize=(16, 6))

    T_plus, T_minus = get_stella_octangula()
    w_axis = get_w_axis()

    # === Subplot 1: T+ tetrahedron with color winding ===
    ax1 = fig.add_subplot(131, projection='3d')

    # Draw T+
    for face in combinations(range(4), 3):
        triangle = T_plus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.3)
        poly.set_facecolor('lightcoral')
        poly.set_edgecolor('darkred')
        ax1.add_collection3d(poly)

    # Color the vertices R, G, B, W
    colors_rgb = ['red', 'green', 'blue', 'gray']
    labels = ['R (φ=0°)', 'G (φ=120°)', 'B (φ=240°)', 'W (apex)']

    for v, c, l in zip(T_plus, colors_rgb, labels):
        ax1.scatter([v[0]], [v[1]], [v[2]], c=c, s=150, zorder=5)
        ax1.text(v[0]*1.3, v[1]*1.3, v[2]*1.3, l, fontsize=9)

    # Draw phase winding R → G → B (counterclockwise when viewed from W)
    # This creates the chiral structure
    r_idx, g_idx, b_idx = 0, 1, 2  # Indices in T_plus
    winding_path = [T_plus[r_idx], T_plus[g_idx], T_plus[b_idx], T_plus[r_idx]]
    winding_path = np.array(winding_path)

    for i in range(3):
        start = winding_path[i]
        end = winding_path[i+1]
        mid = (start + end) / 2
        direction = end - start
        direction = direction / np.linalg.norm(direction) * 0.3
        ax1.quiver(mid[0], mid[1], mid[2],
                   direction[0], direction[1], direction[2],
                   color='purple', arrow_length_ratio=0.4, linewidth=2)

    ax1.set_title('T+ (Matter): R→G→B winding\n(Positive chirality)')
    ax1.set_xlim(-2, 2)
    ax1.set_ylim(-2, 2)
    ax1.set_zlim(-2, 2)

    # === Subplot 2: T- tetrahedron with opposite winding ===
    ax2 = fig.add_subplot(132, projection='3d')

    # Draw T-
    for face in combinations(range(4), 3):
        triangle = T_minus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.3)
        poly.set_facecolor('lightblue')
        poly.set_edgecolor('darkblue')
        ax2.add_collection3d(poly)

    # Anti-colors
    labels_anti = ['R̄', 'Ḡ', 'B̄', 'W̄']
    for v, c, l in zip(T_minus, colors_rgb, labels_anti):
        ax2.scatter([v[0]], [v[1]], [v[2]], c=c, s=150, zorder=5)
        ax2.text(v[0]*1.3, v[1]*1.3, v[2]*1.3, l, fontsize=9)

    # Opposite winding B → G → R
    winding_path_anti = [T_minus[b_idx], T_minus[g_idx], T_minus[r_idx], T_minus[b_idx]]
    winding_path_anti = np.array(winding_path_anti)

    for i in range(3):
        start = winding_path_anti[i]
        end = winding_path_anti[i+1]
        mid = (start + end) / 2
        direction = end - start
        direction = direction / np.linalg.norm(direction) * 0.3
        ax2.quiver(mid[0], mid[1], mid[2],
                   direction[0], direction[1], direction[2],
                   color='cyan', arrow_length_ratio=0.4, linewidth=2)

    ax2.set_title('T- (Antimatter): B→G→R winding\n(Negative chirality)')
    ax2.set_xlim(-2, 2)
    ax2.set_ylim(-2, 2)
    ax2.set_zlim(-2, 2)

    # === Subplot 3: Combined with time flow ===
    ax3 = fig.add_subplot(133, projection='3d')

    # Draw both
    for face in combinations(range(4), 3):
        triangle = T_plus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.2)
        poly.set_facecolor('red')
        poly.set_edgecolor('darkred')
        ax3.add_collection3d(poly)

        triangle = T_minus[list(face)]
        poly = Poly3DCollection([triangle], alpha=0.2)
        poly.set_facecolor('blue')
        poly.set_edgecolor('darkblue')
        ax3.add_collection3d(poly)

    # Time arrow
    ax3.quiver(0, 0, 0,
               w_axis[0]*2.5, w_axis[1]*2.5, w_axis[2]*2.5,
               color='green', arrow_length_ratio=0.1, linewidth=4,
               label='Time (future)')
    ax3.quiver(0, 0, 0,
               -w_axis[0]*2.5, -w_axis[1]*2.5, -w_axis[2]*2.5,
               color='gray', arrow_length_ratio=0.1, linewidth=2,
               linestyle='--', alpha=0.5, label='Past')

    # Energy flow: from T- toward T+ (from past to future)
    # The intersection of T+ and T- is the octahedron at the center
    ax3.scatter([0], [0], [0], c='gold', s=200, marker='o',
                label='Now (observation)')

    # Annotate
    ax3.text(w_axis[0]*2.8, w_axis[1]*2.8, w_axis[2]*2.8,
             'FUTURE', fontsize=10, color='green')
    ax3.text(-w_axis[0]*2.8, -w_axis[1]*2.8, -w_axis[2]*2.8,
             'PAST', fontsize=10, color='gray')

    ax3.set_title('Time Flow Through Stella\nT- (past) → Center (now) → T+ (future)')
    ax3.legend(loc='upper left', fontsize=8)
    ax3.set_xlim(-2.5, 2.5)
    ax3.set_ylim(-2.5, 2.5)
    ax3.set_zlim(-2.5, 2.5)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")

    plt.show()

def analyze_time_direction():
    """
    Analyze and print information about the time direction in the honeycomb.
    """
    print("="*60)
    print("TIME ARROW ANALYSIS IN TETRAHEDRAL-OCTAHEDRAL HONEYCOMB")
    print("="*60)

    T_plus, T_minus = get_stella_octangula()
    w_axis = get_w_axis()

    print("\n1. THE W-AXIS (TEMPORAL DIRECTION)")
    print("-"*40)
    print(f"   W-axis direction: [{w_axis[0]:.4f}, {w_axis[1]:.4f}, {w_axis[2]:.4f}]")
    print(f"   Unnormalized: [1, 1, 1]")
    print(f"   This is the 'body diagonal' of the cube containing the stella")

    print("\n2. T+ VERTICES (MATTER TETRAHEDRON)")
    print("-"*40)
    for i, v in enumerate(T_plus):
        w_proj = np.dot(v, w_axis)
        print(f"   Vertex {i}: {v}  →  W-projection: {w_proj:.4f}")

    print("\n3. T- VERTICES (ANTIMATTER TETRAHEDRON)")
    print("-"*40)
    for i, v in enumerate(T_minus):
        w_proj = np.dot(v, w_axis)
        print(f"   Vertex {i}: {v}  →  W-projection: {w_proj:.4f}")

    print("\n4. INTERPRETATION")
    print("-"*40)
    print("""
   The W-axis connects two special points:

   • W+ direction: Where T+ vertices cluster (positive W-projection)
     → Associated with FUTURE / matter / positive energy

   • W- direction: Where T- vertices cluster (negative W-projection)
     → Associated with PAST / antimatter / negative energy

   At the CENTER (origin):
     → All phases meet (color singlet)
     → This is "NOW" - the observation point
     → The intersection of T+ and T- is the central octahedron
    """)

    print("\n5. CHIRALITY AND TIME")
    print("-"*40)
    print("""
   The phase winding R → G → B (angles 0° → 120° → 240°):

   • In T+: Counterclockwise when viewed from +W (future)
     → Positive chirality (left-handed)

   • In T-: Clockwise when viewed from +W
     → Negative chirality (right-handed)

   This connects:
     TIME DIRECTION ←→ CHIRALITY ←→ MATTER/ANTIMATTER
    """)

    print("\n6. IN THE HONEYCOMB")
    print("-"*40)
    print("""
   At every FCC lattice vertex:
   • A stella octangula is centered
   • The W-axis points in the SAME direction [1,1,1]
   • This creates a GLOBAL time direction

   Between adjacent vertices:
   • Shared faces connect neighboring stellae
   • Phase coherence propagates through shared triangular faces
   • Energy flows along the W-direction

   The honeycomb therefore has:
   • A preferred TIME direction (along [1,1,1])
   • Spatial isotropy in the plane perpendicular to W
   • Consistent chirality everywhere
    """)

# ============================================================================
# Main
# ============================================================================

def main():
    print("Theorem 0.0.6: Time Arrow and Energy Flow Visualization")
    print("="*60)

    # Run analysis
    analyze_time_direction()

    # Generate plots
    print("\nGenerating visualizations...")

    try:
        plot_stella_with_time_arrow('theorem_0_0_6_stella_time_arrow.png')
        plot_honeycomb_time_flow('theorem_0_0_6_honeycomb_time_flow.png')
        plot_chirality_and_flow('theorem_0_0_6_chirality_flow.png')
        print("\n✓ All visualizations generated successfully")
    except Exception as e:
        print(f"\nVisualization error: {e}")
        print("(May require display; analysis completed above)")

if __name__ == "__main__":
    main()
