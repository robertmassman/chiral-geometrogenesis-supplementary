#!/usr/bin/env python3
"""
3D Stella Octangula Visualization for Theorems 0.0.2 and 0.0.3

Run this script to generate the stella octangula figure showing:
- Two interpenetrating tetrahedra (T+ fundamental, T- anti-fundamental)
- 8-vertex structure (6 color vertices + 2 singlet apex vertices)
- Geometric center at origin
- Singlet axis along [1,1,1] direction

Note: Chirality arrows are NOT included here; they are introduced later
in Theorem 0.0.5 (Chirality Selection from Geometry).

Output: fig_thm_0_0_2_stella_3d.pdf and fig_thm_0_0_2_stella_3d.png

Usage:
    python fig_thm_0_0_2_stella_3d.py
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from pathlib import Path

# Output directory
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)


def create_interactive_stella_octangula():
    """Create an interactive 3D stella octangula visualization."""

    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')

    # Tetrahedron T+ vertices
    # Index 0 = W (apex), 1 = R, 2 = G, 3 = B
    T_plus = np.array([
        [1, 1, 1],      # apex (W vertex - singlet)
        [1, -1, -1],    # R
        [-1, 1, -1],    # G
        [-1, -1, 1]     # B
    ])

    # Tetrahedron T- vertices (dual)
    T_minus = np.array([
        [-1, -1, -1],   # apex (W-bar vertex - singlet)
        [-1, 1, 1],     # R-bar
        [1, -1, 1],     # G-bar
        [1, 1, -1]      # B-bar
    ])

    # Define faces for each tetrahedron
    def get_tetra_faces(verts):
        return [
            [verts[0], verts[1], verts[2]],
            [verts[0], verts[1], verts[3]],
            [verts[0], verts[2], verts[3]],
            [verts[1], verts[2], verts[3]]
        ]

    # Plot T+ (blue, transparent)
    faces_plus = get_tetra_faces(T_plus)
    poly_plus = Poly3DCollection(faces_plus, alpha=0.15, facecolor='blue',
                                  edgecolor='blue', linewidth=1)
    ax.add_collection3d(poly_plus)

    # Plot T- (red, transparent)
    faces_minus = get_tetra_faces(T_minus)
    poly_minus = Poly3DCollection(faces_minus, alpha=0.15, facecolor='red',
                                   edgecolor='red', linewidth=1)
    ax.add_collection3d(poly_minus)

    # Draw edges explicitly for clarity
    edges = [(0,1), (0,2), (0,3), (1,2), (2,3), (3,1)]
    for i, j in edges:
        ax.plot3D(*zip(T_plus[i], T_plus[j]), 'b-', linewidth=2, alpha=0.8)
        ax.plot3D(*zip(T_minus[i], T_minus[j]), 'r--', linewidth=2, alpha=0.8)

    # Plot the INTERSECTION CENTER (origin) - this is where everything meets
    ax.scatter(0, 0, 0, c='gold', s=400, marker='o', edgecolor='black',
               linewidth=3, zorder=10)

    # Plot vertices
    # Color scheme matches fig_su3_weight_diagram.py for consistency
    # Fundamental: vibrant colors, Anti-fundamental: darker versions
    colors_fund = ['#e74c3c', '#27ae60', '#3498db']  # R, G, B (vibrant)
    colors_anti = ['#c0392b', '#1e8449', '#2874a6']  # R̄, Ḡ, B̄ (darker)

    # T+ vertices (fundamental) - circles
    ax.scatter(*T_plus[0], c='gold', s=250, marker='*', edgecolor='black', linewidth=2, zorder=5)
    ax.scatter(*T_plus[1], c=colors_fund[0], s=200, edgecolor='black', linewidth=1.5, zorder=5)  # R
    ax.scatter(*T_plus[2], c=colors_fund[1], s=200, edgecolor='black', linewidth=1.5, zorder=5)  # G
    ax.scatter(*T_plus[3], c=colors_fund[2], s=200, edgecolor='black', linewidth=1.5, zorder=5)  # B

    # T- vertices (anti-fundamental) - squares
    ax.scatter(*T_minus[0], c='gold', s=250, marker='*', edgecolor='black', linewidth=2, zorder=5)
    ax.scatter(*T_minus[1], c=colors_anti[0], s=200, marker='s', edgecolor='black', linewidth=1.5, zorder=5)  # R̄
    ax.scatter(*T_minus[2], c=colors_anti[1], s=200, marker='s', edgecolor='black', linewidth=1.5, zorder=5)  # Ḡ
    ax.scatter(*T_minus[3], c=colors_anti[2], s=200, marker='s', edgecolor='black', linewidth=1.5, zorder=5)  # B̄

    # Create legend entries (dummy plots for legend, matching weight diagram style)
    # Fundamental triangle
    ax.plot([], [], 'b-', linewidth=2.5, label=r'$\mathbf{3}$ (fundamental)')
    # Anti-fundamental triangle
    ax.plot([], [], 'r--', linewidth=2.0, label=r'$\bar{\mathbf{3}}$ (anti-fundamental)')
    # Singlet
    ax.scatter([], [], c='gold', s=100, marker='*', edgecolor='black', linewidth=1,
               label=r'Singlet ($W, \bar{W}$)')
    # Singlet axis
    ax.plot([], [], color='green', linewidth=3, label='Singlet axis [1,1,1]')

    # Draw lines from each vertex to the center (showing the intersection structure)
    for v in T_plus:
        ax.plot3D([v[0], 0], [v[1], 0], [v[2], 0], 'b:', linewidth=1, alpha=0.4)
    for v in T_minus:
        ax.plot3D([v[0], 0], [v[1], 0], [v[2], 0], 'r:', linewidth=1, alpha=0.4)

    # Draw the [1,1,1] singlet axis connecting W̄ to W through the center
    # The singlet axis connects the two apex vertices (both project to origin in weight space)
    W_apex = T_plus[0]      # (1, 1, 1)
    W_bar_apex = T_minus[0]  # (-1, -1, -1)

    # Draw the axis as a thick green arrow from W̄ to W
    ax.quiver(W_bar_apex[0], W_bar_apex[1], W_bar_apex[2],
              (W_apex - W_bar_apex)[0], (W_apex - W_bar_apex)[1], (W_apex - W_bar_apex)[2],
              color='green', arrow_length_ratio=0.06, linewidth=4, alpha=0.9)

    # Note: W and W̄ labels are added with the vertex labels below

    # Add vertex labels (colors match the vertex markers)
    label_offset = 0.25
    ax.text(T_plus[0][0]+label_offset, T_plus[0][1]+label_offset, T_plus[0][2]+label_offset,
            'W', fontsize=14, fontweight='bold', color='darkgoldenrod')
    ax.text(T_plus[1][0]+label_offset, T_plus[1][1]-label_offset, T_plus[1][2]-label_offset,
            'R', fontsize=14, fontweight='bold', color='#e74c3c')
    ax.text(T_plus[2][0]-label_offset*1.5, T_plus[2][1]+label_offset, T_plus[2][2]-label_offset,
            'G', fontsize=14, fontweight='bold', color='#27ae60')
    ax.text(T_plus[3][0]-label_offset, T_plus[3][1]-label_offset, T_plus[3][2]+label_offset,
            'B', fontsize=14, fontweight='bold', color='#3498db')

    ax.text(T_minus[0][0]-label_offset*1.5, T_minus[0][1]-label_offset, T_minus[0][2]-label_offset,
            r'$\bar{W}$', fontsize=14, fontweight='bold', color='darkgoldenrod')
    ax.text(T_minus[1][0]-label_offset*1.5, T_minus[1][1]+label_offset, T_minus[1][2]+label_offset,
            r'$\bar{R}$', fontsize=12, color='#c0392b')
    ax.text(T_minus[2][0]+label_offset, T_minus[2][1]-label_offset*1.5, T_minus[2][2]+label_offset,
            r'$\bar{G}$', fontsize=12, color='#1e8449')
    ax.text(T_minus[3][0]+label_offset, T_minus[3][1]+label_offset, T_minus[3][2]-label_offset*1.5,
            r'$\bar{B}$', fontsize=12, color='#2874a6')

    # Set labels and title
    ax.set_xlabel('X', fontsize=12)
    ax.set_ylabel('Y', fontsize=12)
    ax.set_zlabel('Z', fontsize=12)
    ax.set_title('Stella Octangula: Geometric Realization of SU(3)',
                 fontsize=14, fontweight='bold')

    # Set equal aspect ratio and limits
    ax.set_box_aspect([1,1,1])
    limit = 1.6
    ax.set_xlim([-limit, limit])
    ax.set_ylim([-limit, limit])
    ax.set_zlim([-limit, limit])

    # Set a better initial viewing angle (looking down the [1,1,1] axis)
    ax.view_init(elev=28, azim=39)

    # Add legend (matching style of fig_su3_weight_diagram)
    ax.legend(loc='upper left', fontsize=9)

    plt.tight_layout()
    return fig, ax


if __name__ == "__main__":
    print("Creating 3D Stella Octangula visualization...")

    fig, ax = create_interactive_stella_octangula()

    # Save to output directory
    for ext in ['pdf', 'png']:
        filepath = output_dir / f'fig_thm_0_0_2_stella_3d.{ext}'
        fig.savefig(filepath, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    plt.close()
    print("Done!")
