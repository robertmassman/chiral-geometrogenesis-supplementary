#!/usr/bin/env python3
"""
Figure 6: 8 Tetrahedra at Vertex -> Stella Octangula

Generates publication-quality figure showing how 8 tetrahedra meet at an
FCC vertex and partition into two groups of 4, forming the stella octangula.

Key insight: Each honeycomb tetrahedron points toward a cube corner,
and those 8 cube corners ARE the stella vertices. The parity partition
of the tetrahedra corresponds exactly to the T+/T- partition of the stella.

This bridges the stella octangula (Theorem 0.0.3) and honeycomb (Theorem 0.0.6).

Three panels:
- (a) All 8 tetrahedra meeting at vertex, with cube corners shown
- (b) Parity partition with cube corners colored by parity
- (c) Connect the cube corners to form stella octangula

Output: fig_thm_0_0_3_stella_vertex.pdf, fig_thm_0_0_3_stella_vertex.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.lines import Line2D
import matplotlib.patches as mpatches
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'serif',
    'font.serif': ['Times New Roman', 'DejaVu Serif'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})


def create_fig_thm_0_0_3_stella_vertex():
    """
    Visualize how 8 tetrahedra meet at an FCC vertex and partition into
    two groups of 4, forming the stella octangula.
    """
    fig = plt.figure(figsize=(14, 5))

    # FCC lattice: vertices at (i,j,k) where i+j+k is even
    # Origin (0,0,0) is an FCC vertex
    # Nearest FCC neighbors are at distance sqrt(2), e.g., (1,1,0), (1,0,1), etc.

    # The 12 nearest FCC neighbors of the origin (distance sqrt(2))
    fcc_neighbors = np.array([
        [1, 1, 0], [1, -1, 0], [-1, 1, 0], [-1, -1, 0],
        [1, 0, 1], [1, 0, -1], [-1, 0, 1], [-1, 0, -1],
        [0, 1, 1], [0, 1, -1], [0, -1, 1], [0, -1, -1]
    ])

    # The 8 cube corners - these are the STELLA VERTICES
    # Each honeycomb tetrahedron points toward one of these corners
    cube_corners = np.array([
        [1, 1, 1], [1, 1, -1], [1, -1, 1], [1, -1, -1],
        [-1, 1, 1], [-1, 1, -1], [-1, -1, 1], [-1, -1, -1]
    ])

    # Partition cube corners by parity (xyz > 0 vs xyz < 0)
    # T+ (even parity): xyz > 0
    stella_T_plus = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]])
    # T- (odd parity): xyz < 0
    stella_T_minus = np.array([[1, 1, -1], [1, -1, 1], [-1, 1, 1], [-1, -1, -1]])

    # Each tetrahedron sharing the origin uses 3 FCC neighbors that form a triangle
    # The tetrahedron "points toward" the cube corner in that octant
    # T+ tetrahedra point toward T+ stella vertices, T- toward T- stella vertices
    tetrahedra_T_plus = [
        [[1, 1, 0], [1, 0, 1], [0, 1, 1]],       # points toward (1,1,1)
        [[1, -1, 0], [1, 0, -1], [0, -1, -1]],   # points toward (1,-1,-1)
        [[-1, 1, 0], [-1, 0, -1], [0, 1, -1]],   # points toward (-1,1,-1)
        [[-1, -1, 0], [-1, 0, 1], [0, -1, 1]],   # points toward (-1,-1,1)
    ]
    tetrahedra_T_minus = [
        [[1, 1, 0], [1, 0, -1], [0, 1, -1]],     # points toward (1,1,-1)
        [[1, -1, 0], [1, 0, 1], [0, -1, 1]],     # points toward (1,-1,1)
        [[-1, 1, 0], [-1, 0, 1], [0, 1, 1]],     # points toward (-1,1,1)
        [[-1, -1, 0], [-1, 0, -1], [0, -1, -1]], # points toward (-1,-1,-1)
    ]
    tetrahedra_T_plus = [np.array(t) for t in tetrahedra_T_plus]
    tetrahedra_T_minus = [np.array(t) for t in tetrahedra_T_minus]

    origin = np.array([0, 0, 0])

    def draw_tetrahedron(ax, verts, color, alpha=0.3, edge_color=None):
        """Draw a tetrahedron with origin and 3 other vertices."""
        if edge_color is None:
            edge_color = color
        faces = [
            [origin, verts[0], verts[1]],
            [origin, verts[1], verts[2]],
            [origin, verts[2], verts[0]],
            [verts[0], verts[1], verts[2]]
        ]
        ax.add_collection3d(Poly3DCollection(faces, alpha=alpha,
                                              facecolor=color, edgecolor=edge_color, lw=0.8))

    # --- Panel (a): All 8 tetrahedra meeting at vertex, with cube corners shown ---
    ax1 = fig.add_subplot(131, projection='3d')

    # Draw all 8 tetrahedra in gray
    for tet in tetrahedra_T_plus + tetrahedra_T_minus:
        draw_tetrahedron(ax1, tet, '#95a5a6', alpha=0.2, edge_color='#7f8c8d')

    # Draw the central vertex
    ax1.scatter([0], [0], [0], c='gold', s=250, marker='*',
                edgecolors='black', linewidths=1.5, zorder=15)

    # Draw FCC neighbors (tetrahedron base vertices)
    ax1.scatter(fcc_neighbors[:, 0], fcc_neighbors[:, 1], fcc_neighbors[:, 2],
                c='#3498db', s=40, edgecolors='black', linewidths=0.5, alpha=0.7)

    # Draw cube corners (stella vertices) - show where tetrahedra point
    ax1.scatter(cube_corners[:, 0], cube_corners[:, 1], cube_corners[:, 2],
                c='#9b59b6', s=60, marker='D', edgecolors='black', linewidths=0.8, alpha=0.8)

    # Draw dashed lines from origin to cube corners to show directions
    for corner in cube_corners:
        ax1.plot3D([0, corner[0]], [0, corner[1]], [0, corner[2]],
                   color='#9b59b6', lw=1, alpha=0.4, linestyle='--')

    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('(a) 8 tetrahedra point to 8 corners', fontsize=10)
    ax1.view_init(elev=15, azim=45)
    ax1.set_box_aspect([1, 1, 1])

    # Legend for panel (a)
    legend_elements_a = [
        mpatches.Patch(facecolor='#95a5a6', edgecolor='#7f8c8d', alpha=0.4, label='Honeycomb tet'),
        Line2D([0], [0], marker='D', color='w', markerfacecolor='#9b59b6',
               markeredgecolor='black', markersize=8, label='Cube corner'),
    ]
    ax1.legend(handles=legend_elements_a, loc='upper left', fontsize=7)

    # --- Panel (b): Partition with cube corners colored by parity ---
    ax2 = fig.add_subplot(132, projection='3d')

    # Draw T+ tetrahedra (blue)
    for tet in tetrahedra_T_plus:
        draw_tetrahedron(ax2, tet, '#3498db', alpha=0.3, edge_color='#2980b9')

    # Draw T- tetrahedra (red)
    for tet in tetrahedra_T_minus:
        draw_tetrahedron(ax2, tet, '#e74c3c', alpha=0.3, edge_color='#c0392b')

    # Draw the central vertex
    ax2.scatter([0], [0], [0], c='gold', s=250, marker='*',
                edgecolors='black', linewidths=1.5, zorder=15)

    # Draw T+ cube corners (blue) with lines from origin
    ax2.scatter(stella_T_plus[:, 0], stella_T_plus[:, 1], stella_T_plus[:, 2],
                c='#3498db', s=80, marker='D', edgecolors='black', linewidths=1, zorder=10)
    for corner in stella_T_plus:
        ax2.plot3D([0, corner[0]], [0, corner[1]], [0, corner[2]],
                   color='#3498db', lw=1.5, alpha=0.6, linestyle='--')

    # Draw T- cube corners (red) with lines from origin
    ax2.scatter(stella_T_minus[:, 0], stella_T_minus[:, 1], stella_T_minus[:, 2],
                c='#e74c3c', s=80, marker='D', edgecolors='black', linewidths=1, zorder=10)
    for corner in stella_T_minus:
        ax2.plot3D([0, corner[0]], [0, corner[1]], [0, corner[2]],
                   color='#e74c3c', lw=1.5, alpha=0.6, linestyle='--')

    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title(r'(b) Parity partition $\to$ stella vertices', fontsize=10)
    ax2.view_init(elev=15, azim=45)
    ax2.set_box_aspect([1, 1, 1])

    # Legend for panel (b)
    legend_elements_b = [
        mpatches.Patch(facecolor='#3498db', edgecolor='#2980b9', alpha=0.5, label=r'$T_+$ tet $\to$ $T_+$ vertex'),
        mpatches.Patch(facecolor='#e74c3c', edgecolor='#c0392b', alpha=0.5, label=r'$T_-$ tet $\to$ $T_-$ vertex'),
    ]
    ax2.legend(handles=legend_elements_b, loc='upper left', fontsize=7)

    # --- Panel (c): Connect the cube corners to form stella octangula ---
    ax3 = fig.add_subplot(133, projection='3d')

    # Draw T+ tetrahedron of stella (blue) - connecting the 4 T+ cube corners
    T_plus_faces = [
        [stella_T_plus[0], stella_T_plus[1], stella_T_plus[2]],
        [stella_T_plus[0], stella_T_plus[1], stella_T_plus[3]],
        [stella_T_plus[0], stella_T_plus[2], stella_T_plus[3]],
        [stella_T_plus[1], stella_T_plus[2], stella_T_plus[3]]
    ]
    ax3.add_collection3d(Poly3DCollection(T_plus_faces, alpha=0.35,
                                           facecolor='#3498db', edgecolor='#2980b9', lw=1.5))

    # Draw T- tetrahedron of stella (red) - connecting the 4 T- cube corners
    T_minus_faces = [
        [stella_T_minus[0], stella_T_minus[1], stella_T_minus[2]],
        [stella_T_minus[0], stella_T_minus[1], stella_T_minus[3]],
        [stella_T_minus[0], stella_T_minus[2], stella_T_minus[3]],
        [stella_T_minus[1], stella_T_minus[2], stella_T_minus[3]]
    ]
    ax3.add_collection3d(Poly3DCollection(T_minus_faces, alpha=0.35,
                                           facecolor='#e74c3c', edgecolor='#c0392b', lw=1.5))

    # Draw the central vertex (origin = center of stella)
    ax3.scatter([0], [0], [0], c='gold', s=250, marker='*',
                edgecolors='black', linewidths=1.5, zorder=15)

    # Draw stella vertices (same cube corners, now connected)
    ax3.scatter(stella_T_plus[:, 0], stella_T_plus[:, 1], stella_T_plus[:, 2],
                c='#3498db', s=80, marker='D', edgecolors='black', linewidths=1)
    ax3.scatter(stella_T_minus[:, 0], stella_T_minus[:, 1], stella_T_minus[:, 2],
                c='#e74c3c', s=80, marker='D', edgecolors='black', linewidths=1)

    ax3.set_xlabel('X')
    ax3.set_ylabel('Y')
    ax3.set_zlabel('Z')
    ax3.set_title(r'(c) Connect corners $\to$ stella', fontsize=10)
    ax3.view_init(elev=15, azim=45)
    ax3.set_box_aspect([1, 1, 1])

    # Legend for panel (c)
    legend_elements_c = [
        mpatches.Patch(facecolor='#3498db', edgecolor='#2980b9', alpha=0.5, label=r'$T_+$ tetrahedron'),
        mpatches.Patch(facecolor='#e74c3c', edgecolor='#c0392b', alpha=0.5, label=r'$T_-$ tetrahedron'),
        Line2D([0], [0], marker='*', color='w', markerfacecolor='gold',
               markeredgecolor='black', markersize=12, label='FCC vertex = center'),
    ]
    ax3.legend(handles=legend_elements_c, loc='upper left', fontsize=7)

    plt.tight_layout()
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_3_stella_vertex.pdf')
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_3_stella_vertex.png')
    plt.close()
    print(f"✓ Figure 6 saved to {OUTPUT_DIR}/fig_thm_0_0_3_stella_vertex.pdf")
    print(f"✓ Figure 6 saved to {OUTPUT_DIR}/fig_thm_0_0_3_stella_vertex.png")


if __name__ == '__main__':
    create_fig_thm_0_0_3_stella_vertex()
