#!/usr/bin/env python3
"""
Interactive 3D Stella Octangula Visualization for Theorem 0.0.2

Run this script to generate the stella octangula figure with right-handed
chirality arrows, intersection center, and time axis along [1,1,1].

Output: fig_thm_0_0_2_stella_3d.pdf and fig_thm_0_0_2_stella_3d.png

Usage:
    python fig_thm_0_0_2_stella_3d.py

Source: verification/shared/stella_octangula_3d_interactive.py
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
               linewidth=3, zorder=10, label='Geometric center')
    ax.text(0.15, 0.15, 0.15, 'O', fontsize=12, fontweight='bold',
            ha='left', va='bottom')

    # Plot vertices
    # T+ vertices
    ax.scatter(*T_plus[0], c='gold', s=250, marker='*', edgecolor='black', linewidth=2, zorder=5)
    ax.scatter(*T_plus[1], c='red', s=200, edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_plus[2], c='green', s=200, edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_plus[3], c='blue', s=200, edgecolor='black', linewidth=1, zorder=5)

    # T- vertices
    ax.scatter(*T_minus[0], c='gold', s=250, marker='*', edgecolor='black', linewidth=2, zorder=5)
    ax.scatter(*T_minus[1], c='#FF6666', s=200, marker='s', edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_minus[2], c='#66FF66', s=200, marker='s', edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_minus[3], c='#6666FF', s=200, marker='s', edgecolor='black', linewidth=1, zorder=5)

    # Draw lines from each vertex to the center (showing the intersection structure)
    for v in T_plus:
        ax.plot3D([v[0], 0], [v[1], 0], [v[2], 0], 'b:', linewidth=1, alpha=0.4)
    for v in T_minus:
        ax.plot3D([v[0], 0], [v[1], 0], [v[2], 0], 'r:', linewidth=1, alpha=0.4)

    # Draw the [1,1,1] axis through the singlet (connects W and W̄ apexes)
    axis_length = 1.8
    axis_dir = np.array([1, 1, 1]) / np.sqrt(3)  # Normalized [1,1,1] direction
    axis_start = -axis_dir * axis_length
    axis_end = axis_dir * axis_length

    # Draw the axis as a thick green line
    ax.quiver(axis_start[0], axis_start[1], axis_start[2],
              (axis_end - axis_start)[0], (axis_end - axis_start)[1], (axis_end - axis_start)[2],
              color='green', arrow_length_ratio=0.08, linewidth=4, alpha=0.9,
              label='[1,1,1] axis')

    # Add labels for past/future along the time axis
    ax.text(axis_start[0]-0.1, axis_start[1]-0.1, axis_start[2]-0.1,
            r'$\bar{W}$' + '\n(past)', fontsize=10, ha='center', va='top', color='olive')
    ax.text(axis_end[0]+0.1, axis_end[1]+0.1, axis_end[2]+0.1,
            '(future)', fontsize=10, ha='center', va='bottom', color='olive')

    # Draw chirality arrows on the base triangle (R-G-B) - right-handed: R->G->B->R
    def draw_3d_arrow(start, end, color='purple', offset_scale=0.2):
        """Draw an arrow slightly offset from the edge to show direction."""
        midpoint = (start + end) / 2
        direction = end - start
        direction = direction / np.linalg.norm(direction)
        # Offset perpendicular to edge and toward center of triangle
        center = (T_plus[1] + T_plus[2] + T_plus[3]) / 3
        to_center = center - midpoint
        to_center = to_center / np.linalg.norm(to_center)
        # Move outward (away from center)
        offset = -to_center * offset_scale
        arrow_start = midpoint + offset - direction * 0.2
        arrow_end = midpoint + offset + direction * 0.2
        ax.quiver(arrow_start[0], arrow_start[1], arrow_start[2],
                  (arrow_end - arrow_start)[0], (arrow_end - arrow_start)[1], (arrow_end - arrow_start)[2],
                  color=color, arrow_length_ratio=0.35, linewidth=3)

    # R->G, G->B, B->R (right-handed chirality on fundamental triangle)
    draw_3d_arrow(T_plus[1], T_plus[2])  # R -> G
    draw_3d_arrow(T_plus[2], T_plus[3])  # G -> B
    draw_3d_arrow(T_plus[3], T_plus[1])  # B -> R

    # Add vertex labels
    label_offset = 0.25
    ax.text(T_plus[0][0]+label_offset, T_plus[0][1]+label_offset, T_plus[0][2]+label_offset,
            'W', fontsize=14, fontweight='bold', color='darkgoldenrod')
    ax.text(T_plus[1][0]+label_offset, T_plus[1][1]-label_offset, T_plus[1][2]-label_offset,
            'R', fontsize=14, fontweight='bold', color='red')
    ax.text(T_plus[2][0]-label_offset*1.5, T_plus[2][1]+label_offset, T_plus[2][2]-label_offset,
            'G', fontsize=14, fontweight='bold', color='green')
    ax.text(T_plus[3][0]-label_offset, T_plus[3][1]-label_offset, T_plus[3][2]+label_offset,
            'B', fontsize=14, fontweight='bold', color='blue')

    ax.text(T_minus[0][0]-label_offset*1.5, T_minus[0][1]-label_offset, T_minus[0][2]-label_offset,
            r'$\bar{W}$', fontsize=14, fontweight='bold', color='darkgoldenrod')
    ax.text(T_minus[1][0]-label_offset*1.5, T_minus[1][1]+label_offset, T_minus[1][2]+label_offset,
            r'$\bar{R}$', fontsize=12, color='#CC0000')
    ax.text(T_minus[2][0]+label_offset, T_minus[2][1]-label_offset*1.5, T_minus[2][2]+label_offset,
            r'$\bar{G}$', fontsize=12, color='#008800')
    ax.text(T_minus[3][0]+label_offset, T_minus[3][1]+label_offset, T_minus[3][2]-label_offset*1.5,
            r'$\bar{B}$', fontsize=12, color='#0000CC')

    # Set labels and title
    ax.set_xlabel('X', fontsize=12)
    ax.set_ylabel('Y', fontsize=12)
    ax.set_zlabel('Z', fontsize=12)
    ax.set_title('Stella Octangula\n(Right-handed chirality: R→G→B→R)',
                 fontsize=14, fontweight='bold')

    # Set equal aspect ratio and limits
    ax.set_box_aspect([1,1,1])
    limit = 1.6
    ax.set_xlim([-limit, limit])
    ax.set_ylim([-limit, limit])
    ax.set_zlim([-limit, limit])

    # Set a better initial viewing angle (looking down the [1,1,1] axis)
    ax.view_init(elev=28, azim=39)

    # Add info text
    fig.text(0.02, 0.02,
             'Blue solid: T+ (fundamental)\nRed dashed: T- (anti-fundamental)\n'
             'Gold center: Geometric center\nPurple arrows: Right-handed chirality\n'
             r'Green arrow: Internal time $\tau$ along [1,1,1]',
             fontsize=10, verticalalignment='bottom',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

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
