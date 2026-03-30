#!/usr/bin/env python3
"""
Figure 6: Tetrahedral-Octahedral Honeycomb (Theorem 0.0.6)

Generates publication-quality figure showing the tetrahedral-octahedral
honeycomb (octet truss) structure.

Key properties:
- Tetrahedra + octahedra fill 3D space
- Each vertex has 8 tetrahedra meeting
- Stella octangula embedded at each vertex
- FCC lattice coordinates
- Continuum limit gives SO(3) invariance

Lean 4 Reference: Theorem_0_0_6.lean - honeycomb_uniqueness
Proof Document: docs/proofs/foundations/Theorem-0.0.6-Honeycomb-Uniqueness.md

Output: fig_thm_0_0_3_honeycomb.pdf, fig_thm_0_0_3_honeycomb.png
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


def fcc_vertices(n=1):
    """Generate FCC lattice vertices in a cube of side 2n."""
    verts = []
    for i in range(-n, n+1):
        for j in range(-n, n+1):
            for k in range(-n, n+1):
                if (i + j + k) % 2 == 0:
                    verts.append([i, j, k])
    return np.array(verts)


def create_figure_6():
    """
    Generate visualization of the tetrahedral-octahedral honeycomb (octet truss).

    From Lean 4 / Proof doc:
    - honeycomb_embeds_stella: Stella octangula at each vertex
    - fcc_lattice_coordinates: Pre-geometric coordinates via FCC
    - phase_coherence: SU(3) phases match across shared faces
    - continuum_limit: R^3 emerges with SO(3) invariance
    """
    fig = plt.figure(figsize=(10, 4))

    sqrt2 = np.sqrt(2)

    # --- Panel (a): FCC lattice with tetrahedron and octahedron ---
    ax1 = fig.add_subplot(121, projection='3d')

    # FCC lattice
    fcc = fcc_vertices(1)

    # Plot FCC vertices
    ax1.scatter(fcc[:, 0], fcc[:, 1], fcc[:, 2], c='#3498db', s=60,
                edgecolors='black', linewidths=0.5, alpha=0.8, zorder=5)

    # Draw FCC edges
    for i, v1 in enumerate(fcc):
        for v2 in fcc[i+1:]:
            dist = np.linalg.norm(v1 - v2)
            if abs(dist - sqrt2) < 0.1:
                ax1.plot3D([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
                          'k-', lw=0.8, alpha=0.5)

    # Highlight an OCTAHEDRON using actual FCC lattice points
    # An octahedron in FCC has 6 vertices forming a regular octahedron
    # These 6 points all satisfy i+j+k even (FCC condition):
    oct_verts = np.array([
        [1, 0, 1], [-1, 0, 1],   # +x and -x at z=1
        [0, 1, 1], [0, -1, 1],   # +y and -y at z=1
        [0, 0, 2], [0, 0, 0]     # top and bottom
    ])

    # Draw octahedron faces (green, semi-transparent)
    # Vertices: 0=[1,0,1], 1=[-1,0,1], 2=[0,1,1], 3=[0,-1,1], 4=[0,0,2](top), 5=[0,0,0](bottom)
    oct_color = '#27ae60'
    oct_faces = [
        # Top 4 faces (connect to vertex 4 = top)
        [oct_verts[4], oct_verts[0], oct_verts[2]],  # top, +x, +y
        [oct_verts[4], oct_verts[2], oct_verts[1]],  # top, +y, -x
        [oct_verts[4], oct_verts[1], oct_verts[3]],  # top, -x, -y
        [oct_verts[4], oct_verts[3], oct_verts[0]],  # top, -y, +x
        # Bottom 4 faces (connect to vertex 5 = bottom)
        [oct_verts[5], oct_verts[0], oct_verts[2]],  # bottom, +x, +y
        [oct_verts[5], oct_verts[2], oct_verts[1]],  # bottom, +y, -x
        [oct_verts[5], oct_verts[1], oct_verts[3]],  # bottom, -x, -y
        [oct_verts[5], oct_verts[3], oct_verts[0]],  # bottom, -y, +x
    ]
    ax1.add_collection3d(Poly3DCollection(oct_faces, alpha=0.25,
                                           facecolor=oct_color, edgecolor='#1e8449', lw=1.5))

    # Mark octahedron center
    oct_center = np.mean(oct_verts, axis=0)
    ax1.scatter([oct_center[0]], [oct_center[1]], [oct_center[2]],
                c=oct_color, s=100, marker='o', edgecolors='black', linewidths=1, zorder=10)
    ax1.text(oct_center[0]-0.5, oct_center[1]+0.8, oct_center[2],
             'Oct', fontsize=8, color=oct_color)

    # Add a tetrahedron adjacent to the octahedron
    tet_verts = np.array([
        [0, 0, 0],
        [-1, -1, 0],
        [-1, 0, -1],
        [0, -1, -1]
    ])
    tet_faces = [
        [tet_verts[0], tet_verts[1], tet_verts[2]],
        [tet_verts[0], tet_verts[1], tet_verts[3]],
        [tet_verts[0], tet_verts[2], tet_verts[3]],
        [tet_verts[1], tet_verts[2], tet_verts[3]]
    ]
    ax1.add_collection3d(Poly3DCollection(tet_faces, alpha=0.25,
                                           facecolor='#e74c3c', edgecolor='#c0392b', lw=1.5))

    # Mark tetrahedron center
    tet_center = np.mean(tet_verts, axis=0)
    ax1.scatter([tet_center[0]], [tet_center[1]], [tet_center[2]],
                c='#e74c3c', s=100, marker='o', edgecolors='black', linewidths=1, zorder=10)
    ax1.text(tet_center[0]-0.8, tet_center[1]-0.3, tet_center[2],
             'Tet', fontsize=8, color='#c0392b')

    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('(a) Tet + Oct in FCC')
    ax1.view_init(elev=25, azim=35)
    ax1.set_box_aspect([1, 1, 1])

    # Legend
    legend_elements = [
        mpatches.Patch(facecolor='#e74c3c', edgecolor='#c0392b', alpha=0.5, label='Tetrahedron'),
        mpatches.Patch(facecolor=oct_color, edgecolor='#1e8449', alpha=0.5, label='Octahedron'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#e74c3c',
               markeredgecolor='black', markersize=8, label='Tet center'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor=oct_color,
               markeredgecolor='black', markersize=8, label='Oct center'),
    ]
    ax1.legend(handles=legend_elements, loc='upper left', fontsize=6)

    # --- Panel (b): Properties and derivation chain ---
    ax2 = fig.add_subplot(122)
    ax2.axis('off')

    info_text = """Theorem 0.0.6: Spatial Extension
─────────────────────────────────

Honeycomb Structure:
• Tetrahedra + octahedra fill 3D space
• Also called "octet truss"
• Each vertex has 8 tetrahedra meeting

Stella Embedding:
• At each vertex: 8 tetrahedra partition
  into two groups of 4
• These form two interpenetrating tetrahedra
• = Stella octangula (Thm 0.0.3)

FCC Lattice Coordinates:
$\\Lambda_{FCC} = \\{(n_1, n_2, n_3) \\in \\mathbb{Z}^3 :$
$\\quad n_1 + n_2 + n_3 \\equiv 0\\ (\\mathrm{mod}\\ 2)\\}$

Uniqueness: Dihedral angle argument
• Regular tetrahedron: $\\arccos(1/3) \\approx 70.5°$
• 5×70.5°=352.7° (gap), 6×70.5°=423.2° (overlap)
• => Must include octahedra: unique solution

Continuum Limit:
• $O_h$ symmetry → $SO(3)$ invariance
• Emergent metric assigns distances
• Bootstrap resolved: no prior metric needed

Lean 4: honeycomb_uniqueness"""

    ax2.text(0.05, 0.98, info_text, transform=ax2.transAxes, fontsize=8,
             verticalalignment='top', fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='#f8f9fa', alpha=0.9, pad=0.5))

    ax2.set_title('(b) Properties')

    plt.tight_layout()
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_3_honeycomb.pdf')
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_3_honeycomb.png')
    plt.close()
    print(f"✓ Figure 6 saved to {OUTPUT_DIR}/fig_thm_0_0_3_honeycomb.pdf")
    print(f"✓ Figure 6 saved to {OUTPUT_DIR}/fig_thm_0_0_3_honeycomb.png")


if __name__ == '__main__':
    create_figure_6()
