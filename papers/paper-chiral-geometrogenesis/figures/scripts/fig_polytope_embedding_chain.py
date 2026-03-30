#!/usr/bin/env python3
"""
Figure: Polytope Embedding Chain (Section 8)

Three-panel visualization of the geometric embedding chain:
(a) Stella octangula (8 vertices) — S4 x Z2 symmetry
(b) 16-cell (8 vertices) — B4 symmetry, 4D cross-polytope
(c) 24-cell (24 vertices) — F4 / D4 triality

Connecting annotations show the embedding steps: shadow/phi and rectification.

Key physics:
- Stella octangula embeds in the 16-cell via the shadow map phi
- 16-cell rectifies to the 24-cell (midpoints of edges)
- 24-cell has F4 symmetry group with D4 triality
- This chain ultimately leads to the GUT embedding SU(5) -> SM

Proof Document: docs/proofs/foundations/Theorem-0.0.4-GUT-Embedding.md
Paper Section: Section 8 (Polytope Embedding Chain)
Output: fig_polytope_embedding_chain.pdf, fig_polytope_embedding_chain.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import os

# Paths
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# Colors (no purple)
C_TP = (0.20, 0.60, 0.86)
C_TM = (0.91, 0.30, 0.24)
C_ORANGE = (0.90, 0.50, 0.13)
C_GREEN = (0.15, 0.68, 0.15)
C_GOLD = (0.85, 0.65, 0.13)
C_GRAY = (0.55, 0.55, 0.55)

TET_FACE_IDX = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]


def proj_4d_to_3d(pts, w_factor=0.3):
    """Project 4D points to 3D via perspective-like projection."""
    x = pts[:, 0] + w_factor * pts[:, 3]
    y = pts[:, 1] + w_factor * pts[:, 3]
    z = pts[:, 2] + w_factor * pts[:, 3]
    return np.column_stack([x, y, z])


def draw_tet_filled(ax, verts, facecolor, edgecolor, alpha=0.3, lw=1.5):
    """Draw tetrahedron with filled translucent faces."""
    v = np.array(verts, dtype=float)
    faces = [v[list(f)] for f in TET_FACE_IDX]
    poly = Poly3DCollection(faces, alpha=alpha, facecolor=facecolor,
                            edgecolor=edgecolor, linewidth=lw)
    ax.add_collection3d(poly)


def setup_3d_axis(ax, lim=1.3):
    """Style a 3D axis cleanly."""
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.set_axis_off()
    ax.view_init(elev=20, azim=40)


def main():
    fig = plt.figure(figsize=(15, 5.5))

    # Shared geometry: stella octangula
    s3 = np.sqrt(3)
    t_plus = np.array([
        [1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]
    ], dtype=float) / s3  # Normalized
    t_minus = -t_plus

    # ==============================================================
    # (a) Stella Octangula (8 vertices)
    # ==============================================================
    ax1 = fig.add_subplot(131, projection='3d')

    # Draw T+ (blue)
    draw_tet_filled(ax1, t_plus, C_TP, C_TP, alpha=0.20, lw=1.5)
    # Draw T- (red)
    draw_tet_filled(ax1, t_minus, C_TM, C_TM, alpha=0.20, lw=1.5)

    # Vertices
    ax1.scatter(t_plus[:, 0], t_plus[:, 1], t_plus[:, 2],
                color=C_TP, s=100, edgecolors='black', linewidths=1.2,
                zorder=10, depthshade=False)
    ax1.scatter(t_minus[:, 0], t_minus[:, 1], t_minus[:, 2],
                color=C_TM, s=100, edgecolors='black', linewidths=1.2,
                zorder=10, depthshade=False)

    setup_3d_axis(ax1, lim=0.75)
    ax1.set_title(r'(a) Stella Octangula' + '\n' + r'$S_4 \times \mathbb{Z}_2$',
                  fontsize=11, fontweight='bold', pad=-2)
    ax1.text2D(0.50, 0.02, '8 vertices', transform=ax1.transAxes,
               fontsize=9, ha='center', color=C_GRAY)

    # ==============================================================
    # (b) 16-cell / Cross-polytope (8 vertices in 4D)
    # ==============================================================
    ax2 = fig.add_subplot(132, projection='3d')

    # 16-cell vertices: +/-e_i in R^4
    cell16_4d = np.zeros((8, 4))
    for i in range(4):
        cell16_4d[i, i] = 1.0
        cell16_4d[i + 4, i] = -1.0

    cell16_3d = proj_4d_to_3d(cell16_4d, w_factor=0.35)

    # Draw T+ and T- as embedded tetrahedra
    t_plus_16 = cell16_3d[:4]
    t_minus_16 = cell16_3d[4:]
    draw_tet_filled(ax2, t_plus_16, C_TP, C_TP, alpha=0.12, lw=1.0)
    draw_tet_filled(ax2, t_minus_16, C_TM, C_TM, alpha=0.12, lw=1.0)

    # Draw cross-edges (connecting + to - vertices)
    for i in range(8):
        for j in range(i + 1, 8):
            dist_sq = np.sum((cell16_4d[i] - cell16_4d[j]) ** 2)
            if np.isclose(dist_sq, 2.0):
                # Only cross-edges (between + and - halves)
                if (i < 4 and j >= 4) or (i >= 4 and j < 4):
                    ax2.plot([cell16_3d[i, 0], cell16_3d[j, 0]],
                             [cell16_3d[i, 1], cell16_3d[j, 1]],
                             [cell16_3d[i, 2], cell16_3d[j, 2]],
                             '-', color=C_GRAY, lw=0.6, alpha=0.3)

    # Vertices
    ax2.scatter(cell16_3d[:4, 0], cell16_3d[:4, 1], cell16_3d[:4, 2],
                color=C_TP, s=100, edgecolors='black', linewidths=1.2,
                zorder=10, depthshade=False)
    ax2.scatter(cell16_3d[4:, 0], cell16_3d[4:, 1], cell16_3d[4:, 2],
                color=C_TM, s=100, edgecolors='black', linewidths=1.2,
                zorder=10, depthshade=False)

    setup_3d_axis(ax2, lim=1.2)
    ax2.set_title(r'(b) 16-cell' + '\n' + r'$B_4$',
                  fontsize=11, fontweight='bold', pad=-2)
    ax2.text2D(0.50, 0.02, '8 vertices, 24 edges', transform=ax2.transAxes,
               fontsize=9, ha='center', color=C_GRAY)

    # ==============================================================
    # (c) 24-cell (24 vertices in 4D)
    # ==============================================================
    ax3 = fig.add_subplot(133, projection='3d')

    # 24-cell vertices: permutations of (+/-1, +/-1, 0, 0) in R^4
    cell24_4d = []
    for i in range(4):
        for j in range(i + 1, 4):
            for si in [1, -1]:
                for sj in [1, -1]:
                    v = np.zeros(4)
                    v[i] = si
                    v[j] = sj
                    cell24_4d.append(v)
    cell24_4d = np.array(cell24_4d)
    cell24_3d = proj_4d_to_3d(cell24_4d, w_factor=0.35)

    # Draw 24-cell edges (distance^2 = 2 in 4D)
    edge_count = 0
    for i in range(24):
        for j in range(i + 1, 24):
            dist_sq = np.sum((cell24_4d[i] - cell24_4d[j]) ** 2)
            if np.isclose(dist_sq, 2.0):
                ax3.plot([cell24_3d[i, 0], cell24_3d[j, 0]],
                         [cell24_3d[i, 1], cell24_3d[j, 1]],
                         [cell24_3d[i, 2], cell24_3d[j, 2]],
                         '-', color=C_ORANGE, lw=0.6, alpha=0.35)
                edge_count += 1

    # All 24-cell vertices (orange)
    ax3.scatter(cell24_3d[:, 0], cell24_3d[:, 1], cell24_3d[:, 2],
                color=C_ORANGE, s=50, edgecolors='black', linewidths=0.5,
                zorder=5, depthshade=False)

    # Highlight embedded 16-cell vertices within the 24-cell
    # The 16-cell is a subset: find 24-cell vertices closest to 16-cell positions
    # The 16-cell +/-e_i vertices appear as a subset of the 24-cell
    # In 24-cell coords, the 8 vertices with exactly one nonzero component ARE the 16-cell
    cell16_in_24_mask = np.array([np.count_nonzero(np.abs(v) > 0.5) == 1
                                  for v in cell24_4d])
    cell16_in_24_3d = cell24_3d[cell16_in_24_mask]

    # Wait - the 24-cell has vertices (+-1, +-1, 0, 0), none with just one nonzero.
    # The 16-cell vertices (+/-e_i) are NOT vertices of the 24-cell.
    # Instead, the 16-cell is DUAL to the 24-cell.
    # The correct relationship: 16-cell -> rectification -> 24-cell
    # Highlight the embedded T+/T- tetrahedra
    draw_tet_filled(ax3, t_plus_16, C_TP, C_TP, alpha=0.08, lw=0.8)
    draw_tet_filled(ax3, t_minus_16, C_TM, C_TM, alpha=0.08, lw=0.8)

    # Mark 16-cell vertices as diamonds (embedded in 24-cell space)
    ax3.scatter(cell16_3d[:4, 0], cell16_3d[:4, 1], cell16_3d[:4, 2],
                color=C_TP, s=70, marker='D', edgecolors='black',
                linewidths=0.8, zorder=10, depthshade=False)
    ax3.scatter(cell16_3d[4:, 0], cell16_3d[4:, 1], cell16_3d[4:, 2],
                color=C_TM, s=70, marker='D', edgecolors='black',
                linewidths=0.8, zorder=10, depthshade=False)

    setup_3d_axis(ax3, lim=1.5)
    ax3.set_title(r'(c) 24-cell' + '\n' + r'$F_4$, $D_4$ triality',
                  fontsize=11, fontweight='bold', pad=-2)
    ax3.text2D(0.50, 0.02, f'24 vertices, {edge_count} edges',
               transform=ax3.transAxes, fontsize=9, ha='center', color=C_GRAY)

    # ==============================================================
    # Connecting annotations between panels
    # ==============================================================
    # Use figure-level text for the arrows between panels
    fig.text(0.355, 0.52, r'shadow $\phi$', fontsize=10, ha='center',
             va='center', style='italic', color=(0.3, 0.3, 0.3),
             bbox=dict(facecolor='white', alpha=0.9, edgecolor='none'))
    fig.text(0.355, 0.46, r'$\longrightarrow$', fontsize=16, ha='center',
             va='center', color=(0.3, 0.3, 0.3))

    fig.text(0.665, 0.52, 'rectification', fontsize=10, ha='center',
             va='center', style='italic', color=(0.3, 0.3, 0.3),
             bbox=dict(facecolor='white', alpha=0.9, edgecolor='none'))
    fig.text(0.665, 0.46, r'$\longrightarrow$', fontsize=16, ha='center',
             va='center', color=(0.3, 0.3, 0.3))

    plt.subplots_adjust(wspace=0.05)

    # Save
    for ext in ['pdf', 'png']:
        path = os.path.join(OUTPUT_DIR, f'fig_polytope_embedding_chain.{ext}')
        fig.savefig(path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path}")
    plt.close('all')


if __name__ == '__main__':
    main()
