#!/usr/bin/env python3
"""
Figure 4: Polytope Embedding Chain (Theorem 0.0.4)

Generates publication-quality figure showing the GUT embedding chain:
Stella Octangula -> 16-cell (B4) -> 24-cell (D4) -> so(10) (D5) -> SU(5) -> SM

Layout: 4 panels on top (stella, 16-cell, 24-cell, D5), horizontal GUT chain on bottom.

Lean 4 Reference: Theorem_0_0_4.lean - embedding_chain_to_SU5
Proof Document: docs/proofs/foundations/Theorem-0.0.4-GUT-Embedding.md

Output: fig_thm_3_1_2_polytope_chain.pdf, fig_thm_3_1_2_polytope_chain.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
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


def draw_tetrahedron_filled(ax, vertices, facecolor, edgecolor, alpha=0.35, lw=1.5):
    """Draw tetrahedron with filled translucent faces."""
    faces = [
        [vertices[0], vertices[1], vertices[2]],
        [vertices[0], vertices[1], vertices[3]],
        [vertices[0], vertices[2], vertices[3]],
        [vertices[1], vertices[2], vertices[3]]
    ]
    ax.add_collection3d(Poly3DCollection(faces, alpha=alpha,
                                          facecolor=facecolor, edgecolor=edgecolor, lw=lw))


def style_3d_axis_clean(ax, lim=1.0):
    """Style 3D axes with clean look."""
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_xlabel('X', fontsize=8)
    ax.set_ylabel('Y', fontsize=8)
    ax.set_zlabel('Z', fontsize=8)
    ax.tick_params(labelsize=6)
    # Clean white panes
    ax.xaxis.pane.set_facecolor('white')
    ax.yaxis.pane.set_facecolor('white')
    ax.zaxis.pane.set_facecolor('white')
    ax.xaxis.pane.set_edgecolor('lightgray')
    ax.yaxis.pane.set_edgecolor('lightgray')
    ax.zaxis.pane.set_edgecolor('lightgray')
    ax.grid(True, alpha=0.2, color='lightgray')
    ax.set_box_aspect([1, 1, 1])


def proj_4d_to_3d(pts):
    """Project 4D points to 3D."""
    w_factor = 0.5
    x = pts[:,0] + w_factor * pts[:,3]
    y = pts[:,1] + w_factor * pts[:,3]
    z = pts[:,2] + w_factor * pts[:,3]
    return np.column_stack([x, y, z])


def proj_5d_to_3d(pts):
    """Project 5D points to 3D."""
    w_factor = 0.4
    v_factor = 0.3
    x = pts[:,0] + w_factor * pts[:,3] + v_factor * pts[:,4]
    y = pts[:,1] + w_factor * pts[:,3] - v_factor * pts[:,4]
    z = pts[:,2] - w_factor * pts[:,3] + v_factor * pts[:,4]
    return np.column_stack([x, y, z])


def create_figure_4():
    """
    Generate GEOMETRIC visualization of the polytope embedding chain for GUT structure.

    From Lean 4:
    - S4xZ2_to_WB4_injective: S4 x Z2 embeds in W(B4)
    - D4_to_D5_injective: D4 embeds in D5 = so(10)
    """
    fig = plt.figure(figsize=(16, 7))

    # ============ Panel (a): Stella Octangula with filled faces ============
    ax1 = fig.add_subplot(241, projection='3d')

    # Stella octangula vertices: two interpenetrating tetrahedra
    t_plus = np.array([
        [1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]
    ], dtype=float)
    t_minus = -t_plus

    # Draw T+ tetrahedron (blue) with filled faces
    draw_tetrahedron_filled(ax1, t_plus, '#3498db', '#2980b9', alpha=0.35)

    # Draw T- tetrahedron (red) with filled faces
    draw_tetrahedron_filled(ax1, t_minus, '#e74c3c', '#c0392b', alpha=0.35)

    # Draw vertices
    ax1.scatter(t_plus[:, 0], t_plus[:, 1], t_plus[:, 2],
                c='#3498db', s=80, marker='o', edgecolors='black', linewidths=1, zorder=10)
    ax1.scatter(t_minus[:, 0], t_minus[:, 1], t_minus[:, 2],
                c='#e74c3c', s=80, marker='o', edgecolors='black', linewidths=1, zorder=10)

    style_3d_axis_clean(ax1, lim=1.5)
    ax1.set_title('(a) Stella Octangula\n$T_+$ (blue) $\\cup$ $T_-$ (red)', fontsize=10, fontweight='bold')
    ax1.view_init(elev=25, azim=45)

    # ============ Panel (b): 16-cell with filled faces ============
    ax2 = fig.add_subplot(242, projection='3d')

    # 16-cell vertices in R^4: +/-e_i for i=1,2,3,4
    cell16_4d = np.array([
        [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1],
        [-1,0,0,0], [0,-1,0,0], [0,0,-1,0], [0,0,0,-1]
    ], dtype=float)

    cell16_3d = proj_4d_to_3d(cell16_4d)

    # T+ tetrahedron: vertices 0,1,2,3 (the +e_i vertices)
    t_plus_16 = cell16_3d[:4]
    draw_tetrahedron_filled(ax2, t_plus_16, '#3498db', '#2980b9', alpha=0.25)

    # T- tetrahedron: vertices 4,5,6,7 (the -e_i vertices)
    t_minus_16 = cell16_3d[4:]
    draw_tetrahedron_filled(ax2, t_minus_16, '#e74c3c', '#c0392b', alpha=0.25)

    # Draw cross edges (connecting +e to -e) in purple
    plus_indices = {0, 1, 2, 3}
    minus_indices = {4, 5, 6, 7}
    for i in range(8):
        for j in range(i+1, 8):
            dist_sq = np.sum((cell16_4d[i] - cell16_4d[j])**2)
            if np.isclose(dist_sq, 2.0):
                if (i in plus_indices and j in minus_indices) or (i in minus_indices and j in plus_indices):
                    ax2.plot3D([cell16_3d[i,0], cell16_3d[j,0]],
                              [cell16_3d[i,1], cell16_3d[j,1]],
                              [cell16_3d[i,2], cell16_3d[j,2]],
                              color='#9b59b6', lw=1.0, alpha=0.6)

    # Draw vertices
    ax2.scatter(cell16_3d[:4, 0], cell16_3d[:4, 1], cell16_3d[:4, 2],
                c='#3498db', s=100, marker='o', edgecolors='black', linewidths=1, zorder=10)
    ax2.scatter(cell16_3d[4:, 0], cell16_3d[4:, 1], cell16_3d[4:, 2],
                c='#e74c3c', s=100, marker='o', edgecolors='black', linewidths=1, zorder=10)

    style_3d_axis_clean(ax2, lim=1.0)
    ax2.set_title('(b) 16-cell ($B_4$)\n$\\phi: T_\\pm \\to \\pm e_i$', fontsize=10, fontweight='bold')
    ax2.view_init(elev=25, azim=45)

    # ============ Panel (c): 24-cell (D4 roots) ============
    ax3 = fig.add_subplot(243, projection='3d')

    # 24-cell vertices = D4 roots: +/-e_i +/- e_j for i < j (24 vertices)
    cell24_4d = []
    for i in range(4):
        for j in range(i+1, 4):
            for si in [1, -1]:
                for sj in [1, -1]:
                    v = np.zeros(4)
                    v[i] = si
                    v[j] = sj
                    cell24_4d.append(v)
    cell24_4d = np.array(cell24_4d)
    cell24_3d = proj_4d_to_3d(cell24_4d)

    # Draw 24-cell edges
    for i in range(24):
        for j in range(i+1, 24):
            dist_sq = np.sum((cell24_4d[i] - cell24_4d[j])**2)
            if np.isclose(dist_sq, 2.0):
                ax3.plot3D([cell24_3d[i,0], cell24_3d[j,0]],
                          [cell24_3d[i,1], cell24_3d[j,1]],
                          [cell24_3d[i,2], cell24_3d[j,2]],
                          color='#e67e22', lw=1.0, alpha=0.5)

    # Draw 24-cell vertices (orange)
    ax3.scatter(cell24_3d[:,0], cell24_3d[:,1], cell24_3d[:,2],
                c='#e67e22', s=60, edgecolors='black', linewidths=0.5, zorder=5)

    # Highlight embedded 16-cell vertices (show stella embedding)
    draw_tetrahedron_filled(ax3, t_plus_16, '#3498db', '#2980b9', alpha=0.15)
    draw_tetrahedron_filled(ax3, t_minus_16, '#e74c3c', '#c0392b', alpha=0.15)
    ax3.scatter(cell16_3d[:4, 0], cell16_3d[:4, 1], cell16_3d[:4, 2],
                c='#3498db', s=80, marker='D', edgecolors='black', linewidths=1, zorder=10)
    ax3.scatter(cell16_3d[4:, 0], cell16_3d[4:, 1], cell16_3d[4:, 2],
                c='#e74c3c', s=80, marker='D', edgecolors='black', linewidths=1, zorder=10)

    style_3d_axis_clean(ax3, lim=1.3)
    ax3.set_title('(c) 24-cell ($D_4$)\n$16\\text{-cell} \\subset D_4$ roots', fontsize=10, fontweight='bold')
    ax3.view_init(elev=25, azim=45)

    # ============ Panel (d): D5 root system (so(10)) ============
    ax4 = fig.add_subplot(244, projection='3d')

    # Generate D5 roots: +/-e_i +/- e_j for i < j in R^5 (40 roots total)
    d5_roots_5d = []
    for i in range(5):
        for j in range(i+1, 5):
            for si in [1, -1]:
                for sj in [1, -1]:
                    v = np.zeros(5)
                    v[i] = si
                    v[j] = sj
                    d5_roots_5d.append(v)
    d5_roots_5d = np.array(d5_roots_5d)
    d5_roots_3d = proj_5d_to_3d(d5_roots_5d)

    # Draw D5 edges
    for i in range(40):
        for j in range(i+1, 40):
            dist_sq = np.sum((d5_roots_5d[i] - d5_roots_5d[j])**2)
            if np.isclose(dist_sq, 2.0):
                ax4.plot3D([d5_roots_3d[i,0], d5_roots_3d[j,0]],
                          [d5_roots_3d[i,1], d5_roots_3d[j,1]],
                          [d5_roots_3d[i,2], d5_roots_3d[j,2]],
                          color='#27ae60', lw=0.6, alpha=0.3)

    # Draw D5 vertices (green)
    ax4.scatter(d5_roots_3d[:,0], d5_roots_3d[:,1], d5_roots_3d[:,2],
                c='#27ae60', s=40, edgecolors='#1e8449', linewidths=0.3, zorder=5)

    # Highlight D4 subset (where 5th component = 0)
    d4_indices = [idx for idx, v in enumerate(d5_roots_5d) if np.isclose(v[4], 0)]
    d4_3d_in_d5 = d5_roots_3d[d4_indices]

    # Highlight D4 subset with orange
    ax4.scatter(d4_3d_in_d5[:,0], d4_3d_in_d5[:,1], d4_3d_in_d5[:,2],
                c='#e67e22', s=70, edgecolors='black', linewidths=0.5, zorder=10)

    style_3d_axis_clean(ax4, lim=1.6)
    ax4.set_title('(d) $\\mathfrak{so}(10)$ ($D_5$)\n$D_4 \\subset D_5$ (40 roots)', fontsize=10, fontweight='bold')
    ax4.view_init(elev=25, azim=45)

    # ============ Panel (e): Horizontal GUT chain across bottom ============
    ax5 = fig.add_subplot(212)
    ax5.axis('off')

    # Draw the embedding chain horizontally with cleaner style
    x_positions = [0.06, 0.21, 0.36, 0.51, 0.68, 0.88]
    labels = [
        ('Stella\n$S_4 \\times \\mathbb{Z}_2$', '#3498db'),
        ('16-cell\n$B_4$', '#9b59b6'),
        ('24-cell\n$D_4$', '#e67e22'),
        ('$\\mathfrak{so}(10)$\n$D_5$', '#27ae60'),
        ('$SU(5)$', '#16a085'),
        ('$SU(3) \\times SU(2) \\times U(1)$', '#e74c3c'),
    ]

    # Draw boxes with cleaner styling
    for i, (name, color) in enumerate(labels):
        ax5.text(x_positions[i], 0.5, name, ha='center', va='center',
                fontsize=9, fontweight='bold', color='black',
                bbox=dict(boxstyle='round,pad=0.3', facecolor=color, alpha=0.2,
                         edgecolor=color, lw=2))

    # Draw arrows between boxes
    arrow_labels = ['$\\subset$', '$\\subset$', '$\\subset$', '$\\supset$', 'break']
    for i in range(len(x_positions) - 1):
        ax5.annotate('', xy=(x_positions[i+1] - 0.055, 0.5), xytext=(x_positions[i] + 0.055, 0.5),
                    arrowprops=dict(arrowstyle='->', color='#333333', lw=1.5))
        ax5.text((x_positions[i] + x_positions[i+1])/2, 0.72, arrow_labels[i],
                ha='center', va='center', fontsize=9, color='#333333')

    # Add title and Weinberg angle with cleaner styling
    ax5.text(0.5, 0.95, '(e) GUT Embedding Chain', ha='center', fontsize=11, fontweight='bold')
    ax5.text(0.5, 0.15, '$\\sin^2\\theta_W = 3/8$ at GUT scale',
            ha='center', fontsize=10, style='italic',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='#fffacd', alpha=0.9,
                     edgecolor='#e67e22', lw=1.5))

    ax5.set_xlim(0, 1)
    ax5.set_ylim(0, 1)

    plt.tight_layout()
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_3_1_2_polytope_chain.pdf')
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_3_1_2_polytope_chain.png')
    plt.close()
    print(f"✓ Figure 4 saved to {OUTPUT_DIR}/fig_thm_3_1_2_polytope_chain.pdf")
    print(f"✓ Figure 4 saved to {OUTPUT_DIR}/fig_thm_3_1_2_polytope_chain.png")


if __name__ == '__main__':
    create_figure_4()
