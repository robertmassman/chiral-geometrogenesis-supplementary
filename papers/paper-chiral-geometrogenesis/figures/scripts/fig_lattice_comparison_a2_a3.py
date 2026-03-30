#!/usr/bin/env python3
"""
Figure: Lattice Comparison A2 -> A3 (Section 6)

Three-panel visualization comparing root lattices and their physical realizations:
(a) A2 root lattice (2D hexagonal) — coordination 6
(b) A3/FCC lattice (3D) — coordination 12 (unique from SU(3))
(c) B3/Simple cubic (3D) — coordination 6 (rejected alternative)

Key physics:
- A2 is the 2D weight lattice of SU(3)
- A3 = FCC is the unique 3D lattice with SU(3) phase coherence
- B3 (simple cubic) lacks the required A2 sublattice structure
- FCC has coordination 12 = 2 * |roots of A3|

Proof Document: docs/proofs/Phase1/Theorem-1.1.1-Lattice-From-SU3.md
Paper Section: Section 6 (Lattice Structure)
Output: fig_lattice_comparison_a2_a3.pdf, fig_lattice_comparison_a2_a3.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Line3DCollection
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

# Colors
C_TP = (0.20, 0.60, 0.86)      # Blue
C_TM = (0.91, 0.30, 0.24)      # Red
C_GREEN = (0.15, 0.68, 0.15)   # Green
C_GOLD = (0.85, 0.65, 0.13)    # Gold
C_GRAY = (0.55, 0.55, 0.55)    # Gray
C_REJECT = (0.75, 0.20, 0.20)  # Dark red for rejected


def main():
    fig = plt.figure(figsize=(15, 5))

    # ==============================================================
    # (a) A2 Root Lattice (2D Hexagonal)
    # ==============================================================
    ax = fig.add_subplot(131)

    # A2 root vectors
    a1 = np.array([1, 0])
    a2 = np.array([0.5, np.sqrt(3) / 2])

    # Generate lattice points
    pts = []
    for i in range(-3, 4):
        for j in range(-3, 4):
            p = i * a1 + j * a2
            if np.linalg.norm(p) < 3.2:
                pts.append(p)
    pts = np.array(pts)

    # Draw all lattice points
    ax.scatter(pts[:, 0], pts[:, 1], c=C_GRAY, s=30, edgecolors='black',
               linewidths=0.5, zorder=5, alpha=0.6)

    # Central vertex (origin) highlighted
    ax.plot(0, 0, 'o', color=C_TP, markersize=12, markeredgecolor='black',
            markeredgewidth=1.5, zorder=10)

    # 6 nearest neighbors of the origin
    # A2 NN vectors: +/-a1, +/-a2, +/-(a1-a2)
    nn_vecs = [a1, -a1, a2, -a2, a1 - a2, -(a1 - a2)]
    for v in nn_vecs:
        ax.plot(v[0], v[1], 'o', color=C_GREEN, markersize=8,
                markeredgecolor='black', markeredgewidth=1.0, zorder=8)
        ax.plot([0, v[0]], [0, v[1]], '-', color=C_GREEN, lw=2.0,
                alpha=0.7, zorder=6)

    # Draw root vectors as arrows
    for v in nn_vecs[:3]:  # Only positive roots to avoid clutter
        ax.annotate('', xy=v * 0.95, xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=C_GOLD, lw=2.0,
                                    mutation_scale=12))

    # Draw full NN bonds (lighter) for context
    for i, p1 in enumerate(pts):
        for j, p2 in enumerate(pts):
            if j > i:
                d = np.linalg.norm(p1 - p2)
                if abs(d - 1.0) < 0.01:  # NN distance = 1
                    ax.plot([p1[0], p2[0]], [p1[1], p2[1]], '-',
                            color=C_GRAY, lw=0.4, alpha=0.3, zorder=1)

    ax.set_aspect('equal')
    ax.set_xlim(-2.5, 2.5)
    ax.set_ylim(-2.5, 2.5)
    ax.set_xlabel(r'$x$')
    ax.set_ylabel(r'$y$')
    ax.set_title(r'(a) $A_2$ Root Lattice (2D)', fontsize=11,
                 fontweight='bold')
    ax.text(0.98, 0.02, 'Coordination 6', transform=ax.transAxes,
            fontsize=10, ha='right', va='bottom',
            bbox=dict(facecolor='white', alpha=0.8, edgecolor=C_GREEN,
                      boxstyle='round,pad=0.3'))

    # ==============================================================
    # (b) A3 / FCC Lattice (3D)
    # ==============================================================
    ax = fig.add_subplot(132, projection='3d')

    # FCC nearest-neighbor vectors: 12 permutations of (+/-1, +/-1, 0)/sqrt(2)
    fcc_nn = []
    for i in range(3):
        for s1 in [1, -1]:
            for s2 in [1, -1]:
                v = np.zeros(3)
                j = (i + 1) % 3
                k = (i + 2) % 3
                v[j] = s1
                v[k] = s2
                fcc_nn.append(v / np.sqrt(2))
    fcc_nn = np.array(fcc_nn)

    # Central vertex
    ax.scatter(0, 0, 0, c=C_TP, s=150, edgecolors='black', linewidths=1.5,
               zorder=10, depthshade=False)

    # 12 nearest neighbors with bonds
    for v in fcc_nn:
        ax.scatter(*v, c=C_GREEN, s=60, edgecolors='black', linewidths=0.8,
                   zorder=8, depthshade=False)
        ax.plot([0, v[0]], [0, v[1]], [0, v[2]], '-', color=C_GREEN,
                lw=1.8, alpha=0.6)

    # Highlight one A2 plane (the {111} plane through origin)
    # Choose the plane with normal [1,1,1]: pick NNs in that plane
    # NNs in the z=0 plane: those with v[2] = 0 are not in FCC NNs
    # Instead, highlight NNs forming hexagonal ring
    # In the (1,1,0)/sqrt(2) family, one hexagonal ring:
    hex_ring = [v for v in fcc_nn
                if abs(v[0] + v[1] + v[2]) < 0.01]  # sum = 0 plane
    # This selects NNs perpendicular to [111]
    # Actually the {111} planes contain 6 NNs each
    # Let's highlight the NNs in one {001} plane (z-component = 0)
    z0_ring = [v for v in fcc_nn if abs(v[2]) < 0.01]
    for v in z0_ring:
        ax.scatter(*v, c=C_GOLD, s=80, edgecolors='black', linewidths=1.0,
                   zorder=9, depthshade=False)

    # Draw edges between neighbors in the z=0 ring to show hexagonal motif
    z0_ring = np.array(z0_ring)
    if len(z0_ring) > 0:
        # Sort by angle
        angles = np.arctan2(z0_ring[:, 1], z0_ring[:, 0])
        order = np.argsort(angles)
        z0_sorted = z0_ring[order]
        for i_v in range(len(z0_sorted)):
            j_v = (i_v + 1) % len(z0_sorted)
            p1, p2 = z0_sorted[i_v], z0_sorted[j_v]
            if np.linalg.norm(p1 - p2) < 1.1:
                ax.plot([p1[0], p2[0]], [p1[1], p2[1]], [p1[2], p2[2]],
                        '-', color=C_GOLD, lw=1.5, alpha=0.6)

    lim = 0.95
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.view_init(elev=20, azim=35)
    ax.set_xlabel('x', fontsize=8, labelpad=-5)
    ax.set_ylabel('y', fontsize=8, labelpad=-5)
    ax.set_zlabel('z', fontsize=8, labelpad=-5)
    ax.tick_params(labelsize=6)
    ax.set_title(r'(b) $A_3$/FCC Lattice (3D)', fontsize=11,
                 fontweight='bold', pad=5)

    # Add coordination label as 3D text
    ax.text2D(0.95, 0.02, 'Coordination 12', transform=ax.transAxes,
              fontsize=10, ha='right', va='bottom',
              bbox=dict(facecolor='white', alpha=0.8, edgecolor=C_GREEN,
                        boxstyle='round,pad=0.3'))

    # ==============================================================
    # (c) B3 / Simple Cubic Lattice (3D) — Rejected
    # ==============================================================
    ax = fig.add_subplot(133, projection='3d')

    # Simple cubic NN vectors: 6 permutations of (+/-1, 0, 0)
    cubic_nn = []
    for i in range(3):
        for s in [1, -1]:
            v = np.zeros(3)
            v[i] = s
            cubic_nn.append(v)
    cubic_nn = np.array(cubic_nn)

    # Central vertex
    ax.scatter(0, 0, 0, c=C_GRAY, s=150, edgecolors='black', linewidths=1.5,
               zorder=10, depthshade=False)

    # 6 nearest neighbors with bonds
    for v in cubic_nn:
        ax.scatter(*v, c=C_REJECT, s=60, edgecolors='black', linewidths=0.8,
                   zorder=8, depthshade=False, alpha=0.6)
        ax.plot([0, v[0]], [0, v[1]], [0, v[2]], '-', color=C_REJECT,
                lw=1.8, alpha=0.5)

    # Draw cube wireframe (single unit cell)
    cube_verts = np.array([
        [1, 1, 1], [1, 1, -1], [1, -1, 1], [1, -1, -1],
        [-1, 1, 1], [-1, 1, -1], [-1, -1, 1], [-1, -1, -1]
    ], dtype=float)
    cube_edges = [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),
                  (3,7),(4,5),(4,6),(5,7),(6,7)]
    lines = [[cube_verts[i], cube_verts[j]] for i, j in cube_edges]
    lc = Line3DCollection(lines, colors=[(0.7, 0.7, 0.7, 0.25)] * len(lines),
                          linewidths=0.6)
    ax.add_collection3d(lc)

    lim = 1.3
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.view_init(elev=20, azim=35)
    ax.set_xlabel('x', fontsize=8, labelpad=-5)
    ax.set_ylabel('y', fontsize=8, labelpad=-5)
    ax.set_zlabel('z', fontsize=8, labelpad=-5)
    ax.tick_params(labelsize=6)
    ax.set_title(r'(c) $B_3$ Lattice (3D) $-$ Rejected', fontsize=11,
                 fontweight='bold', color=C_REJECT, pad=5)

    # Rejection marker
    ax.text2D(0.95, 0.02, 'Coordination 6', transform=ax.transAxes,
              fontsize=10, ha='right', va='bottom',
              bbox=dict(facecolor='white', alpha=0.8, edgecolor=C_REJECT,
                        boxstyle='round,pad=0.3'))

    plt.tight_layout()

    # Save
    for ext in ['pdf', 'png']:
        path = os.path.join(OUTPUT_DIR, f'fig_lattice_comparison_a2_a3.{ext}')
        fig.savefig(path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path}")
    plt.close('all')


if __name__ == '__main__':
    main()
