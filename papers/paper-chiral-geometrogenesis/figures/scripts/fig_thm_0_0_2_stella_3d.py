#!/usr/bin/env python3
"""
Figure: 3D Stella Octangula (Theorems 0.0.2 and 0.0.3)

Single-panel 3D visualization showing:
- Two interpenetrating tetrahedra (T+ fundamental, T- anti-fundamental)
- 8-vertex structure: 4 color vertices (R, G, B, W) on T+, 4 anti-color on T-
- Bounding cube wireframe
- Singlet axis along [1,1,1] direction (gold arrow)

Note: Chirality arrows are NOT included here; they are introduced later
in Theorem 0.0.5 (Chirality Selection from Geometry).

Proof Document: docs/proofs/foundations/Theorem-0.0.2-Euclidean-From-SU3.md
Paper Section: Section 3 (Theorem 0.0.2)
Output: fig_thm_0_0_2_stella_3d.pdf, fig_thm_0_0_2_stella_3d.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
import os

# Paths
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style (matching fig_vertex_face_duality.py)
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
CC = {
    'R': (0.91, 0.15, 0.15),
    'G': (0.15, 0.68, 0.15),
    'B': (0.20, 0.40, 0.86),
    'W': (0.55, 0.55, 0.55),
}
# Anti-colors (darker versions)
CC_ANTI = {
    'aR': (0.75, 0.22, 0.17),
    'aG': (0.12, 0.52, 0.29),
    'aB': (0.16, 0.33, 0.65),
    'aW': (0.40, 0.40, 0.40),
}

C_TP = (0.20, 0.60, 0.86)
C_TM = (0.91, 0.30, 0.24)
C_GOLD = (0.85, 0.65, 0.13)

ELEV, AZIM = 28, 39

# Geometry
s3 = np.sqrt(3)

TP = {
    'R': np.array([ 1, -1, -1]) / s3,
    'G': np.array([-1,  1, -1]) / s3,
    'B': np.array([-1, -1,  1]) / s3,
    'W': np.array([ 1,  1,  1]) / s3,
}

TM = {
    'aR': np.array([-1,  1,  1]) / s3,
    'aG': np.array([ 1, -1,  1]) / s3,
    'aB': np.array([ 1,  1, -1]) / s3,
    'aW': np.array([-1, -1, -1]) / s3,
}

COLOR_KEYS = ['R', 'G', 'B', 'W']
ANTI_KEYS = ['aR', 'aG', 'aB', 'aW']
TET_FACE_IDX = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]

CUBE_HALF = 1.0 / s3
AXIS_111 = np.array([1, 1, 1]) / s3


def draw_cube_wire(ax, half, color=(0.5, 0.5, 0.5), alpha=0.15, lw=0.6):
    """Draw bounding cube wireframe."""
    h = half
    c = np.array([
        [-h, -h, -h], [ h, -h, -h], [ h,  h, -h], [-h,  h, -h],
        [-h, -h,  h], [ h, -h,  h], [ h,  h,  h], [-h,  h,  h],
    ])
    edges = [(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),
             (0,4),(1,5),(2,6),(3,7)]
    lines = [[c[i], c[j]] for i, j in edges]
    lc = Line3DCollection(lines, colors=[(*color, alpha)] * len(lines),
                          linewidths=lw)
    ax.add_collection3d(lc)


def main():
    fig = plt.figure(figsize=(8, 7))
    ax = fig.add_subplot(111, projection='3d')

    # T+ tetrahedron (blue, semi-transparent with black edges)
    tp_arr = np.array([TP[c] for c in COLOR_KEYS])
    faces_tp = [tp_arr[list(f)] for f in TET_FACE_IDX]
    poly_tp = Poly3DCollection(faces_tp, alpha=0.10, facecolor=C_TP,
                               edgecolor='black', linewidth=1.8)
    ax.add_collection3d(poly_tp)

    # T- tetrahedron (red, fainter with dashed-style edges)
    tm_arr = np.array([TM[k] for k in ANTI_KEYS])
    faces_tm = [tm_arr[list(f)] for f in TET_FACE_IDX]
    poly_tm = Poly3DCollection(faces_tm, alpha=0.06, facecolor=C_TM,
                               edgecolor=(*C_TM, 0.5), linewidth=1.2)
    ax.add_collection3d(poly_tm)

    # Bounding cube wireframe
    draw_cube_wire(ax, CUBE_HALF)

    # Singlet axis: gold arrow along [111] from W-bar to W
    axis_len = 0.85
    ax.quiver(-AXIS_111[0] * axis_len, -AXIS_111[1] * axis_len,
              -AXIS_111[2] * axis_len,
              2 * AXIS_111[0] * axis_len, 2 * AXIS_111[1] * axis_len,
              2 * AXIS_111[2] * axis_len,
              color=C_GOLD, arrow_length_ratio=0.06, linewidth=3.0,
              alpha=0.8, zorder=15)

    # T+ colored vertex dots (circles)
    for c_name in COLOR_KEYS:
        pos = TP[c_name]
        marker = '*' if c_name == 'W' else 'o'
        size = 300 if c_name == 'W' else 280
        ax.scatter(*pos, color=CC[c_name], s=size, marker=marker,
                   edgecolors='black', linewidths=1.5, zorder=10,
                   depthshade=False)

    # T- anti-color vertex dots (squares)
    for a_name in ANTI_KEYS:
        pos = TM[a_name]
        marker = '*' if a_name == 'aW' else 's'
        size = 300 if a_name == 'aW' else 200
        ax.scatter(*pos, color=CC_ANTI[a_name], s=size, marker=marker,
                   edgecolors='black', linewidths=1.2, zorder=10,
                   depthshade=False)

    # Vertex labels — T+ (fundamental)
    # W gets a custom offset perpendicular to [111] so it's not behind the star
    for c_name in COLOR_KEYS:
        pos = TP[c_name]
        if c_name == 'W':
            off = np.array([-0.14, 0.0, 0.08])  # offset to the left of the star
        else:
            direction = pos / np.linalg.norm(pos)
            off = direction * 0.20
        lbl_color = (0.35, 0.35, 0.35) if c_name == 'W' else CC[c_name]
        ax.text(pos[0] + off[0], pos[1] + off[1], pos[2] + off[2],
                f'$v_{{{c_name}}}$', fontsize=12, fontweight='bold',
                color=lbl_color, ha='center', va='center', zorder=11)

    # Vertex labels — T- (anti-fundamental)
    # W-bar gets a custom offset perpendicular to [111]
    label_map = {'aR': r'$\bar{v}_R$', 'aG': r'$\bar{v}_G$',
                 'aB': r'$\bar{v}_B$', 'aW': r'$\bar{v}_W$'}
    for a_name in ANTI_KEYS:
        pos = TM[a_name]
        if a_name == 'aW':
            off = np.array([0.14, 0.0, -0.08])  # offset to the right of the star
        else:
            direction = pos / np.linalg.norm(pos)
            off = direction * 0.20
        lbl_color = (0.30, 0.30, 0.30) if a_name == 'aW' else CC_ANTI[a_name]
        ax.text(pos[0] + off[0], pos[1] + off[1], pos[2] + off[2],
                label_map[a_name], fontsize=10,
                color=lbl_color, ha='center', va='center', zorder=11)

    # Center marker
    ax.scatter(0, 0, 0, color='black', s=30, zorder=9, depthshade=False)

    # Legend (using dummy entries)
    ax.plot([], [], '-', color=C_TP, linewidth=2.5,
            label=r'$T_+$: $\mathbf{3}$ (fundamental)')
    ax.plot([], [], '-', color=C_TM, linewidth=2.0, alpha=0.6,
            label=r'$T_-$: $\bar{\mathbf{3}}$ (anti-fundamental)')
    ax.plot([], [], '-', color=C_GOLD, linewidth=3.0,
            label=r'Singlet axis $[111]$')
    ax.legend(loc='upper left', fontsize=9, framealpha=0.9)

    # Clean axis setup
    lim = 0.78
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.view_init(elev=ELEV, azim=AZIM)
    ax.set_axis_off()

    ax.set_title(r'Stella Octangula: $T_+ \cup T_-$',
                 fontsize=13, fontweight='bold', pad=-5)

    # Save
    for ext in ['pdf', 'png']:
        path = os.path.join(OUTPUT_DIR, f'fig_thm_0_0_2_stella_3d.{ext}')
        fig.savefig(path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path}")
    plt.close('all')


if __name__ == '__main__':
    main()
