#!/usr/bin/env python3
"""
Figure: Vertex-Face Duality on the Stella Octangula

Two-panel visualization showing complementary color representations:
(a) Vertex coloring: each T+ vertex labeled by its source color
(b) Face coloring: each T+ face labeled by its depression color

Key physics:
- Vertex coloring displays pressure sources (color charge eigenstates)
- Face coloring displays depression zones (pressure minima)
- Related by inversion v_c -> -v_c/3 through the stella center
- Vertex coloring = standard SU(3) weight diagram
- Face coloring = pressure-depression geometry (Paper 2)

Proof Document: docs/proofs/Phase0/Definition-0.1.4-Color-Field-Domains.md
Paper Section: Paper 1, Remark (Vertex-Face Duality), after Definition 0.1.4

Output: fig_vertex_face_duality.pdf, fig_vertex_face_duality.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
import matplotlib.gridspec as gridspec
import os

# Paths
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style (matching fig_stella_to_fcc_panels.py)
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

# ============================================================
# GEOMETRY
# ============================================================

s3 = np.sqrt(3)

# T+ vertices (paper convention: Remark vertex-face-duality, Paper 1)
TP = {
    'R': np.array([ 1, -1, -1]) / s3,
    'G': np.array([-1,  1, -1]) / s3,
    'B': np.array([-1, -1,  1]) / s3,
    'W': np.array([ 1,  1,  1]) / s3,
}

# T- vertices (dual tetrahedron)
TM = {
    'aR': np.array([-1,  1,  1]) / s3,
    'aG': np.array([ 1, -1,  1]) / s3,
    'aB': np.array([ 1,  1, -1]) / s3,
    'aW': np.array([-1, -1, -1]) / s3,
}

# Face centers = depression zone centers = -v_c/3
FC = {c: -TP[c] / 3 for c in TP}

# T+ faces: face opposite vertex 'c' = triangle of the other 3 vertices
COLOR_KEYS = ['R', 'G', 'B', 'W']
TP_FACES = {}
for c in COLOR_KEYS:
    others = [k for k in COLOR_KEYS if k != c]
    TP_FACES[c] = np.array([TP[o] for o in others])

# T- faces (for background rendering)
TM_KEYS = list(TM.keys())
TM_FACE_LIST = []
for i in range(4):
    others = [TM_KEYS[j] for j in range(4) if j != i]
    TM_FACE_LIST.append(np.array([TM[o] for o in others]))

# Bounding cube half-edge
CUBE_HALF = 1.0 / s3

# Tetrahedron face/edge indexing (for 4-vertex tet)
TET_FACE_IDX = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]

# ============================================================
# COLORS (no purple per figures/CLAUDE.md)
# ============================================================

CC = {
    'R': (0.91, 0.15, 0.15),   # Red
    'G': (0.15, 0.68, 0.15),   # Green
    'B': (0.20, 0.40, 0.86),   # Blue
    'W': (0.55, 0.55, 0.55),   # Gray (singlet)
}

C_TP = (0.20, 0.60, 0.86)    # T+ wireframe blue
C_TM = (0.91, 0.30, 0.24)    # T- wireframe red
C_CUBE = (0.5, 0.5, 0.5)     # Cube wireframe gray

ELEV, AZIM = 28, 39


# ============================================================
# DRAWING HELPERS
# ============================================================

def draw_tet_faces(ax, verts_4, facecolor, edgecolor, alpha=0.3, lw=1.5):
    """Draw a tetrahedron given 4 vertices."""
    v = np.array(verts_4)
    faces = [v[list(f)] for f in TET_FACE_IDX]
    poly = Poly3DCollection(faces, alpha=alpha, facecolor=facecolor,
                            edgecolor=edgecolor, linewidth=lw)
    ax.add_collection3d(poly)


def draw_cube_wire(ax, half, color=C_CUBE, alpha=0.15, lw=0.6):
    """Draw bounding cube wireframe."""
    h = half
    c = np.array([
        [-h, -h, -h], [ h, -h, -h], [ h,  h, -h], [-h,  h, -h],
        [-h, -h,  h], [ h, -h,  h], [ h,  h,  h], [-h,  h,  h],
    ])
    edges = [(0, 1), (1, 2), (2, 3), (3, 0),
             (4, 5), (5, 6), (6, 7), (7, 4),
             (0, 4), (1, 5), (2, 6), (3, 7)]
    lines = [[c[i], c[j]] for i, j in edges]
    lc = Line3DCollection(lines, colors=[(*color, alpha)] * len(lines),
                          linewidths=lw)
    ax.add_collection3d(lc)


def setup_ax(ax, title=''):
    """Configure 3D axis matching fig_stella_to_fcc_panels.py style."""
    lim = 0.78
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.view_init(elev=ELEV, azim=AZIM)
    ax.set_axis_off()
    if title:
        ax.set_title(title, fontsize=11, fontweight='bold', pad=-5)


# ============================================================
# MAIN
# ============================================================

def main():
    fig = plt.figure(figsize=(12, 5.5))
    gs = gridspec.GridSpec(1, 2, wspace=0.02)

    # ================================================================
    # (a) Vertex Coloring — Pressure Sources
    # ================================================================
    ax = fig.add_subplot(gs[0, 0], projection='3d')

    # T+ transparent with black edges (geometry scaffold)
    tp_arr = np.array([TP[c] for c in COLOR_KEYS])
    faces_tp = [tp_arr[list(f)] for f in TET_FACE_IDX]
    poly = Poly3DCollection(faces_tp, alpha=0.06, facecolor=C_TP,
                            edgecolor='black', linewidth=1.8)
    ax.add_collection3d(poly)

    # T- faint wireframe
    tm_arr = np.array(list(TM.values()))
    faces_tm = [tm_arr[list(f)] for f in TET_FACE_IDX]
    poly_tm = Poly3DCollection(faces_tm, alpha=0.04, facecolor=C_TM,
                               edgecolor=(*C_TM, 0.25), linewidth=0.8)
    ax.add_collection3d(poly_tm)

    # Cube wireframe
    draw_cube_wire(ax, CUBE_HALF)

    # Colored vertex dots (main visual element)
    for c_name in COLOR_KEYS:
        pos = TP[c_name]
        ax.scatter(*pos, c=[CC[c_name]], s=280, edgecolors='black',
                   linewidths=1.5, zorder=10, depthshade=False)

    # Vertex labels (offset radially outward)
    for c_name in COLOR_KEYS:
        pos = TP[c_name]
        direction = pos / np.linalg.norm(pos)
        off = direction * 0.20
        # Use darker gray for W so it's readable against white background
        lbl_color = (0.35, 0.35, 0.35) if c_name == 'W' else CC[c_name]
        ax.text(pos[0] + off[0], pos[1] + off[1], pos[2] + off[2],
                f'$v_{{{c_name}}}$', fontsize=12, fontweight='bold',
                color=lbl_color, ha='center', va='center', zorder=11)

    # Center marker
    ax.scatter(0, 0, 0, c='black', s=30, zorder=9, depthshade=False)

    setup_ax(ax, r'(a) Vertex Coloring $-$ Pressure Sources')

    # ================================================================
    # (b) Face Coloring — Depression Zones
    # ================================================================
    ax = fig.add_subplot(gs[0, 1], projection='3d')

    # T+ with individually colored faces (one color per face)
    # Face opposite c is colored with color c (depression color)
    colored_faces = [TP_FACES[c] for c in COLOR_KEYS]
    face_colors = [CC[c] for c in COLOR_KEYS]
    poly = Poly3DCollection(colored_faces, alpha=0.40,
                            facecolor=face_colors,
                            edgecolor='black', linewidth=1.8)
    ax.add_collection3d(poly)

    # T- faint wireframe
    poly_tm = Poly3DCollection(TM_FACE_LIST, alpha=0.04, facecolor=C_TM,
                               edgecolor=(*C_TM, 0.25), linewidth=0.8)
    ax.add_collection3d(poly_tm)

    # Cube wireframe
    draw_cube_wire(ax, CUBE_HALF)

    # Dashed lines: vertex -> face center (inversion v_c -> -v_c/3)
    # Only show for R, G, B (face opposite W is hidden from this angle)
    for c_name in ['R', 'G', 'B']:
        v = TP[c_name]
        f = FC[c_name]
        ax.plot([v[0], f[0]], [v[1], f[1]], [v[2], f[2]],
                '--', color=CC[c_name], alpha=0.6, lw=1.8, zorder=5)
        # Small dot at vertex (mapping origin)
        ax.scatter(*v, c=[CC[c_name]], s=60, edgecolors='black',
                   linewidths=0.8, zorder=8, alpha=0.5, depthshade=False)

    # Depression zone labels on visible faces (E_W face is hidden)
    for c_name in ['R', 'G', 'B']:
        f = FC[c_name]
        # Push label outward along face normal for readability
        outward = f / np.linalg.norm(f)
        off = outward * 0.35
        ax.text(f[0] + off[0], f[1] + off[1], f[2] + off[2],
                f'$E_{{{c_name}}}$', fontsize=13, fontweight='bold',
                color=CC[c_name], ha='center', va='center', zorder=11,
                bbox=dict(facecolor='white', alpha=0.75, edgecolor='none',
                          pad=1.5))

    # Center marker
    ax.scatter(0, 0, 0, c='black', s=30, zorder=9, depthshade=False)

    setup_ax(ax, r'(b) Face Coloring $-$ Depression Zones')

    plt.subplots_adjust(wspace=0.02)

    # Save
    for ext in ['pdf', 'png']:
        path = os.path.join(OUTPUT_DIR, f'fig_vertex_face_duality.{ext}')
        fig.savefig(path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path}")
    plt.close('all')


if __name__ == '__main__':
    main()
