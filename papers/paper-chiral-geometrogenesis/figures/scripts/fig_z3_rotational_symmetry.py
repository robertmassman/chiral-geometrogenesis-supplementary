#!/usr/bin/env python3
"""
Figure: Z3 Rotational Symmetry (Section 5)

Two-panel visualization of the Z3 discrete symmetry of the stella octangula:
(a) 3D stella with [111] body diagonal as Z3 rotation axis, colored R/G/B vertices
(b) View along [111] showing equilateral triangle of R/G/B with 120-degree rotation arrow

Key physics:
- The [111] diagonal of the bounding cube is a 3-fold rotation axis
- T+ color vertices (R, G, B) map to each other under 120-degree rotations
- This geometric Z3 is the origin of the Z3 center of SU(3)
- The W vertex (singlet) sits on the rotation axis

Proof Document: docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md
Paper Section: Section 5 (Z3 Rotational Symmetry)
Output: fig_z3_rotational_symmetry.pdf, fig_z3_rotational_symmetry.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
import matplotlib.gridspec as gridspec
from matplotlib.patches import FancyArrowPatch, Arc
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
CC = {
    'R': (0.91, 0.15, 0.15),
    'G': (0.15, 0.68, 0.15),
    'B': (0.20, 0.40, 0.86),
    'W': (0.55, 0.55, 0.55),
}
C_TP = (0.20, 0.60, 0.86)
C_TM = (0.91, 0.30, 0.24)
C_GOLD = (0.85, 0.65, 0.13)

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
TET_FACE_IDX = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]

# [111] direction (normalized)
AXIS_111 = np.array([1, 1, 1]) / s3


def draw_tet_faces(ax, verts_4, facecolor, edgecolor, alpha=0.3, lw=1.5):
    """Draw a tetrahedron given 4 vertices."""
    v = np.array(verts_4)
    faces = [v[list(f)] for f in TET_FACE_IDX]
    poly = Poly3DCollection(faces, alpha=alpha, facecolor=facecolor,
                            edgecolor=edgecolor, linewidth=lw)
    ax.add_collection3d(poly)


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


def setup_ax(ax, title='', lim=0.78):
    """Configure 3D axis."""
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.set_axis_off()
    if title:
        ax.set_title(title, fontsize=11, fontweight='bold', pad=-5)


def project_onto_plane_perp_111(v):
    """Project 3D vector onto the plane perpendicular to [111]."""
    # Orthonormal basis for the plane perp to [111]:
    # e1 = [1, -1, 0] / sqrt(2)
    # e2 = [1, 1, -2] / sqrt(6)
    e1 = np.array([1, -1, 0]) / np.sqrt(2)
    e2 = np.array([1, 1, -2]) / np.sqrt(6)
    return np.array([np.dot(v, e1), np.dot(v, e2)])


def main():
    fig = plt.figure(figsize=(12, 5.5))
    gs = gridspec.GridSpec(1, 2, wspace=0.05, width_ratios=[1.1, 1])

    # ==============================================================
    # (a) 3D Stella with Z3 Axis [111]
    # ==============================================================
    ax = fig.add_subplot(gs[0, 0], projection='3d')

    CUBE_HALF = 1.0 / s3

    # T+ with black edges
    tp_arr = np.array([TP[c] for c in COLOR_KEYS])
    faces_tp = [tp_arr[list(f)] for f in TET_FACE_IDX]
    poly = Poly3DCollection(faces_tp, alpha=0.08, facecolor=C_TP,
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

    # Z3 rotation axis: bold gold arrow along [111]
    axis_len = 0.85
    ax.quiver(-AXIS_111[0] * axis_len, -AXIS_111[1] * axis_len,
              -AXIS_111[2] * axis_len,
              2 * AXIS_111[0] * axis_len, 2 * AXIS_111[1] * axis_len,
              2 * AXIS_111[2] * axis_len,
              color=C_GOLD, arrow_length_ratio=0.06, linewidth=3.5,
              alpha=0.9, zorder=15)

    # Label the axis — use 2D overlay for precise screen positioning
    ax.text2D(0.44, 0.57, r'$[111]$', transform=ax.transAxes,
              fontsize=12, fontweight='bold', color=C_GOLD, ha='center',
              va='center', zorder=16)

    # Colored vertex dots
    for c_name in COLOR_KEYS:
        pos = TP[c_name]
        ax.scatter(*pos, c=[CC[c_name]], s=280, edgecolors='black',
                   linewidths=1.5, zorder=10, depthshade=False)

    # Vertex labels
    for c_name in COLOR_KEYS:
        pos = TP[c_name]
        direction = pos / np.linalg.norm(pos)
        off = direction * 0.20
        lbl_color = (0.35, 0.35, 0.35) if c_name == 'W' else CC[c_name]
        ax.text(pos[0] + off[0], pos[1] + off[1], pos[2] + off[2],
                f'$v_{{{c_name}}}$', fontsize=12, fontweight='bold',
                color=lbl_color, ha='center', va='center', zorder=11)

    # Center marker
    ax.scatter(0, 0, 0, c='black', s=30, zorder=9, depthshade=False)

    setup_ax(ax, r'(a) Stella with $\mathbb{Z}_3$ Axis $[111]$')
    ax.view_init(elev=28, azim=39)

    # ==============================================================
    # (b) View Along [111]: Z3 Rotation
    # ==============================================================
    ax2 = fig.add_subplot(gs[0, 1])

    # Project all T+ vertices onto plane perp to [111]
    proj = {}
    for c in COLOR_KEYS:
        proj[c] = project_onto_plane_perp_111(TP[c])

    # Draw the equilateral triangle connecting R, G, B
    tri_verts = np.array([proj['R'], proj['G'], proj['B'], proj['R']])
    ax2.plot(tri_verts[:, 0], tri_verts[:, 1], '-', color='black',
             lw=1.5, alpha=0.4)
    ax2.fill(tri_verts[:3, 0], tri_verts[:3, 1], alpha=0.05, color='gray')

    # Colored vertex dots
    for c_name in ['R', 'G', 'B']:
        p = proj[c_name]
        ax2.plot(p[0], p[1], 'o', color=CC[c_name], markersize=16,
                 markeredgecolor='black', markeredgewidth=1.5, zorder=10)
        # Labels offset outward
        direction = p / (np.linalg.norm(p) + 1e-8)
        off = direction * 0.18
        ax2.text(p[0] + off[0], p[1] + off[1],
                 f'$v_{{{c_name}}}$', fontsize=13, fontweight='bold',
                 color=CC[c_name], ha='center', va='center', zorder=11)

    # W vertex projects to origin along [111]
    w_proj = proj['W']
    ax2.plot(w_proj[0], w_proj[1], '*', color=C_GOLD, markersize=14,
             markeredgecolor='black', markeredgewidth=1.0, zorder=12)
    ax2.text(w_proj[0] + 0.08, w_proj[1] + 0.08, r'$v_W$', fontsize=11,
             color=(0.35, 0.35, 0.35), fontweight='bold', zorder=13)

    # Draw circular arrow for 120-degree Z3 rotation
    # Arrow arc from R -> G -> B
    radius = np.linalg.norm(proj['R']) * 0.42
    # Draw arc
    angles_arc = np.linspace(0, 2 * np.pi * 0.85, 200)
    # Start angle: angle of R projection
    angle_R = np.arctan2(proj['R'][1], proj['R'][0])
    arc_x = radius * np.cos(angles_arc + angle_R + 0.15)
    arc_y = radius * np.sin(angles_arc + angle_R + 0.15)
    ax2.plot(arc_x, arc_y, '-', color=C_GOLD, lw=2.5, alpha=0.8, zorder=8)

    # Arrowhead at the end of the arc
    end_angle = angle_R + 0.15 + 2 * np.pi * 0.85
    arrow_dx = -radius * np.sin(end_angle) * 0.15
    arrow_dy = radius * np.cos(end_angle) * 0.15
    ax2.annotate('', xy=(arc_x[-1] + arrow_dx, arc_y[-1] + arrow_dy),
                 xytext=(arc_x[-1], arc_y[-1]),
                 arrowprops=dict(arrowstyle='->', color=C_GOLD, lw=2.5,
                                 mutation_scale=18))

    # Label the rotation
    ax2.text(0.0, -0.15, r'$120°$', fontsize=12, fontweight='bold',
             color=C_GOLD, ha='center', va='center',
             bbox=dict(facecolor='white', alpha=0.8, edgecolor='none',
                       pad=2))

    # Axis label
    ax2.text(0.02, 0.95, r'View along $[111]$', transform=ax2.transAxes,
             fontsize=10, ha='left', va='top', style='italic',
             color=(0.4, 0.4, 0.4))

    ax2.set_aspect('equal')
    ax2.set_xlim(-1.05, 1.05)
    ax2.set_ylim(-1.25, 1.05)
    ax2.axhline(0, color='gray', lw=0.5, alpha=0.2)
    ax2.axvline(0, color='gray', lw=0.5, alpha=0.2)
    ax2.set_xlabel(r'$e_1 = [1,\bar{1},0]/\sqrt{2}$', fontsize=10)
    ax2.set_ylabel(r'$e_2 = [1,1,\bar{2}]/\sqrt{6}$', fontsize=10)
    ax2.set_title(r'(b) $\mathbb{Z}_3$ Rotation: $R \to G \to B$',
                  fontsize=11, fontweight='bold')

    plt.tight_layout()

    # Save
    for ext in ['pdf', 'png']:
        path = os.path.join(OUTPUT_DIR, f'fig_z3_rotational_symmetry.{ext}')
        fig.savefig(path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path}")
    plt.close('all')


if __name__ == '__main__':
    main()
