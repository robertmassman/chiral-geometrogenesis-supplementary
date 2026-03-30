#!/usr/bin/env python3
"""
Figure: Stella Octangula to FCC Honeycomb (Theorem 0.0.6)

Five-panel progression showing how stellae octangulae tile 3D space:
(a) Single stella octangula (T+ union T-)
(b) Decomposition into 8 corner tetrahedra + 1 central octahedron
(c) Interlocking neighbors: center stella + 3 adjacent
(d) 3x3x3 stella grid with center highlighted
(e) Complete FCC tetrahedral-octahedral honeycomb

Key physics:
- Stella octangula = compound of two interpenetrating tetrahedra (Theorem 0.0.3)
- Each stella decomposes into 8 corner tets + 1 center oct (half cube volume)
- Adjacent stellae interlock: T+ vertices of one cube = T- vertices of neighbor
- Edge octahedra fill the remaining half of cube volume between stellae
- Together stellae + edge octs = tetrahedral-octahedral honeycomb (unique, Theorem 0.0.6)

Proof Document: docs/proofs/foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md
Also references: docs/proofs/foundations/Theorem-0.0.3-Stella-Uniqueness.md
Paper Section: Section 2.3 (Spatial Extension)

Output: fig_stella_to_fcc_panels.pdf, fig_stella_to_fcc_panels.png
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

# Colors (no purple per figures/CLAUDE.md)
C_TP = (0.20, 0.60, 0.86)       # Blue - T+
C_TM = (0.91, 0.30, 0.24)       # Red - T-
C_OCT = (0.15, 0.68, 0.38)      # Green - center oct
C_EOCT = (0.95, 0.61, 0.07)     # Amber - edge oct
C_SHARED = (0.18, 0.80, 0.44)   # Green - shared vertex
C_CUBE = (0.5, 0.5, 0.5)        # Gray - cube wireframe

a = 1.0
ELEV, AZIM = 28, 39


# ============================================================
# GEOMETRY GENERATORS
# ============================================================

def corner_tet(cx, cy, cz, dx, dy, dz):
    return np.array([
        [cx + dx*a, cy + dy*a, cz + dz*a],
        [cx + dx*a, cy + 0.5*a, cz + 0.5*a],
        [cx + 0.5*a, cy + dy*a, cz + 0.5*a],
        [cx + 0.5*a, cy + 0.5*a, cz + dz*a],
    ])

def center_oct(cx, cy, cz):
    return np.array([
        [cx + 0.5*a, cy + 0.5*a, cz],
        [cx + 0.5*a, cy + 0.5*a, cz + a],
        [cx + 0.5*a, cy, cz + 0.5*a],
        [cx + 0.5*a, cy + a, cz + 0.5*a],
        [cx, cy + 0.5*a, cz + 0.5*a],
        [cx + a, cy + 0.5*a, cz + 0.5*a],
    ])

def edge_oct_x(i, j, k):
    return np.array([
        [i*a, j*a, k*a], [(i+1)*a, j*a, k*a],
        [(i+0.5)*a, (j+0.5)*a, k*a], [(i+0.5)*a, (j-0.5)*a, k*a],
        [(i+0.5)*a, j*a, (k+0.5)*a], [(i+0.5)*a, j*a, (k-0.5)*a],
    ])

def edge_oct_y(i, j, k):
    return np.array([
        [i*a, j*a, k*a], [i*a, (j+1)*a, k*a],
        [(i+0.5)*a, (j+0.5)*a, k*a], [(i-0.5)*a, (j+0.5)*a, k*a],
        [i*a, (j+0.5)*a, (k+0.5)*a], [i*a, (j+0.5)*a, (k-0.5)*a],
    ])

def edge_oct_z(i, j, k):
    return np.array([
        [i*a, j*a, k*a], [i*a, j*a, (k+1)*a],
        [(i+0.5)*a, j*a, (k+0.5)*a], [(i-0.5)*a, j*a, (k+0.5)*a],
        [i*a, (j+0.5)*a, (k+0.5)*a], [i*a, (j-0.5)*a, (k+0.5)*a],
    ])

def stella_tp(cx, cy, cz):
    return np.array([[cx,cy,cz],[cx+1,cy+1,cz],[cx+1,cy,cz+1],[cx,cy+1,cz+1]], dtype=float) * a

def stella_tm(cx, cy, cz):
    return np.array([[cx+1,cy,cz],[cx,cy+1,cz],[cx,cy,cz+1],[cx+1,cy+1,cz+1]], dtype=float) * a


# ============================================================
# MATPLOTLIB 3D HELPERS
# ============================================================

TET_FACES = [(0,1,2),(0,1,3),(0,2,3),(1,2,3)]
TET_EDGES = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
OCT_OPP = {(0,1),(1,0),(2,3),(3,2),(4,5),(5,4)}


def draw_tet(ax, v, facecolor, edgecolor, alpha=0.3, lw=1.5):
    """Draw a tetrahedron with filled faces and edges."""
    v = np.array(v, dtype=float)
    faces = [v[list(f)] for f in TET_FACES]
    poly = Poly3DCollection(faces, alpha=alpha, facecolor=facecolor,
                            edgecolor=edgecolor, linewidth=lw)
    ax.add_collection3d(poly)


def draw_oct(ax, v, facecolor, edgecolor, alpha=0.3, lw=1.5):
    """Draw an octahedron with filled faces and edges."""
    v = np.array(v, dtype=float)
    faces = []
    for aa in [0,1]:
        for b in [2,3]:
            for c in [4,5]:
                faces.append(v[[aa, b, c]])
    poly = Poly3DCollection(faces, alpha=alpha, facecolor=facecolor,
                            edgecolor=edgecolor, linewidth=lw)
    ax.add_collection3d(poly)


def draw_cube_wire(ax, origin, color=C_CUBE, alpha=0.3, lw=0.8):
    """Draw a cube wireframe."""
    o = np.array(origin, dtype=float)
    c = [o, o+[a,0,0], o+[a,a,0], o+[0,a,0],
         o+[0,0,a], o+[a,0,a], o+[a,a,a], o+[0,a,a]]
    edges = [(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),(0,4),(1,5),(2,6),(3,7)]
    lines = [[c[i], c[j]] for i, j in edges]
    lc = Line3DCollection(lines, colors=[(*color, alpha)]*len(lines), linewidths=lw)
    ax.add_collection3d(lc)


def setup_3d_ax(ax, lim, title=''):
    """Configure a 3D axis with clean look."""
    ax.set_xlim(lim); ax.set_ylim(lim); ax.set_zlim(lim)
    ax.set_box_aspect([1,1,1])
    ax.view_init(elev=ELEV, azim=AZIM)
    ax.set_axis_off()
    if title:
        ax.set_title(title, fontsize=11, fontweight='bold', pad=-5)


# ============================================================
# BUILD FIGURE
# ============================================================

def main():
    fig = plt.figure(figsize=(15, 10))
    gs = gridspec.GridSpec(2, 3, hspace=0.05, wspace=0.02)

    # ---- (a) Stella Octangula ----
    ax = fig.add_subplot(gs[0, 0], projection='3d')
    tp = stella_tp(0, 0, 0)
    tm = stella_tm(0, 0, 0)
    draw_tet(ax, tp, C_TP, C_TP, alpha=0.25, lw=2)
    draw_tet(ax, tm, C_TM, C_TM, alpha=0.25, lw=2)
    # Vertices
    ax.scatter(*tp.T, c=[C_TP], s=30, edgecolors='black', linewidths=0.8, zorder=5)
    ax.scatter(*tm.T, c=[C_TM], s=30, edgecolors='black', linewidths=0.8, zorder=5)
    draw_cube_wire(ax, [0,0,0], alpha=0.2, lw=0.6)
    setup_3d_ax(ax, [-0.15, 1.15], r'(a) Stella Octangula ($T_+ \cup T_-$)')

    # ---- (b) Decomposition ----
    ax = fig.add_subplot(gs[0, 1], projection='3d')
    tp_tets = [corner_tet(0,0,0,dx,dy,dz) for dx,dy,dz in [(0,0,0),(1,1,0),(1,0,1),(0,1,1)]]
    tm_tets = [corner_tet(0,0,0,dx,dy,dz) for dx,dy,dz in [(1,0,0),(0,1,0),(0,0,1),(1,1,1)]]
    for t in tp_tets:
        draw_tet(ax, t, C_TP, C_TP, alpha=0.35, lw=1.5)
    for t in tm_tets:
        draw_tet(ax, t, C_TM, C_TM, alpha=0.35, lw=1.5)
    draw_oct(ax, center_oct(0,0,0), C_OCT, C_OCT, alpha=0.35, lw=1.5)
    draw_cube_wire(ax, [0,0,0], alpha=0.2, lw=0.6)
    setup_3d_ax(ax, [-0.15, 1.15], '(b) Decomposition (8 tets + 1 oct)')

    # ---- (c) Interlocking Neighbors ----
    ax = fig.add_subplot(gs[0, 2], projection='3d')
    # Center stella (solid)
    ctp = stella_tp(1,1,1); ctm = stella_tm(1,1,1)
    draw_tet(ax, ctp, C_TP, C_TP, alpha=0.4, lw=2)
    draw_tet(ax, ctm, C_TM, C_TM, alpha=0.4, lw=2)
    draw_cube_wire(ax, [1,1,1], color=(0,0,0), alpha=0.7, lw=1.5)
    # 3 neighbors (filled, lighter)
    nbr = [(0,1,1),(1,0,1),(1,1,0)]
    for ncx,ncy,ncz in nbr:
        ntp = stella_tp(ncx,ncy,ncz); ntm = stella_tm(ncx,ncy,ncz)
        draw_tet(ax, ntp, C_TP, C_TP, alpha=0.15, lw=1.2)
        draw_tet(ax, ntm, C_TM, C_TM, alpha=0.15, lw=1.2)
        draw_cube_wire(ax, [ncx,ncy,ncz], alpha=0.15, lw=0.5)
    # Edge octs at shared faces
    eoct_specs = set()
    gen = {'x': edge_oct_x, 'y': edge_oct_y, 'z': edge_oct_z}
    for ncx,ncy,ncz in nbr:
        if ncx != 1:
            fx = min(ncx,1)+1
            eoct_specs.update([('y',fx,1,1),('y',fx,1,2),('z',fx,1,1),('z',fx,2,1)])
        elif ncy != 1:
            fy = min(ncy,1)+1
            eoct_specs.update([('x',1,fy,1),('x',1,fy,2),('z',1,fy,1),('z',2,fy,1)])
        else:
            fz = min(ncz,1)+1
            eoct_specs.update([('x',1,1,fz),('x',1,2,fz),('y',1,1,fz),('y',2,1,fz)])
    for axis, i, j, k in eoct_specs:
        draw_oct(ax, gen[axis](i,j,k), C_EOCT, C_EOCT, alpha=0.2, lw=0.8)
    # Shared vertices
    shared = set()
    for ncx,ncy,ncz in nbr:
        if ncx != 1:
            fx = min(ncx,1)+1
            for j in [1,2]:
                for k in [1,2]: shared.add((fx,j,k))
        elif ncy != 1:
            fy = min(ncy,1)+1
            for i in [1,2]:
                for k in [1,2]: shared.add((i,fy,k))
        else:
            fz = min(ncz,1)+1
            for i in [1,2]:
                for j in [1,2]: shared.add((i,j,fz))
    sv = np.array(sorted(shared), dtype=float) * a
    ax.scatter(sv[:,0], sv[:,1], sv[:,2], c=[C_SHARED], s=50, marker='D',
              edgecolors='black', linewidths=1, zorder=5)
    setup_3d_ax(ax, [-0.2, 2.2], '(c) Interlocking Neighbors')

    # ---- (d) 3x3x3 Stella Grid ----
    ax = fig.add_subplot(gs[1, 0], projection='3d')
    ng = 3
    # Center stella (solid)
    draw_tet(ax, stella_tp(1,1,1), C_TP, C_TP, alpha=0.5, lw=2)
    draw_tet(ax, stella_tm(1,1,1), C_TM, C_TM, alpha=0.5, lw=2)
    draw_cube_wire(ax, [1,1,1], color=(0,0,0), alpha=0.7, lw=1.5)
    # 26 surrounding (filled, faint)
    for cx in range(ng):
        for cy in range(ng):
            for cz in range(ng):
                if cx == 1 and cy == 1 and cz == 1:
                    continue
                draw_tet(ax, stella_tp(cx,cy,cz), C_TP, C_TP, alpha=0.08, lw=0.6)
                draw_tet(ax, stella_tm(cx,cy,cz), C_TM, C_TM, alpha=0.08, lw=0.6)
    # Edge octs
    for i in range(ng):
        for j in range(ng+1):
            for k in range(ng+1):
                v = edge_oct_x(i,j,k)
                if np.all(v >= -0.5*a) and np.all(v <= (ng+0.5)*a):
                    draw_oct(ax, v, C_EOCT, C_EOCT, alpha=0.08, lw=0.3)
    for i in range(ng+1):
        for j in range(ng):
            for k in range(ng+1):
                v = edge_oct_y(i,j,k)
                if np.all(v >= -0.5*a) and np.all(v <= (ng+0.5)*a):
                    draw_oct(ax, v, C_EOCT, C_EOCT, alpha=0.08, lw=0.3)
    for i in range(ng+1):
        for j in range(ng+1):
            for k in range(ng):
                v = edge_oct_z(i,j,k)
                if np.all(v >= -0.5*a) and np.all(v <= (ng+0.5)*a):
                    draw_oct(ax, v, C_EOCT, C_EOCT, alpha=0.08, lw=0.3)
    # Grid wire
    for i in range(ng+1):
        for j in range(ng+1):
            for k in range(ng+1):
                o = np.array([i,j,k], dtype=float) * a
                if i < ng:
                    ax.plot3D([o[0], o[0]+a], [o[1], o[1]], [o[2], o[2]],
                             color='gray', alpha=0.2, lw=0.4)
                if j < ng:
                    ax.plot3D([o[0], o[0]], [o[1], o[1]+a], [o[2], o[2]],
                             color='gray', alpha=0.2, lw=0.4)
                if k < ng:
                    ax.plot3D([o[0], o[0]], [o[1], o[1]], [o[2], o[2]+a],
                             color='gray', alpha=0.2, lw=0.4)
    setup_3d_ax(ax, [-0.2, 3.2], r'(d) $3\times3\times3$ Stella Grid')

    # ---- (e) FCC Honeycomb ----
    ax = fig.add_subplot(gs[1, 1], projection='3d')
    nf = 3
    # Center cube decomposed at full opacity
    for dx,dy,dz in [(0,0,0),(1,1,0),(1,0,1),(0,1,1)]:
        draw_tet(ax, corner_tet(1,1,1,dx,dy,dz), C_TP, C_TP, alpha=0.5, lw=2)
    for dx,dy,dz in [(1,0,0),(0,1,0),(0,0,1),(1,1,1)]:
        draw_tet(ax, corner_tet(1,1,1,dx,dy,dz), C_TM, C_TM, alpha=0.5, lw=2)
    draw_oct(ax, center_oct(1,1,1), C_OCT, C_OCT, alpha=0.5, lw=2)
    draw_cube_wire(ax, [1,1,1], color=(0,0,0), alpha=0.8, lw=1.5)
    # Surrounding 26 cubes decomposed (faint filled)
    for cx in range(nf):
        for cy in range(nf):
            for cz in range(nf):
                if cx == 1 and cy == 1 and cz == 1:
                    continue
                for dx in range(2):
                    for dy in range(2):
                        for dz in range(2):
                            draw_tet(ax, corner_tet(cx,cy,cz,dx,dy,dz),
                                    C_TP, (0,0,0), alpha=0.06, lw=0.3)
                draw_oct(ax, center_oct(cx,cy,cz), C_OCT, (0,0,0), alpha=0.06, lw=0.3)
    # All edge octs
    for i in range(nf):
        for j in range(nf+1):
            for k in range(nf+1):
                v = edge_oct_x(i,j,k)
                if np.all(v >= -0.5*a) and np.all(v <= (nf+0.5)*a):
                    draw_oct(ax, v, C_EOCT, (0,0,0), alpha=0.1, lw=0.3)
    for i in range(nf+1):
        for j in range(nf):
            for k in range(nf+1):
                v = edge_oct_y(i,j,k)
                if np.all(v >= -0.5*a) and np.all(v <= (nf+0.5)*a):
                    draw_oct(ax, v, C_EOCT, (0,0,0), alpha=0.1, lw=0.3)
    for i in range(nf+1):
        for j in range(nf+1):
            for k in range(nf):
                v = edge_oct_z(i,j,k)
                if np.all(v >= -0.5*a) and np.all(v <= (nf+0.5)*a):
                    draw_oct(ax, v, C_EOCT, (0,0,0), alpha=0.1, lw=0.3)
    setup_3d_ax(ax, [-0.1, 3.1], '(e) FCC Honeycomb')

    # ---- Legend ----
    ax_leg = fig.add_subplot(gs[1, 2])
    ax_leg.set_xlim(0, 5); ax_leg.set_ylim(0, 6.5)
    ax_leg.set_axis_off()
    items = [
        (5.5, '^', C_TP, r'$T_+$ tetrahedron'),
        (4.5, 'v', C_TM, r'$T_-$ tetrahedron'),
        (3.5, 'D', C_OCT, 'Center octahedron'),
        (2.5, 'D', C_EOCT, 'Edge octahedron'),
        (1.5, 's', (1,1,1), 'Unit cube'),
        (0.7, 'D', C_SHARED, 'Shared vertex'),
    ]
    for y, marker, color, label in items:
        ec = 'black' if color != (1,1,1) else (0.3, 0.3, 0.3)
        ax_leg.scatter(0.6, y, s=120, c=[color], marker=marker,
                      edgecolors=ec, linewidths=1.5, zorder=5)
        ax_leg.text(1.2, y, label, fontsize=11, va='center')
    ax_leg.set_title('Legend', fontsize=11, fontweight='bold')

    plt.tight_layout()

    # Save
    for ext in ['pdf', 'png']:
        path = os.path.join(OUTPUT_DIR, f'fig_stella_to_fcc_panels.{ext}')
        fig.savefig(path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path}")
    plt.close('all')


if __name__ == '__main__':
    main()
