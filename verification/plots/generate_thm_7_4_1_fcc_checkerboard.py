#!/usr/bin/env python3
"""
FCC Tet-Oct Honeycomb: Bipartite 2-Coloring (Theorem 7.4.1, §7.2)
===================================================================

Two-panel figure:
  (a) Exploded view — up-tet, down-tet, and octahedron sharing faces
  (b) Assembled cluster with (111) reflection plane and bipartite coloring

The bipartite property: every face is shared between one tet and one oct.
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import matplotlib.patches as mpatches
from scipy.spatial import ConvexHull
from itertools import combinations

a = 1.0
d_nn = a / np.sqrt(2)

# ── Colors ──
UP_CLR   = '#2166AC'    # strong blue
DN_CLR   = '#B2182B'    # strong red
OCT_CLR  = '#F4A460'    # sandy brown / amber
SHARED_CLR = '#2ca02c'  # green
PLANE_CLR  = '#87CEEB'  # sky blue

# ── Cell definitions (all verified regular) ──

# Up-tetrahedron T+ : centroid near (a/4, a/4, a/4)
T_up = np.array([[0,0,0], [.5,.5,0], [.5,0,.5], [0,.5,.5]], float) * a

# Down-tetrahedra T- adjacent to the central octahedron O_4
# T_dn_A shares face with O_4 through vertices {(a/2,a/2,a), (a/2,0,a/2), (0,a/2,a/2)}
# 4th vertex at (0,0,a)
T_dn_A = np.array([[.5,.5,1], [.5,0,.5], [0,.5,.5], [0,0,1]], float) * a

# T_dn_B shares face with O_4 through {(a/2,a/2,0), (a/2,0,a/2), (a,a/2,a/2)}
# 4th vertex at (a,0,0)
T_dn_B = np.array([[.5,.5,0], [.5,0,.5], [1,.5,.5], [1,0,0]], float) * a

# T_dn_C shares face with O_4 through {(a/2,a/2,0), (0,a/2,a/2), (a/2,a,a/2)}
# 4th vertex at (0,a,0)
T_dn_C = np.array([[.5,.5,0], [0,.5,.5], [.5,1,.5], [0,1,0]], float) * a

# Octahedron O_4: center at (a/2, a/2, a/2), 6 face-center vertices
O_4 = np.array([[.5,.5,0], [.5,0,.5], [0,.5,.5],
                [.5,.5,1], [1,.5,.5], [.5,1,.5]], float) * a

# ── Validation ──
def check_tet(v, label):
    edges = [np.linalg.norm(v[i]-v[j]) for i,j in combinations(range(4),2)]
    ok = all(abs(e - d_nn) < 0.01*d_nn for e in edges)
    print(f"  {label}: {'OK' if ok else 'FAIL'} edges={[f'{e:.4f}' for e in sorted(edges)]}")
    return ok

def check_oct(v, label):
    dists = sorted([np.linalg.norm(v[i]-v[j]) for i,j in combinations(range(6),2)])
    n_e = sum(1 for d in dists if abs(d - d_nn) < 0.01*d_nn)
    n_d = sum(1 for d in dists if abs(d - a) < 0.01*a)
    ok = (n_e == 12 and n_d == 3)
    print(f"  {label}: {'OK' if ok else 'FAIL'} ({n_e} edges, {n_d} diags)")
    return ok

print("Cell checks:")
check_tet(T_up, "T_up")
check_tet(T_dn_A, "T_dn_A")
check_tet(T_dn_B, "T_dn_B")
check_tet(T_dn_C, "T_dn_C")
check_oct(O_4, "O_4")

# ── Find shared faces ──
def shared_faces(cell_a, cell_b):
    """Find equilateral triangular faces shared between two polyhedra."""
    sa = set(map(tuple, np.round(cell_a, 8)))
    sb = set(map(tuple, np.round(cell_b, 8)))
    common = sa & sb
    faces = []
    for tri in combinations(common, 3):
        arr = np.array(tri)
        edges = [np.linalg.norm(arr[i]-arr[j]) for i,j in [(0,1),(0,2),(1,2)]]
        if all(abs(e - d_nn) < 0.02*d_nn for e in edges):
            faces.append(arr)
    return faces

sf_up_o4 = shared_faces(T_up, O_4)
sf_dnA_o4 = shared_faces(T_dn_A, O_4)
sf_dnB_o4 = shared_faces(T_dn_B, O_4)
sf_dnC_o4 = shared_faces(T_dn_C, O_4)
print(f"Shared: T_up-O_4={len(sf_up_o4)}, T_dn_A-O_4={len(sf_dnA_o4)}, "
      f"T_dn_B-O_4={len(sf_dnB_o4)}, T_dn_C-O_4={len(sf_dnC_o4)}")

# ── Drawing helpers ──
def draw_poly(ax, verts, fc, ec, alpha=0.4, lw=1.0):
    hull = ConvexHull(verts)
    faces = [verts[s] for s in hull.simplices]
    ax.add_collection3d(Poly3DCollection(faces, alpha=alpha, facecolor=fc,
                                         edgecolor=ec, linewidth=lw))

def draw_face(ax, tri, fc, ec, alpha=0.5, lw=2.0):
    ax.add_collection3d(Poly3DCollection([tri], alpha=alpha, facecolor=fc,
                                         edgecolor=ec, linewidth=lw))

def explode(verts, center, factor):
    c = verts.mean(axis=0)
    d = c - center
    norm = np.linalg.norm(d)
    if norm < 1e-10:
        d = np.array([0.0, 0.0, 1.0])
    else:
        d = d / norm
    return verts + factor * d

# ============================================================================
# Figure
# ============================================================================
fig = plt.figure(figsize=(16, 7.5), facecolor='white')

# ── Panel (a): Exploded view ──
ax1 = fig.add_subplot(121, projection='3d', facecolor='white')

# Show T_up, T_dn_A, and O_4 exploded apart
center = np.mean([T_up.mean(0), T_dn_A.mean(0), O_4.mean(0)], axis=0)
EX = 0.32  # explode distance

T_up_ex  = explode(T_up, center, EX)
T_dn_ex  = explode(T_dn_A, center, EX)
O_4_ex   = explode(O_4, center, EX)

draw_poly(ax1, T_up_ex, UP_CLR, '#0d3366', alpha=0.55, lw=1.4)
draw_poly(ax1, T_dn_ex, DN_CLR, '#6b0f1a', alpha=0.55, lw=1.4)
draw_poly(ax1, O_4_ex, OCT_CLR, '#8B6914', alpha=0.30, lw=1.4)

# Show shared faces at intermediate positions (ghost)
for sf in sf_up_o4:
    sf_mid = explode(sf, center, EX * 0.45)
    draw_face(ax1, sf_mid, SHARED_CLR, 'darkgreen', alpha=0.35, lw=1.8)
for sf in sf_dnA_o4:
    sf_mid = explode(sf, center, EX * 0.45)
    draw_face(ax1, sf_mid, SHARED_CLR, 'darkgreen', alpha=0.35, lw=1.8)

# Dashed connection lines between cell centroids and shared face midpoints
for sf in sf_up_o4:
    mid = sf.mean(0)
    for cell_ex, cell_orig in [(T_up_ex, T_up), (O_4_ex, O_4)]:
        c_ex = cell_ex.mean(0)
        mid_ex = explode(mid.reshape(1,3), center, EX*0.45)[0]
        ax1.plot([c_ex[0], mid_ex[0]], [c_ex[1], mid_ex[1]], [c_ex[2], mid_ex[2]],
                 '--', color='gray', alpha=0.4, lw=0.8)

# Labels
c = T_up_ex.mean(0)
ax1.text(c[0]-0.18, c[1]-0.12, c[2]-0.22,
         r'Up-tet $T_+$' + '\n("Black")', fontsize=10.5, ha='center',
         color=UP_CLR, fontweight='bold',
         bbox=dict(boxstyle='round,pad=0.25', fc='white', alpha=0.93, ec=UP_CLR, lw=1))

c = T_dn_ex.mean(0)
ax1.text(c[0]+0.02, c[1]+0.05, c[2]+0.25,
         r'Down-tet $T_-$' + '\n("Black")', fontsize=10.5, ha='center',
         color=DN_CLR, fontweight='bold',
         bbox=dict(boxstyle='round,pad=0.25', fc='white', alpha=0.93, ec=DN_CLR, lw=1))

c = O_4_ex.mean(0)
ax1.text(c[0]+0.28, c[1]+0.08, c[2]-0.05,
         'Octahedron\n("White")', fontsize=10.5, ha='center',
         color='#8B6914', fontweight='bold',
         bbox=dict(boxstyle='round,pad=0.25', fc='white', alpha=0.93, ec=OCT_CLR, lw=1))

# Shared face label
if sf_up_o4:
    mid = sf_up_o4[0].mean(0)
    mid_ex = explode(mid.reshape(1,3), center, EX*0.45)[0]
    ax1.text(mid_ex[0]-0.22, mid_ex[1]-0.18, mid_ex[2]+0.0,
             'Shared\nface', fontsize=8.5, ha='center', color='darkgreen', fontweight='bold',
             bbox=dict(boxstyle='round,pad=0.2', fc='#e8f8e8', alpha=0.92, ec='darkgreen', lw=0.7))

ax1.set_xlim(-0.25, 0.95)
ax1.set_ylim(-0.20, 1.00)
ax1.set_zlim(-0.15, 1.25)
ax1.set_xlabel('x/a', fontsize=10, labelpad=4)
ax1.set_ylabel('y/a', fontsize=10, labelpad=4)
ax1.set_zlabel('z/a', fontsize=10, labelpad=4)
ax1.view_init(elev=20, azim=-48)
for pane in [ax1.xaxis.pane, ax1.yaxis.pane, ax1.zaxis.pane]:
    pane.fill = False
    pane.set_edgecolor('lightgray')
ax1.grid(True, alpha=0.12)
ax1.set_title('(a)  Exploded View: Primitive Cells\n'
              r'$T_+$, $T_-$, and octahedron sharing faces',
              fontsize=12, fontweight='bold', pad=10)

# ── Panel (b): Assembled cluster with (111) plane ──
ax2 = fig.add_subplot(122, projection='3d', facecolor='white')

# Draw all verified cells in assembled position
# Up-tet
draw_poly(ax2, T_up, UP_CLR, '#0d3366', alpha=0.50, lw=1.3)

# Down-tets (3 regular ones sharing faces with O_4)
for t in [T_dn_A, T_dn_B, T_dn_C]:
    draw_poly(ax2, t, DN_CLR, '#6b0f1a', alpha=0.50, lw=1.3)

# Central octahedron
draw_poly(ax2, O_4, OCT_CLR, '#8B6914', alpha=0.22, lw=1.3)

# Highlight some shared tet-oct faces
for sf in sf_up_o4:
    draw_face(ax2, sf, SHARED_CLR, 'darkgreen', alpha=0.40, lw=2.0)
for sf in sf_dnA_o4[:1]:  # just one from each dn-tet
    draw_face(ax2, sf, SHARED_CLR, 'darkgreen', alpha=0.40, lw=2.0)

# (111) reflection plane
plane_h = 0.75 * a  # x+y+z = 0.75a — between the up and down tet layers

def make_111_plane(h, lo=-0.15, hi=1.15):
    """Polygon where x+y+z=h intersects [lo,hi]^3."""
    pts = []
    box = [lo, hi]
    for axis in range(3):
        for val in box:
            other = [i for i in range(3) if i != axis]
            a1, a2 = other
            # Fix axis=val, then x_{a1} ranges, x_{a2} = h - val - x_{a1}
            for t in np.linspace(lo, hi, 200):
                r = h - val - t
                if lo - 1e-8 <= r <= hi + 1e-8:
                    p = [0,0,0]
                    p[axis] = val
                    p[a1] = t
                    p[a2] = np.clip(r, lo, hi)
                    pts.append(p)
    if not pts:
        return None
    pts = np.array(pts)
    # Deduplicate
    unique = [pts[0]]
    for p in pts[1:]:
        if all(np.linalg.norm(p - u) > 1e-6 for u in unique):
            unique.append(p)
    pts = np.array(unique)
    if len(pts) < 3:
        return None
    # Sort by angle
    ctr = pts.mean(0)
    n = np.array([1,1,1]) / np.sqrt(3)
    u = np.cross(n, [1,0,0]); u /= np.linalg.norm(u)
    v = np.cross(n, u)
    ang = [np.arctan2(np.dot(p-ctr, v), np.dot(p-ctr, u)) for p in pts]
    # Keep only the convex hull vertices
    order = np.argsort(ang)
    sorted_pts = pts[order]
    # Thin to convex hull in 2D
    coords_2d = np.array([[np.dot(p-ctr, u), np.dot(p-ctr, v)] for p in sorted_pts])
    try:
        hull = ConvexHull(coords_2d)
        return sorted_pts[hull.vertices]
    except:
        return sorted_pts

ppoly = make_111_plane(plane_h, lo=-0.18, hi=1.18)
if ppoly is not None:
    ax2.add_collection3d(Poly3DCollection([ppoly], alpha=0.12, facecolor=PLANE_CLR,
                                           edgecolor='steelblue', linewidth=1.5,
                                           linestyle='--'))

# Cell labels
c = T_up.mean(0)
ax2.text(c[0]-0.22, c[1]-0.15, c[2]-0.12,
         r'$T_+$', fontsize=13, ha='center', color=UP_CLR, fontweight='bold',
         bbox=dict(boxstyle='round,pad=0.15', fc='white', alpha=0.92, ec=UP_CLR, lw=1))

c = T_dn_A.mean(0)
ax2.text(c[0]-0.15, c[1]+0.05, c[2]+0.18,
         r'$T_-$', fontsize=13, ha='center', color=DN_CLR, fontweight='bold',
         bbox=dict(boxstyle='round,pad=0.15', fc='white', alpha=0.92, ec=DN_CLR, lw=1))

c = O_4.mean(0)
ax2.text(c[0]+0.22, c[1]+0.20, c[2]-0.02,
         'Oct', fontsize=11, ha='center', color='#8B6914', fontweight='bold',
         bbox=dict(boxstyle='round,pad=0.15', fc='white', alpha=0.92, ec=OCT_CLR, lw=1))

# (111) plane annotation
if ppoly is not None:
    pc = ppoly.mean(0)
    ax2.text(pc[0]+0.35, pc[1]-0.22, pc[2]+0.18,
             '(111) plane\n' + r'$\theta: T_+ \leftrightarrow T_-$' + '\n2-coloring preserved',
             fontsize=8.5, ha='center', color='steelblue', fontweight='bold',
             bbox=dict(boxstyle='round,pad=0.25', fc='white', alpha=0.93, ec='steelblue', lw=0.8))

ax2.set_xlim(-0.2, 1.15)
ax2.set_ylim(-0.2, 1.15)
ax2.set_zlim(-0.15, 1.20)
ax2.set_xlabel('x/a', fontsize=10, labelpad=4)
ax2.set_ylabel('y/a', fontsize=10, labelpad=4)
ax2.set_zlabel('z/a', fontsize=10, labelpad=4)
ax2.view_init(elev=22, azim=-50)
for pane in [ax2.xaxis.pane, ax2.yaxis.pane, ax2.zaxis.pane]:
    pane.fill = False
    pane.set_edgecolor('lightgray')
ax2.grid(True, alpha=0.12)
ax2.set_title('(b)  Assembled Cluster with (111) Plane\n'
              'Every face is shared between one tet and one oct',
              fontsize=12, fontweight='bold', pad=10)

# ── Shared legend at bottom ──
legend_elements = [
    mpatches.Patch(facecolor=UP_CLR, edgecolor='k', alpha=0.55,
                   label=r'Up-tetrahedra ($T_+$) — "Black"'),
    mpatches.Patch(facecolor=DN_CLR, edgecolor='k', alpha=0.55,
                   label=r'Down-tetrahedra ($T_-$) — "Black"'),
    mpatches.Patch(facecolor=OCT_CLR, edgecolor='k', alpha=0.35,
                   label=r'Octahedra — "White"'),
    mpatches.Patch(facecolor=SHARED_CLR, edgecolor='darkgreen', alpha=0.5,
                   label='Shared tet-oct face'),
    mpatches.Patch(facecolor=PLANE_CLR, edgecolor='steelblue', alpha=0.2,
                   label=r'(111) reflection plane $\theta$'),
]
fig.legend(handles=legend_elements, loc='lower center', ncol=3, fontsize=9.5,
           framealpha=0.95, edgecolor='gray', fancybox=True,
           bbox_to_anchor=(0.5, -0.02))

fig.suptitle('FCC Tet-Oct Honeycomb: Bipartite Checkerboard 2-Coloring  '
             '(Theorem 7.4.1, §7.2)',
             fontsize=14.5, fontweight='bold', y=1.01)

fig.text(0.5, -0.07,
         'Bipartite property: every triangular face is shared between one tetrahedron '
         'and one octahedron.\nNo two cells of the same type share a face. '
         r'The (111) reflection swaps $T_+ \leftrightarrow T_-$ but preserves the 2-coloring.',
         ha='center', fontsize=9.5, style='italic', color='#555555')

plt.tight_layout(rect=[0, 0.04, 1, 0.96])
outpath = ('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/'
           'verification/plots/thm_7_4_1_fcc_checkerboard_structure.png')
plt.savefig(outpath, dpi=200, bbox_inches='tight', facecolor='white')
print(f"\nSaved: {outpath}")
plt.close()
print("Done.")
