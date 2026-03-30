#!/usr/bin/env python3
"""
Figure: Geometry Emerging from Discrete Structure
==================================================

4-panel visualization showing the stella octangula (discrete) smoothly
blending into a sphere (continuous) via the spherification formula:

    v(t) = (1-t) * v_flat + t * R * normalize(v_flat)

Z₃ color structure (R, G, B phases on T₊; R̄, Ḡ, B̄ on T₋) persists
at all blending levels, demonstrating that the topological invariant
(Z₃ center symmetry) survives the continuum limit.

The wireframe opacity fades as t → 1, showing discrete edges dissolving
while the smooth colored surface emerges — geometry from structure.

Related:
- Paper Section: Continuum Limit from Discrete Structure (sec:continuum-limit)
- Theorem: Z₃ survival through all limits
- Definition 0.1.1: Stella Octangula Boundary Topology

Output:
- fig_geometry_emergence.png
- fig_geometry_emergence.pdf

Author: Chiral Geometrogenesis Project
Date: 2026-03-18
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import Patch
from pathlib import Path

OUTPUT_DIR = Path(__file__).parent.parent
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# ============================================================================
# COLOR PALETTE — Z₃ phases mapped to RGB
# ============================================================================

# T₊ face colors (saturated) — each face colored by its Z₃ phase sector
FACE_COLORS_PLUS = [
    (0.91, 0.30, 0.24, 0.92),   # R phase (0)
    (0.15, 0.68, 0.38, 0.92),   # G phase (2π/3)
    (0.20, 0.60, 0.86, 0.92),   # B phase (4π/3)
    (0.70, 0.70, 0.70, 0.50),   # W (singlet, neutral)
]

# T₋ face colors (pastel/lighter) — anticolor phases
FACE_COLORS_MINUS = [
    (0.95, 0.58, 0.55, 0.88),   # R̄
    (0.51, 0.88, 0.67, 0.88),   # Ḡ
    (0.52, 0.76, 0.91, 0.88),   # B̄
    (0.85, 0.85, 0.85, 0.50),   # W̄
]

# ============================================================================
# STELLA OCTANGULA GEOMETRY
# ============================================================================

def stella_vertices():
    """
    Return T₊ and T₋ tetrahedra vertices on the unit sphere.

    T₊ vertices at (±1/√3, ±1/√3, ±1/√3) with even parity.
    T₋ = -T₊ (point inversion / charge conjugation).
    """
    s = 1.0 / np.sqrt(3)
    T_plus = np.array([
        [ s,  s,  s],   # vertex 0: R
        [ s, -s, -s],   # vertex 1: G
        [-s,  s, -s],   # vertex 2: B
        [-s, -s,  s],   # vertex 3: W
    ])
    T_minus = -T_plus
    return T_plus, T_minus


def tetra_faces():
    """
    Return the 4 face index triples for a tetrahedron.
    Face i is opposite vertex i.
    """
    return [
        [1, 2, 3],  # face 0: opposite vertex 0 (R) → colored R
        [0, 2, 3],  # face 1: opposite vertex 1 (G) → colored G
        [0, 1, 3],  # face 2: opposite vertex 2 (B) → colored B
        [0, 1, 2],  # face 3: opposite vertex 3 (W) → colored W
    ]


# ============================================================================
# SUBDIVISION AND BLENDING
# ============================================================================

def subdivide_triangle(v0, v1, v2, n_sub):
    """
    Subdivide triangle (v0, v1, v2) into n_sub² sub-triangles
    using barycentric coordinates.
    """
    vertices = []
    idx_map = {}

    for i in range(n_sub + 1):
        for j in range(n_sub + 1 - i):
            bary_a = i / n_sub
            bary_b = j / n_sub
            bary_c = 1.0 - bary_a - bary_b
            v = bary_a * v0 + bary_b * v1 + bary_c * v2
            idx_map[(i, j)] = len(vertices)
            vertices.append(v)

    faces = []
    for i in range(n_sub):
        for j in range(n_sub - i):
            faces.append([idx_map[(i, j)], idx_map[(i + 1, j)], idx_map[(i, j + 1)]])
            if i + j < n_sub - 1:
                faces.append([idx_map[(i + 1, j)], idx_map[(i + 1, j + 1)], idx_map[(i, j + 1)]])

    return np.array(vertices), np.array(faces)


def blend_to_sphere(vertices, t, R=1.0):
    """
    Spherification blend:  v(t) = (1-t) * v_flat + t * R * v̂

    t = 0: original flat polyhedron
    t = 1: all vertices projected to sphere of radius R
    """
    norms = np.linalg.norm(vertices, axis=1, keepdims=True)
    norms = np.maximum(norms, 1e-12)
    v_sphere = R * vertices / norms
    return (1.0 - t) * vertices + t * v_sphere


def get_original_edges(tetra):
    """Get the 6 edges of a tetrahedron for wireframe overlay."""
    edges = []
    for i in range(4):
        for j in range(i + 1, 4):
            edges.append((tetra[i], tetra[j]))
    return edges


def build_blended_mesh(t, n_sub=8):
    """
    Build the full stella octangula mesh at blending parameter t.
    Returns lists of (polygon_vertices, facecolor) for rendering,
    plus original edges for wireframe overlay.

    Since ∂S = ∂T₊ ⊔ ∂T₋ is a DISJOINT union, T₊ and T₋ project
    to separate concentric spheres at radii R₊ = 1.0 and R₋ = 0.92.
    This prevents z-fighting and visualizes the two-component topology.
    """
    T_plus, T_minus = stella_vertices()
    face_idx = tetra_faces()

    polys = []
    orig_edges = []

    # Two radii — disjoint union means separate surfaces
    radii = [1.0, 0.90]

    for tetra, colors, R in [(T_plus, FACE_COLORS_PLUS, radii[0]),
                              (T_minus, FACE_COLORS_MINUS, radii[1])]:
        for fi, face in enumerate(face_idx):
            v0, v1, v2 = tetra[face[0]], tetra[face[1]], tetra[face[2]]
            verts, sub_faces = subdivide_triangle(v0, v1, v2, n_sub)
            verts_blended = blend_to_sphere(verts, t, R=R)

            fc = colors[fi]
            for sf in sub_faces:
                tri = verts_blended[sf]
                polys.append((tri, fc))

        # Collect original tetrahedron edges (blended)
        for i in range(4):
            for j in range(i + 1, 4):
                edge_pts = np.array([
                    tetra[i] * (1 - s) + tetra[j] * s
                    for s in np.linspace(0, 1, 20)
                ])
                edge_blended = blend_to_sphere(edge_pts, t, R=R)
                orig_edges.append(edge_blended)

    return polys, orig_edges


# ============================================================================
# RENDERING
# ============================================================================

def render_panel(ax, t, n_sub=10, title=None):
    """Render one panel at blending parameter t."""

    polys, orig_edges = build_blended_mesh(t, n_sub=n_sub)

    # Edge visibility fades as geometry smooths
    # Subdivision mesh edges: very faint, fade fast
    sub_edge_alpha = max(0.0, (1.0 - t) ** 2) * 0.35
    sub_edge_lw = max(0.05, (1.0 - t) * 0.5)

    triangles = []
    facecolors = []

    for tri, fc in polys:
        triangles.append(tri)
        facecolors.append(fc)

    collection = Poly3DCollection(
        triangles,
        facecolors=facecolors,
        edgecolors=(0.2, 0.2, 0.2, sub_edge_alpha),
        linewidths=sub_edge_lw,
        zsort='average',
    )
    ax.add_collection3d(collection)

    # Draw original tetrahedron edges as bold wireframe overlay
    # These represent the discrete structure — they fade with t
    orig_edge_alpha = max(0.0, 1.0 - t) * 0.9
    orig_edge_lw = max(0.1, (1.0 - t) ** 0.5 * 2.5)
    for edge in orig_edges:
        ax.plot3D(
            edge[:, 0], edge[:, 1], edge[:, 2],
            color=(0.1, 0.1, 0.1, orig_edge_alpha),
            linewidth=orig_edge_lw,
            zorder=10,
        )

    # Styling
    lim = 0.72
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_zlim(-lim, lim)
    ax.set_box_aspect([1, 1, 1])
    ax.axis('off')

    # Camera angle — slight tilt to show both tetrahedra clearly
    ax.view_init(elev=20, azim=35)

    if title:
        ax.set_title(title, fontsize=10, fontweight='bold', pad=-4)


def generate_figure():
    """Generate the 4-panel geometry emergence figure."""

    plt.rcParams.update({
        'font.size': 10,
        'font.family': 'serif',
        'mathtext.fontset': 'dejavuserif',
    })

    fig = plt.figure(figsize=(13, 4.2))

    # Blending stages
    stages = [
        (0.00, r'$t = 0$: Discrete $\partial\mathcal{S}$'),
        (0.33, r'$t = 0.33$: Inflating'),
        (0.70, r'$t = 0.70$: Nearly smooth'),
        (1.00, r'$t = 1$: Continuous $S^2 \!\sqcup\! S^2$'),
    ]

    for i, (t, title) in enumerate(stages):
        ax = fig.add_subplot(1, 4, i + 1, projection='3d')
        n_sub = 14 if t > 0.5 else 8
        render_panel(ax, t, n_sub=n_sub, title=title)

    # Color legend at bottom
    legend_patches = [
        Patch(facecolor=FACE_COLORS_PLUS[0][:3], label=r'$R$ (phase $0$)'),
        Patch(facecolor=FACE_COLORS_PLUS[1][:3], label=r'$G$ (phase $2\pi/3$)'),
        Patch(facecolor=FACE_COLORS_PLUS[2][:3], label=r'$B$ (phase $4\pi/3$)'),
        Patch(facecolor=FACE_COLORS_MINUS[0][:3], edgecolor='gray',
              label=r'$\bar{R},\bar{G},\bar{B}$ ($T_-$)'),
    ]
    fig.legend(
        handles=legend_patches, loc='lower center', ncol=4,
        fontsize=8.5, frameon=True, framealpha=0.9,
        bbox_to_anchor=(0.5, -0.02),
    )

    # Master title with formula
    fig.suptitle(
        r'Geometry emerging from discrete structure:'
        r'$\quad\mathbf{v}(t) = (1{-}t)\,\mathbf{v}_{\mathrm{flat}}'
        r' + t\,R\,\hat{\mathbf{v}}$'
        r'$\qquad\mathbb{Z}_3$ color preserved $\forall\, t$',
        fontsize=11, y=1.01,
    )

    plt.tight_layout(rect=[0, 0.06, 1, 0.96])

    # Save
    png_path = OUTPUT_DIR / 'fig_geometry_emergence.png'
    pdf_path = OUTPUT_DIR / 'fig_geometry_emergence.pdf'

    plt.savefig(png_path, dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(pdf_path, bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")
    return png_path, pdf_path


# ============================================================================
# PHYSICS SUMMARY
# ============================================================================

def print_physics():
    """Print the mathematical content being visualized."""
    print("=" * 65)
    print("Geometry Emergence — Physics Summary")
    print("=" * 65)
    print()
    print("The continuum limit v(t) = (1-t)*v_flat + t*R*v̂ shows:")
    print()
    print("  t=0  : Stella octangula ∂S = ∂T₊ ⊔ ∂T₋")
    print("         8 flat triangular faces, 8 vertices, χ = 4")
    print("         Discrete O_h symmetry group (48 elements)")
    print()
    print("  t→1  : Two smooth S² (circumscribed spheres)")
    print("         Continuous SO(3) symmetry emerges")
    print("         Same χ = 4 (topological invariant)")
    print()
    print("  ∀ t  : Z₃ color structure preserved")
    print("         R (0), G (2π/3), B (4π/3) phases persist")
    print("         Center symmetry Z(SU(3)) = Z₃ is algebraic,")
    print("         not geometric — it cannot be smoothed away")
    print()
    print("  Key   : Bold wireframe edges dissolve (discrete → continuous)")
    print("         but colored faces persist (topology is eternal)")
    print("=" * 65)


if __name__ == "__main__":
    print_physics()
    generate_figure()
