#!/usr/bin/env python3
"""
Figure: Polyhedra Comparison Chart (Theorem 0.0.3 - Stella Uniqueness)

Compares candidate polyhedra for minimal geometric realization of SU(3).
Shows why the stella octangula is the unique 3D minimal geometric realization.

Key physics:
- Only stella octangula satisfies all constraints (GR1-GR3, MIN1-MIN3)
- Octahedron fails (GR1): can't separate fundamental/anti-fundamental
- Cube fails (GR2): wrong symmetry group (S₄ not S₃ × ℤ₂)
- Triangular prism fails (GR3): no antipodal symmetry
- 2D triangles fail (MIN2): no radial direction for confinement

Proof Document: docs/proofs/foundations/Theorem-0.0.3-Stella-Uniqueness.md
Paper Section: Section on SU(3) geometric realization uniqueness

Output: fig_thm_0_0_3_polyhedra_comparison.pdf, fig_thm_0_0_3_polyhedra_comparison.png
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
    'font.family': 'sans-serif',
    'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# Color palette
COLOR_PASS = '#40A040'      # Green for pass
COLOR_FAIL = '#C03030'      # Red for fail
COLOR_GOLD = '#FFD700'      # Gold for unique solution
COLOR_T_PLUS = '#2060B0'    # Blue for T+ tetrahedron
COLOR_T_MINUS = '#B03030'   # Red for T- tetrahedron
COLOR_NEUTRAL = '#707070'   # Gray for other polyhedra
COLOR_EDGE = '#303030'      # Dark for edges


def create_stella_octangula_vertices():
    """Return vertices of stella octangula (two dual tetrahedra)."""
    # T+ tetrahedron
    T_plus = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ]) / np.sqrt(3)

    # T- tetrahedron (dual, inverted)
    T_minus = np.array([
        [-1, -1, -1],
        [-1, 1, 1],
        [1, -1, 1],
        [1, 1, -1]
    ]) / np.sqrt(3)

    return T_plus, T_minus


def create_octahedron_vertices():
    """Return vertices of regular octahedron."""
    return np.array([
        [1, 0, 0], [-1, 0, 0],
        [0, 1, 0], [0, -1, 0],
        [0, 0, 1], [0, 0, -1]
    ])


def create_cube_vertices():
    """Return vertices of cube."""
    return np.array([
        [1, 1, 1], [1, 1, -1], [1, -1, 1], [1, -1, -1],
        [-1, 1, 1], [-1, 1, -1], [-1, -1, 1], [-1, -1, -1]
    ]) / np.sqrt(3)


def create_triangular_prism_vertices():
    """Return vertices of triangular prism."""
    h = 0.8  # height
    r = 0.7  # radius
    angles = [0, 2*np.pi/3, 4*np.pi/3]
    top = np.array([[r*np.cos(a), r*np.sin(a), h] for a in angles])
    bottom = np.array([[r*np.cos(a), r*np.sin(a), -h] for a in angles])
    return np.vstack([top, bottom])


def create_two_triangles_vertices():
    """Return vertices of two separate triangles (2D in 3D space)."""
    r = 0.8
    angles = [0, 2*np.pi/3, 4*np.pi/3]
    # Fundamental triangle
    T1 = np.array([[r*np.cos(a), r*np.sin(a), 0] for a in angles])
    # Anti-fundamental (inverted)
    T2 = np.array([[-r*np.cos(a), -r*np.sin(a), 0] for a in angles])
    return T1, T2


def draw_tetrahedron(ax, vertices, color, alpha=0.4, edge_color=None):
    """Draw a tetrahedron given 4 vertices."""
    if edge_color is None:
        edge_color = COLOR_EDGE

    # Define the 4 triangular faces
    faces = [
        [vertices[0], vertices[1], vertices[2]],
        [vertices[0], vertices[1], vertices[3]],
        [vertices[0], vertices[2], vertices[3]],
        [vertices[1], vertices[2], vertices[3]]
    ]

    # Add faces
    collection = Poly3DCollection(faces, alpha=alpha, facecolor=color,
                                   edgecolor=edge_color, linewidth=1)
    ax.add_collection3d(collection)

    # Draw vertices
    ax.scatter(*vertices.T, color=color, s=50, edgecolor='white', linewidth=1, zorder=5)


def draw_octahedron(ax, vertices, color=COLOR_NEUTRAL, alpha=0.4):
    """Draw an octahedron."""
    # 8 triangular faces
    faces_idx = [
        [0, 2, 4], [0, 4, 3], [0, 3, 5], [0, 5, 2],
        [1, 2, 4], [1, 4, 3], [1, 3, 5], [1, 5, 2]
    ]
    faces = [[vertices[i] for i in f] for f in faces_idx]

    collection = Poly3DCollection(faces, alpha=alpha, facecolor=color,
                                   edgecolor=COLOR_EDGE, linewidth=1)
    ax.add_collection3d(collection)
    ax.scatter(*vertices.T, color=color, s=50, edgecolor='white', linewidth=1, zorder=5)


def draw_cube(ax, vertices, color=COLOR_NEUTRAL, alpha=0.3):
    """Draw a cube."""
    # 6 square faces (as pairs of triangles)
    faces_idx = [
        [0, 1, 5, 4], [2, 3, 7, 6],  # front/back
        [0, 2, 6, 4], [1, 3, 7, 5],  # left/right
        [0, 1, 3, 2], [4, 5, 7, 6]   # top/bottom
    ]
    faces = [[vertices[i] for i in f] for f in faces_idx]

    collection = Poly3DCollection(faces, alpha=alpha, facecolor=color,
                                   edgecolor=COLOR_EDGE, linewidth=1)
    ax.add_collection3d(collection)
    ax.scatter(*vertices.T, color=color, s=50, edgecolor='white', linewidth=1, zorder=5)


def draw_triangular_prism(ax, vertices, color=COLOR_NEUTRAL, alpha=0.4):
    """Draw a triangular prism."""
    # 2 triangular faces + 3 rectangular faces
    faces = [
        [vertices[0], vertices[1], vertices[2]],  # top triangle
        [vertices[3], vertices[4], vertices[5]],  # bottom triangle
        [vertices[0], vertices[1], vertices[4], vertices[3]],  # side 1
        [vertices[1], vertices[2], vertices[5], vertices[4]],  # side 2
        [vertices[2], vertices[0], vertices[3], vertices[5]]   # side 3
    ]

    collection = Poly3DCollection(faces, alpha=alpha, facecolor=color,
                                   edgecolor=COLOR_EDGE, linewidth=1)
    ax.add_collection3d(collection)
    ax.scatter(*vertices.T, color=color, s=50, edgecolor='white', linewidth=1, zorder=5)


def draw_two_triangles(ax, T1, T2):
    """Draw two separate triangles."""
    # Triangle 1 (fundamental)
    faces1 = [[T1[0], T1[1], T1[2]]]
    collection1 = Poly3DCollection(faces1, alpha=0.5, facecolor=COLOR_T_PLUS,
                                    edgecolor=COLOR_EDGE, linewidth=1.5)
    ax.add_collection3d(collection1)
    ax.scatter(*T1.T, color=COLOR_T_PLUS, s=60, edgecolor='white', linewidth=1, zorder=5)

    # Triangle 2 (anti-fundamental)
    faces2 = [[T2[0], T2[1], T2[2]]]
    collection2 = Poly3DCollection(faces2, alpha=0.5, facecolor=COLOR_T_MINUS,
                                    edgecolor=COLOR_EDGE, linewidth=1.5)
    ax.add_collection3d(collection2)
    ax.scatter(*T2.T, color=COLOR_T_MINUS, s=60, edgecolor='white', linewidth=1, zorder=5)


def setup_3d_axes(ax, title):
    """Configure 3D axes for polyhedra visualization."""
    ax.set_xlim([-1.2, 1.2])
    ax.set_ylim([-1.2, 1.2])
    ax.set_zlim([-1.2, 1.2])
    ax.set_box_aspect([1, 1, 1])
    ax.set_title(title, fontsize=11, fontweight='bold', pad=10)

    # Clean up axes
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_zticks([])
    ax.xaxis.pane.fill = False
    ax.yaxis.pane.fill = False
    ax.zaxis.pane.fill = False
    ax.xaxis.pane.set_edgecolor('lightgray')
    ax.yaxis.pane.set_edgecolor('lightgray')
    ax.zaxis.pane.set_edgecolor('lightgray')
    ax.grid(True, alpha=0.3)


def main():
    """Generate the polyhedra comparison figure."""

    # Create figure: 2 rows, 3 columns for polyhedra + 1 column for table
    fig = plt.figure(figsize=(16, 10))

    # ==========================================================================
    # Top row: Polyhedra visualizations
    # ==========================================================================

    # Panel (a): Stella Octangula - THE SOLUTION
    ax1 = fig.add_subplot(2, 3, 1, projection='3d')
    T_plus, T_minus = create_stella_octangula_vertices()
    draw_tetrahedron(ax1, T_plus, COLOR_T_PLUS, alpha=0.5)
    draw_tetrahedron(ax1, T_minus, COLOR_T_MINUS, alpha=0.5)
    setup_3d_axes(ax1, '(a) Stella Octangula')
    ax1.view_init(elev=20, azim=45)
    # Add success indicator
    ax1.text2D(0.5, -0.05, '8 vertices, 12 edges', transform=ax1.transAxes,
               ha='center', fontsize=9, color=COLOR_PASS, fontweight='bold')

    # Panel (b): Octahedron - FAILS
    ax2 = fig.add_subplot(2, 3, 2, projection='3d')
    oct_verts = create_octahedron_vertices()
    draw_octahedron(ax2, oct_verts, COLOR_NEUTRAL, alpha=0.4)
    setup_3d_axes(ax2, '(b) Octahedron')
    ax2.view_init(elev=20, azim=45)
    ax2.text2D(0.5, -0.05, '6 vertices, 12 edges', transform=ax2.transAxes,
               ha='center', fontsize=9, color=COLOR_FAIL, fontweight='bold')

    # Panel (c): Cube - FAILS
    ax3 = fig.add_subplot(2, 3, 3, projection='3d')
    cube_verts = create_cube_vertices()
    draw_cube(ax3, cube_verts, COLOR_NEUTRAL, alpha=0.3)
    setup_3d_axes(ax3, '(c) Cube')
    ax3.view_init(elev=20, azim=45)
    ax3.text2D(0.5, -0.05, '8 vertices, 12 edges', transform=ax3.transAxes,
               ha='center', fontsize=9, color=COLOR_FAIL, fontweight='bold')

    # Panel (d): Triangular Prism - FAILS
    ax4 = fig.add_subplot(2, 3, 4, projection='3d')
    prism_verts = create_triangular_prism_vertices()
    draw_triangular_prism(ax4, prism_verts, COLOR_NEUTRAL, alpha=0.4)
    setup_3d_axes(ax4, '(d) Triangular Prism')
    ax4.view_init(elev=20, azim=45)
    ax4.text2D(0.5, -0.05, '6 vertices, 9 edges', transform=ax4.transAxes,
               ha='center', fontsize=9, color=COLOR_FAIL, fontweight='bold')

    # Panel (e): Two Triangles (2D) - FAILS
    ax5 = fig.add_subplot(2, 3, 5, projection='3d')
    T1, T2 = create_two_triangles_vertices()
    draw_two_triangles(ax5, T1, T2)
    setup_3d_axes(ax5, '(e) Two Triangles (2D)')
    ax5.view_init(elev=60, azim=45)  # Top-down-ish view to show 2D nature
    ax5.text2D(0.5, -0.05, '6 vertices (2D only)', transform=ax5.transAxes,
               ha='center', fontsize=9, color=COLOR_FAIL, fontweight='bold')

    # ==========================================================================
    # Panel (f): Comparison Table
    # ==========================================================================
    ax6 = fig.add_subplot(2, 3, 6)
    ax6.axis('off')

    # Table data from Theorem 0.0.3 Section 2.5
    polyhedra = [
        'Stella Octangula',
        'Octahedron',
        'Cube',
        'Triangular Prism',
        'Two Triangles (2D)',
        'Two Tetrahedra\n(separate)'
    ]

    # Criteria satisfaction matrix
    # [GR1, GR2, GR3, MIN1, MIN2, MIN3]
    # GR1: Weight correspondence (vertices → weights)
    # GR2: Symmetry preservation (S₃ action)
    # GR3: Conjugation compatibility (antipodal)
    # MIN1: Vertex minimality
    # MIN2: 3D embedding
    # MIN3: Edge minimality

    satisfaction = [
        [True, True, True, True, True, True],     # Stella Octangula - ALL PASS
        [False, True, True, True, True, False],   # Octahedron - fails GR1, edges
        [False, False, True, True, True, True],   # Cube - fails GR1, GR2
        [False, False, False, True, True, False], # Triangular Prism - fails GR1, GR2, GR3
        [True, True, True, True, False, True],    # Two Triangles - fails MIN2 (2D only)
        [True, True, True, True, True, False],    # Two separate Tetrahedra - not connected
    ]

    failure_reasons = [
        'UNIQUE SOLUTION',
        'Fails GR1: can\'t separate\nfund/anti-fund',
        'Fails GR2: wrong symmetry\n(S₄ not S₃ × Z₂)',
        'Fails GR3: no antipodal\nsymmetry',
        'Fails MIN2: no radial\ndirection (2D only)',
        'Not a single connected\npolyhedral complex'
    ]

    criteria = ['GR1', 'GR2', 'GR3', 'MIN1', 'MIN2', 'MIN3']

    # Draw table
    cell_width = 0.09
    cell_height = 0.12
    start_x = 0.25
    start_y = 0.92

    # Header row
    ax6.text(start_x - 0.15, start_y + 0.05, 'Polyhedron', fontsize=10,
             fontweight='bold', ha='left')
    for i, criterion in enumerate(criteria):
        ax6.text(start_x + (i + 0.5) * cell_width, start_y + 0.05, criterion,
                 fontsize=9, ha='center', fontweight='bold')
    ax6.text(start_x + 6.5 * cell_width + 0.05, start_y + 0.05, 'Result',
             fontsize=10, fontweight='bold', ha='center')

    # Data rows
    for row_idx, (poly, sat, reason) in enumerate(zip(polyhedra, satisfaction, failure_reasons)):
        y = start_y - (row_idx + 0.5) * cell_height

        # Polyhedron name
        is_solution = row_idx == 0
        color = COLOR_T_PLUS if is_solution else 'black'
        weight = 'bold' if is_solution else 'normal'
        ax6.text(start_x - 0.15, y, poly, fontsize=9, ha='left', va='center',
                 color=color, fontweight=weight)

        # Criteria cells
        for col_idx, passed in enumerate(sat):
            x = start_x + (col_idx + 0.5) * cell_width

            if passed:
                bg_color = '#90EE90' if not is_solution else COLOR_PASS
                symbol = '✓'
                text_color = 'darkgreen' if not is_solution else 'white'
            else:
                bg_color = '#FFB0B0'
                symbol = '✗'
                text_color = 'darkred'

            rect = plt.Rectangle((x - cell_width/2, y - cell_height/2.5),
                                  cell_width, cell_height * 0.8,
                                  facecolor=bg_color, edgecolor='gray', linewidth=0.5)
            ax6.add_patch(rect)
            ax6.text(x, y, symbol, fontsize=12, ha='center', va='center',
                     color=text_color, fontweight='bold')

        # Result column
        result_x = start_x + 6.5 * cell_width + 0.05
        if is_solution:
            rect = plt.Rectangle((result_x - cell_width * 0.9, y - cell_height/2.5),
                                  cell_width * 1.8, cell_height * 0.8,
                                  facecolor=COLOR_GOLD, edgecolor='#B8860B', linewidth=2)
            ax6.add_patch(rect)
            ax6.text(result_x, y, '✓ UNIQUE', fontsize=9, ha='center', va='center',
                     color='black', fontweight='bold')
        else:
            ax6.text(result_x, y, reason, fontsize=7, ha='center', va='center',
                     color=COLOR_FAIL, style='italic')

    # Add legend for criteria
    legend_y = 0.08
    criteria_explanations = [
        '(GR1) Weight Correspondence: vertices map to SU(3) weights',
        '(GR2) Symmetry Preservation: automorphisms respect S₃ Weyl action',
        '(GR3) Conjugation Compatibility: charge conjugation as geometric involution',
        '(MIN1) Vertex Minimality: minimum vertices for SU(3) weights',
        '(MIN2) Dimension: 3D embedding (Physical Hypothesis 0.0.0f)',
        '(MIN3) Edge Minimality: minimum edges for connectivity'
    ]

    for i, expl in enumerate(criteria_explanations):
        ax6.text(0.02, legend_y - i * 0.04, expl, fontsize=8, ha='left', va='top',
                 transform=ax6.transAxes)

    ax6.set_xlim(0, 1)
    ax6.set_ylim(-0.2, 1.1)
    ax6.set_title('(f) Criteria Satisfaction Matrix', fontsize=11, fontweight='bold')

    # ==========================================================================
    # Main title
    # ==========================================================================
    fig.suptitle('Theorem 0.0.3: Stella Octangula Uniqueness — Polyhedra Comparison',
                 fontsize=14, fontweight='bold', y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.96])

    # Save figures
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_3_polyhedra_comparison.png',
                dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_3_polyhedra_comparison.pdf',
                bbox_inches='tight', facecolor='white')
    plt.close()

    print("Figure saved successfully!")
    print(f"Output: {OUTPUT_DIR}/fig_thm_0_0_3_polyhedra_comparison.png")
    print(f"Output: {OUTPUT_DIR}/fig_thm_0_0_3_polyhedra_comparison.pdf")
    print()
    print("Key physics illustrated:")
    print("  - Stella octangula (a): Two interpenetrating tetrahedra T₊ ∪ T₋")
    print("    8 vertices = 6 weights (3⊕3̄) + 2 apex (singlet direction)")
    print("  - Octahedron (b): 6 vertices can't separate fund/anti-fund (fails GR1)")
    print("  - Cube (c): Wrong symmetry S₄ instead of S₃ × Z₂ (fails GR2)")
    print("  - Triangular prism (d): No antipodal symmetry (fails GR3)")
    print("  - Two triangles (e): 2D only, no radial direction (fails MIN2)")
    print("  - Stella octangula is the UNIQUE minimal 3D geometric realization of SU(3)")


if __name__ == '__main__':
    main()
