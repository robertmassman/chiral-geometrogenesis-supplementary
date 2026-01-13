#!/usr/bin/env python3
"""
Theorem 0.0.3b Visualization: Completeness of Geometric Realization Classification
==================================================================================

Creates visualization plots demonstrating:
1. SU(3) weight diagram for 3⊕3̄ representation
2. Polyhedra classification showing which satisfy GR1-GR3
3. Tetrahemihexahedron exclusion via symmetry incompatibility
4. Stella octangula as unique solution

Output: verification/plots/theorem_0_0_3b_completeness.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, FancyArrowPatch, Circle, RegularPolygon
from matplotlib.collections import PatchCollection
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import matplotlib.gridspec as gridspec

# Set up nice plotting style
plt.rcParams['font.size'] = 10
plt.rcParams['axes.titlesize'] = 12
plt.rcParams['axes.labelsize'] = 10
plt.rcParams['figure.facecolor'] = 'white'


def plot_su3_weight_diagram(ax):
    """
    Plot the SU(3) weight diagram for the 3⊕3̄ representation.

    The 6 weights form two triangles (3 and 3̄) that are related by
    charge conjugation (negation).
    """
    ax.set_title('SU(3) Weight Diagram: $\\mathbf{3} \\oplus \\bar{\\mathbf{3}}$', fontsize=12, fontweight='bold')

    # SU(3) fundamental weights (in Cartan subalgebra coordinates)
    # Using standard normalization where weights form equilateral triangle
    sqrt3 = np.sqrt(3)

    # Fundamental representation (3) weights
    w_R = np.array([0.5, 1/(2*sqrt3)])
    w_G = np.array([-0.5, 1/(2*sqrt3)])
    w_B = np.array([0, -1/sqrt3])

    # Anti-fundamental (3̄) weights = negatives
    w_R_bar = -w_R
    w_G_bar = -w_G
    w_B_bar = -w_B

    # Plot the weight diagram
    colors_3 = ['#e74c3c', '#27ae60', '#3498db']  # R, G, B
    colors_3bar = ['#c0392b', '#1e8449', '#2874a6']  # darker versions
    labels_3 = ['$\\vec{w}_R$', '$\\vec{w}_G$', '$\\vec{w}_B$']
    labels_3bar = ['$-\\vec{w}_R$', '$-\\vec{w}_G$', '$-\\vec{w}_B$']

    weights_3 = [w_R, w_G, w_B]
    weights_3bar = [w_R_bar, w_G_bar, w_B_bar]

    # Draw triangles connecting weights
    triangle_3 = plt.Polygon([w_R, w_G, w_B], fill=True, alpha=0.2,
                              facecolor='blue', edgecolor='blue', linewidth=2)
    triangle_3bar = plt.Polygon([w_R_bar, w_G_bar, w_B_bar], fill=True, alpha=0.2,
                                 facecolor='red', edgecolor='red', linewidth=2)
    ax.add_patch(triangle_3)
    ax.add_patch(triangle_3bar)

    # Plot weight points
    for w, c, label in zip(weights_3, colors_3, labels_3):
        ax.scatter(w[0], w[1], c=c, s=150, zorder=5, edgecolors='black', linewidths=1.5)
        ax.annotate(label, (w[0], w[1]), xytext=(10, 10),
                   textcoords='offset points', fontsize=11, fontweight='bold')

    for w, c, label in zip(weights_3bar, colors_3bar, labels_3bar):
        ax.scatter(w[0], w[1], c=c, s=150, zorder=5, edgecolors='black', linewidths=1.5, marker='s')
        ax.annotate(label, (w[0], w[1]), xytext=(10, -15),
                   textcoords='offset points', fontsize=11, fontweight='bold')

    # Plot origin
    ax.scatter(0, 0, c='gray', s=80, marker='x', zorder=5, linewidths=2)
    ax.annotate('$\\vec{0}$', (0, 0), xytext=(-20, -15), textcoords='offset points', fontsize=10)

    # Draw charge conjugation arrows
    for w3, w3bar in zip(weights_3, weights_3bar):
        ax.annotate('', xy=w3bar, xytext=w3,
                   arrowprops=dict(arrowstyle='->', color='purple', alpha=0.5,
                                  connectionstyle='arc3,rad=0.2', lw=1.5))

    # Add root vectors (optional - shows S_3 action)
    ax.arrow(0, 0, 0.4, 0, head_width=0.03, head_length=0.02, fc='gray', ec='gray', alpha=0.5)
    ax.arrow(0, 0, -0.2, 0.35, head_width=0.03, head_length=0.02, fc='gray', ec='gray', alpha=0.5)

    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.8, 0.8)
    ax.set_aspect('equal')
    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.3)
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.3)
    ax.set_xlabel('$h_1^*$ (Cartan coordinate)')
    ax.set_ylabel('$h_2^*$ (Cartan coordinate)')

    # Legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='blue',
               markersize=10, label='$\\mathbf{3}$ (fundamental)'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='red',
               markersize=10, label='$\\bar{\\mathbf{3}}$ (anti-fundamental)'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=9)

    # Add multiplicity note
    ax.text(0.02, 0.98, 'Each weight has\nmultiplicity 1', transform=ax.transAxes,
           fontsize=9, verticalalignment='top', bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))


def plot_polyhedra_classification(ax):
    """
    Create a classification chart showing which polyhedra satisfy GR1-GR3.
    """
    ax.set_title('Polyhedra Classification by GR Conditions', fontsize=12, fontweight='bold')
    ax.axis('off')

    # Data: polyhedron name, vertices, GR1, GR2, GR3, MIN1, result
    data = [
        ('Tetrahedron', 4, False, True, False, False, 'FAIL'),
        ('Cube', 8, True, False, True, True, 'FAIL'),
        ('Octahedron', 6, False, False, True, False, 'FAIL'),
        ('Stella Octangula', 8, True, True, True, True, 'PASS'),
        ('Tetrahemihexahedron', 6, False, True, False, False, 'FAIL'),
        ('Sm. Stellated Dodeca.', 12, True, False, True, False, 'FAIL'),
        ('Great Stellated Dodeca.', 20, True, False, True, False, 'FAIL'),
        ('Compound 3 Tetra.', 12, True, False, True, False, 'FAIL'),
    ]

    # Create table
    col_labels = ['Polyhedron', 'V', 'GR1', 'GR2', 'GR3', 'MIN1', 'Result']
    cell_colors = []
    cell_text = []

    for row in data:
        name, v, gr1, gr2, gr3, min1, result = row
        row_colors = ['white']
        row_text = [name, str(v)]

        for val in [gr1, gr2, gr3, min1]:
            if val:
                row_text.append('✓')
                row_colors.append('#d4edda')  # light green
            else:
                row_text.append('✗')
                row_colors.append('#f8d7da')  # light red

        if result == 'PASS':
            row_text.append('✓ PASS')
            row_colors.append('#28a745')  # green
        else:
            row_text.append('✗ FAIL')
            row_colors.append('#dc3545')  # red

        cell_text.append(row_text)
        # Pad colors for all columns
        while len(row_colors) < len(col_labels):
            row_colors.append('white')
        cell_colors.append(row_colors[:len(col_labels)])

    table = ax.table(cellText=cell_text,
                     colLabels=col_labels,
                     cellColours=cell_colors,
                     cellLoc='center',
                     loc='center',
                     bbox=[0, 0.1, 1, 0.85])

    table.auto_set_font_size(False)
    table.set_fontsize(9)
    table.scale(1, 1.5)

    # Style header
    for j in range(len(col_labels)):
        table[(0, j)].set_facecolor('#4a90d9')
        table[(0, j)].set_text_props(color='white', fontweight='bold')

    # Highlight stella octangula row
    for j in range(len(col_labels)):
        table[(4, j)].set_facecolor('#d4edda')

    ax.text(0.5, 0.02, 'Only the stella octangula satisfies all conditions',
           transform=ax.transAxes, ha='center', fontsize=10, fontweight='bold',
           bbox=dict(boxstyle='round', facecolor='#d4edda', alpha=0.8))


def plot_tetrahemihexahedron_exclusion(ax):
    """
    Visualize why the tetrahemihexahedron fails GR2.

    Shows the T_d symmetry group action mixing positive and negative weights.
    """
    ax.set_title('Tetrahemihexahedron: GR2 Failure', fontsize=12, fontweight='bold')

    # Tetrahemihexahedron has octahedron vertices
    vertices = np.array([
        [1, 0, 0],   # +x
        [-1, 0, 0],  # -x
        [0, 1, 0],   # +y
        [0, -1, 0],  # -y
        [0, 0, 1],   # +z
        [0, 0, -1]   # -z
    ])

    # Plot vertices
    colors = ['red', 'darkred', 'green', 'darkgreen', 'blue', 'darkblue']
    labels = ['+x', '-x', '+y', '-y', '+z', '-z']
    weight_labels = ['$w_R$', '$-w_R$', '$w_G$', '$-w_G$', '$w_B$', '$-w_B$']

    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)

    # Draw octahedron edges (project to 2D using isometric-ish view)
    # Using projection: x' = x - 0.5*z, y' = y - 0.5*z
    proj = lambda v: (v[0] - 0.3*v[2], v[1] - 0.3*v[2])

    # Draw edges of octahedron
    edges = [
        (0, 2), (0, 3), (0, 4), (0, 5),  # +x to others
        (1, 2), (1, 3), (1, 4), (1, 5),  # -x to others
        (2, 4), (2, 5), (3, 4), (3, 5)   # remaining
    ]

    for i, j in edges:
        p1 = proj(vertices[i])
        p2 = proj(vertices[j])
        ax.plot([p1[0], p2[0]], [p1[1], p2[1]], 'k-', alpha=0.3, linewidth=1)

    # Plot projected vertices
    for i, (v, c, l, wl) in enumerate(zip(vertices, colors, labels, weight_labels)):
        p = proj(v)
        ax.scatter(p[0], p[1], c=c, s=200, zorder=5, edgecolors='black', linewidths=2)
        ax.annotate(f'{l}\n{wl}', p, xytext=(15, 5), textcoords='offset points', fontsize=9)

    # Show the problematic rotation R_2 (swaps +x ↔ -y)
    p_px = proj(vertices[0])  # +x
    p_my = proj(vertices[3])  # -y

    ax.annotate('', xy=p_my, xytext=p_px,
               arrowprops=dict(arrowstyle='<->', color='purple', lw=2,
                              connectionstyle='arc3,rad=0.3'))
    ax.text((p_px[0] + p_my[0])/2 + 0.3, (p_px[1] + p_my[1])/2,
           '$R_2$', fontsize=11, color='purple', fontweight='bold')

    # Explanation box
    explanation = (
        "Under $R_2$: +x ↔ -y\n"
        "GR2 requires: $\\iota(-y) = \\phi(R_2) \\cdot w_R$\n"
        "But $\\phi(R_2) \\cdot w_R \\in \\{w_R, w_G, w_B\\}$\n"
        "GR3 requires: $\\iota(-y) = -w_G$\n"
        "Contradiction! $-w_G \\notin \\{w_R, w_G, w_B\\}$"
    )
    ax.text(0.02, 0.02, explanation, transform=ax.transAxes, fontsize=8,
           verticalalignment='bottom', bbox=dict(boxstyle='round', facecolor='#f8d7da', alpha=0.9))

    ax.set_aspect('equal')
    ax.axis('off')


def plot_stella_octangula_3d(ax):
    """
    Plot the stella octangula showing its structure as two interpenetrating tetrahedra.
    """
    ax.set_title('Stella Octangula: Unique Solution', fontsize=12, fontweight='bold')

    # Stella octangula vertices (two tetrahedra)
    # Tetrahedron 1 (fundamental 3)
    tet1 = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ]) / np.sqrt(3)

    # Tetrahedron 2 (anti-fundamental 3̄)
    tet2 = -tet1

    # Colors for weight labels
    colors_1 = ['#e74c3c', '#27ae60', '#3498db', '#95a5a6']  # R, G, B, apex
    colors_2 = ['#c0392b', '#1e8449', '#2874a6', '#7f8c8d']  # R̄, Ḡ, B̄, apex

    # Plot tetrahedron 1
    faces1 = [
        [tet1[0], tet1[1], tet1[2]],
        [tet1[0], tet1[1], tet1[3]],
        [tet1[0], tet1[2], tet1[3]],
        [tet1[1], tet1[2], tet1[3]]
    ]

    poly1 = Poly3DCollection(faces1, alpha=0.3, facecolor='blue', edgecolor='blue', linewidth=1)
    ax.add_collection3d(poly1)

    # Plot tetrahedron 2
    faces2 = [
        [tet2[0], tet2[1], tet2[2]],
        [tet2[0], tet2[1], tet2[3]],
        [tet2[0], tet2[2], tet2[3]],
        [tet2[1], tet2[2], tet2[3]]
    ]

    poly2 = Poly3DCollection(faces2, alpha=0.3, facecolor='red', edgecolor='red', linewidth=1)
    ax.add_collection3d(poly2)

    # Plot vertices
    labels_1 = ['$w_R$', '$w_G$', '$w_B$', 'apex']
    labels_2 = ['$-w_R$', '$-w_G$', '$-w_B$', 'apex']

    for v, c, l in zip(tet1, colors_1[:3], labels_1[:3]):
        ax.scatter(*v, c=c, s=100, edgecolors='black', linewidths=1.5)

    for v, c, l in zip(tet2, colors_2[:3], labels_2[:3]):
        ax.scatter(*v, c=c, s=100, edgecolors='black', linewidths=1.5, marker='s')

    # Set axis properties
    ax.set_xlim([-1, 1])
    ax.set_ylim([-1, 1])
    ax.set_zlim([-1, 1])
    ax.set_xlabel('X')
    ax.set_ylabel('Y')
    ax.set_zlabel('Z')

    # Remove tick labels for cleaner look
    ax.set_xticklabels([])
    ax.set_yticklabels([])
    ax.set_zticklabels([])

    # Add text annotation
    ax.text2D(0.02, 0.98,
             "8 vertices\n6 non-zero weights\n2 apex vertices\nS₃ × Z₂ symmetry",
             transform=ax.transAxes, fontsize=9, verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='#d4edda', alpha=0.8))


def plot_exclusion_flowchart(ax):
    """
    Create a flowchart showing the exclusion logic for different structure types.
    """
    ax.set_title('Exclusion Logic Flowchart', fontsize=12, fontweight='bold')
    ax.axis('off')
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)

    # Boxes
    def add_box(x, y, text, color='white', width=2.2, height=0.8):
        rect = plt.Rectangle((x - width/2, y - height/2), width, height,
                             facecolor=color, edgecolor='black', linewidth=1.5)
        ax.add_patch(rect)
        ax.text(x, y, text, ha='center', va='center', fontsize=8, wrap=True)

    # Start
    add_box(5, 9.5, 'All Structures', color='#4a90d9')

    # First branch: finite vs infinite
    ax.annotate('', xy=(3, 8), xytext=(5, 9),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    ax.annotate('', xy=(7, 8), xytext=(5, 9),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))

    add_box(3, 8, 'Finite |V|', color='#e8f4fd')
    add_box(7, 8, 'Infinite |V|', color='#fce4e4')

    # Infinite branch exclusion
    ax.annotate('', xy=(7, 6.5), xytext=(7, 7.5),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    add_box(7, 6.5, '❌ Excluded\n(Lemma 5.1)', color='#f8d7da', height=1)

    ax.text(8.5, 7.2, '3⊕3̄ is 6-dim\nwith mult. 1', fontsize=7, style='italic')

    # Finite branch: convex vs non-convex
    ax.annotate('', xy=(1.5, 6.5), xytext=(3, 7.5),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    ax.annotate('', xy=(4.5, 6.5), xytext=(3, 7.5),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))

    add_box(1.5, 6.5, 'Convex\n(Platonic)', color='#e8f4fd', height=1)
    add_box(4.5, 6.5, 'Non-convex\n(K-P, uniform)', color='#e8f4fd', height=1)

    # Convex exclusion
    ax.annotate('', xy=(1.5, 5), xytext=(1.5, 6),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    add_box(1.5, 5, '❌ Excluded\n(Wrong V or Sym)', color='#f8d7da', height=1)

    # Non-convex split
    ax.annotate('', xy=(3.5, 5), xytext=(4.5, 6),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    ax.annotate('', xy=(5.5, 5), xytext=(4.5, 6),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))

    add_box(3.5, 5, 'V ≠ 8', color='#fce4e4', height=0.7)
    add_box(5.5, 5, 'V = 8', color='#d4edda', height=0.7)

    # V ≠ 8 exclusion
    ax.annotate('', xy=(3.5, 4), xytext=(3.5, 4.6),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    add_box(3.5, 4, '❌ Excluded\n(MIN1)', color='#f8d7da', height=0.8)

    # V = 8 check
    ax.annotate('', xy=(5.5, 4), xytext=(5.5, 4.6),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    add_box(5.5, 4, 'Check GR2\n(S₃ symmetry)', color='#fff3cd', height=0.8)

    # Final outcomes
    ax.annotate('', xy=(4.5, 2.8), xytext=(5.5, 3.5),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    ax.annotate('', xy=(6.5, 2.8), xytext=(5.5, 3.5),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))

    add_box(4.5, 2.8, '❌ Cube\n(O_h ≠ S₃)', color='#f8d7da', height=0.8)
    add_box(6.5, 2.8, '✓ Stella\nOctangula', color='#28a745', height=0.8)

    # Final box
    add_box(5.5, 1.2, 'UNIQUE SOLUTION', color='#28a745', width=3, height=0.6)
    ax.annotate('', xy=(5.5, 1.5), xytext=(6.5, 2.4),
               arrowprops=dict(arrowstyle='->', color='green', lw=2))


def create_comprehensive_figure():
    """
    Create the comprehensive visualization figure.
    """
    fig = plt.figure(figsize=(16, 12))

    # Create grid
    gs = gridspec.GridSpec(2, 3, figure=fig, height_ratios=[1, 1],
                          width_ratios=[1, 1, 1], hspace=0.3, wspace=0.3)

    # Plot 1: SU(3) weight diagram (top left)
    ax1 = fig.add_subplot(gs[0, 0])
    plot_su3_weight_diagram(ax1)

    # Plot 2: Polyhedra classification table (top middle)
    ax2 = fig.add_subplot(gs[0, 1])
    plot_polyhedra_classification(ax2)

    # Plot 3: Tetrahemihexahedron exclusion (top right)
    ax3 = fig.add_subplot(gs[0, 2])
    plot_tetrahemihexahedron_exclusion(ax3)

    # Plot 4: Stella octangula 3D (bottom left)
    ax4 = fig.add_subplot(gs[1, 0], projection='3d')
    plot_stella_octangula_3d(ax4)

    # Plot 5: Exclusion flowchart (bottom middle + right)
    ax5 = fig.add_subplot(gs[1, 1:])
    plot_exclusion_flowchart(ax5)

    # Main title
    fig.suptitle('Theorem 0.0.3b: Completeness of Geometric Realization Classification\n'
                'The stella octangula is the UNIQUE minimal geometric realization of SU(3)',
                fontsize=14, fontweight='bold', y=0.98)

    # Save
    output_path = 'verification/plots/theorem_0_0_3b_completeness.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")

    plt.close()
    return output_path


def create_weight_multiplicity_plot():
    """
    Create a separate plot focusing on weight multiplicities.
    """
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Left: 3⊕3̄ has multiplicity 1
    ax1 = axes[0]
    ax1.set_title('$\\mathbf{3} \\oplus \\bar{\\mathbf{3}}$: Non-degenerate Weights', fontsize=12, fontweight='bold')

    weights = ['$w_R$', '$w_G$', '$w_B$', '$-w_R$', '$-w_G$', '$-w_B$']
    multiplicities = [1, 1, 1, 1, 1, 1]
    colors = ['#e74c3c', '#27ae60', '#3498db', '#c0392b', '#1e8449', '#2874a6']

    bars = ax1.bar(weights, multiplicities, color=colors, edgecolor='black', linewidth=1.5)
    ax1.set_ylabel('Multiplicity', fontsize=11)
    ax1.set_xlabel('Weight', fontsize=11)
    ax1.set_ylim(0, 2.5)
    ax1.axhline(y=1, color='green', linestyle='--', alpha=0.7, label='All mult. = 1')
    ax1.legend()

    # Add annotation
    ax1.text(0.5, 0.95, 'Each non-zero weight has\nmultiplicity exactly 1\n→ At most 6 vertices with\nnon-zero weight labels',
            transform=ax1.transAxes, ha='center', va='top', fontsize=10,
            bbox=dict(boxstyle='round', facecolor='#d4edda', alpha=0.8))

    # Right: Comparison with adjoint
    ax2 = axes[1]
    ax2.set_title('Adjoint ($\\mathbf{8}$): Has Degenerate Zero Weight', fontsize=12, fontweight='bold')

    weights_adj = ['$\\alpha_1$', '$\\alpha_2$', '$\\alpha_1+\\alpha_2$',
                   '$-\\alpha_1$', '$-\\alpha_2$', '$-(\\alpha_1+\\alpha_2)$', '$0$']
    mult_adj = [1, 1, 1, 1, 1, 1, 2]
    colors_adj = ['#e74c3c', '#27ae60', '#3498db', '#c0392b', '#1e8449', '#2874a6', '#95a5a6']

    bars2 = ax2.bar(weights_adj, mult_adj, color=colors_adj, edgecolor='black', linewidth=1.5)
    ax2.set_ylabel('Multiplicity', fontsize=11)
    ax2.set_xlabel('Weight (root notation)', fontsize=11)
    ax2.set_ylim(0, 2.5)
    ax2.axhline(y=1, color='red', linestyle='--', alpha=0.7, label='Degeneracy at 0')
    ax2.legend()
    ax2.tick_params(axis='x', rotation=45)

    # Highlight the degenerate weight
    bars2[-1].set_edgecolor('red')
    bars2[-1].set_linewidth(3)

    ax2.text(0.5, 0.95, 'Zero weight has multiplicity 2\nin adjoint representation\n(Cartan subalgebra)',
            transform=ax2.transAxes, ha='center', va='top', fontsize=10,
            bbox=dict(boxstyle='round', facecolor='#fce4e4', alpha=0.8))

    fig.suptitle('Weight Multiplicities: Key to Infinite Structure Exclusion',
                fontsize=13, fontweight='bold', y=1.02)

    plt.tight_layout()
    output_path = 'verification/plots/theorem_0_0_3b_weight_multiplicities.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")

    plt.close()
    return output_path


def main():
    """Generate all visualization plots for Theorem 0.0.3b."""
    print("=" * 70)
    print("THEOREM 0.0.3b VISUALIZATION")
    print("Completeness of Geometric Realization Classification")
    print("=" * 70)

    # Create main comprehensive figure
    path1 = create_comprehensive_figure()

    # Create weight multiplicity comparison
    path2 = create_weight_multiplicity_plot()

    print("\n" + "=" * 70)
    print("VISUALIZATION COMPLETE")
    print("=" * 70)
    print(f"\nGenerated plots:")
    print(f"  1. {path1}")
    print(f"  2. {path2}")

    return [path1, path2]


if __name__ == "__main__":
    main()
