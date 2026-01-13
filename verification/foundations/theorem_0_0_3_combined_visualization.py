#!/usr/bin/env python3
"""
Theorem 0.0.3 & 0.0.3b Combined Visualization
==============================================

Creates comprehensive visualization for:
- Theorem 0.0.3: Stella Octangula as Unique Minimal Geometric Realization of SU(3)
- Theorem 0.0.3b: Completeness of Geometric Realization Classification

Key visual elements:
1. SU(3) weight diagram (3⊕3̄ representation)
2. 3D stella octangula structure (dual interpenetrating tetrahedra)
3. Polyhedra classification and elimination table
4. Completeness proof flowchart
5. Apex vertex physical interpretation

Output: verification/plots/theorem_0_0_3_combined.png

Author: Verification Agent
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, FancyArrowPatch, Circle, Rectangle, FancyBboxPatch
from matplotlib.collections import PatchCollection
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import matplotlib.gridspec as gridspec

# Set up nice plotting style
plt.rcParams['font.size'] = 10
plt.rcParams['axes.titlesize'] = 12
plt.rcParams['axes.labelsize'] = 10
plt.rcParams['figure.facecolor'] = 'white'


def plot_su3_weight_diagram_enhanced(ax):
    """
    Enhanced SU(3) weight diagram for 3⊕3̄ representation.
    Shows the fundamental and anti-fundamental triangles with
    clear color coding and charge conjugation relation.
    """
    ax.set_title('SU(3) Weight Diagram: $\\mathbf{3} \\oplus \\bar{\\mathbf{3}}$\n(6 Non-Zero Weights)', 
                 fontsize=11, fontweight='bold')

    # SU(3) fundamental weights (in Cartan-Weyl coordinates)
    sqrt3 = np.sqrt(3)

    # Fundamental representation (3) weights
    w_R = np.array([0.5, 1/(2*sqrt3)])
    w_G = np.array([-0.5, 1/(2*sqrt3)])
    w_B = np.array([0, -1/sqrt3])

    # Anti-fundamental (3̄) weights = negatives
    w_R_bar = -w_R
    w_G_bar = -w_G
    w_B_bar = -w_B

    # Draw triangles connecting weights
    triangle_3 = plt.Polygon([w_R, w_G, w_B], fill=True, alpha=0.15,
                              facecolor='blue', edgecolor='blue', linewidth=2.5,
                              linestyle='-', label='Fundamental $\\mathbf{3}$')
    triangle_3bar = plt.Polygon([w_R_bar, w_G_bar, w_B_bar], fill=True, alpha=0.15,
                                 facecolor='red', edgecolor='red', linewidth=2.5,
                                 linestyle='--', label='Anti-fund. $\\bar{\\mathbf{3}}$')
    ax.add_patch(triangle_3)
    ax.add_patch(triangle_3bar)

    # Draw edges from apex projection point (origin) to all weights
    for w in [w_R, w_G, w_B]:
        ax.plot([0, w[0]], [0, w[1]], 'b:', alpha=0.4, linewidth=1)
    for w in [w_R_bar, w_G_bar, w_B_bar]:
        ax.plot([0, w[0]], [0, w[1]], 'r:', alpha=0.4, linewidth=1)

    # Colors for weights
    colors_3 = ['#e74c3c', '#27ae60', '#3498db']  # R, G, B
    colors_3bar = ['#c0392b', '#1e8449', '#2874a6']  # darker versions
    labels_3 = ['$\\vec{w}_R$', '$\\vec{w}_G$', '$\\vec{w}_B$']
    labels_3bar = ['$-\\vec{w}_R$', '$-\\vec{w}_G$', '$-\\vec{w}_B$']

    weights_3 = [w_R, w_G, w_B]
    weights_3bar = [w_R_bar, w_G_bar, w_B_bar]

    # Plot weight points - fundamental
    for w, c, label in zip(weights_3, colors_3, labels_3):
        ax.scatter(w[0], w[1], c=c, s=180, zorder=5, edgecolors='black', linewidths=2)
        ax.annotate(label, (w[0], w[1]), xytext=(8, 8),
                   textcoords='offset points', fontsize=10, fontweight='bold')

    # Plot weight points - anti-fundamental
    for w, c, label in zip(weights_3bar, colors_3bar, labels_3bar):
        ax.scatter(w[0], w[1], c=c, s=180, zorder=5, edgecolors='black', linewidths=2, marker='s')
        ax.annotate(label, (w[0], w[1]), xytext=(8, -15),
                   textcoords='offset points', fontsize=10, fontweight='bold')

    # Plot origin (apex projection)
    ax.scatter(0, 0, c='gold', s=200, marker='*', zorder=6, edgecolors='black', linewidths=2)
    ax.annotate('$W, \\bar{W}$\n(apex proj.)', (0, 0), xytext=(-45, -25),
               textcoords='offset points', fontsize=9, 
               bbox=dict(boxstyle='round', facecolor='gold', alpha=0.3))

    # Draw charge conjugation arrows (curved)
    for w3, w3bar in zip(weights_3, weights_3bar):
        ax.annotate('', xy=w3bar, xytext=w3,
                   arrowprops=dict(arrowstyle='->', color='purple', alpha=0.5,
                                  connectionstyle='arc3,rad=0.25', lw=1.5))

    # Add S₃ action label
    ax.text(0.55, 0.3, '$S_3$ action\n(Weyl group)', fontsize=9, 
            color='purple', style='italic', alpha=0.8)

    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.8, 0.8)
    ax.set_aspect('equal')
    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.3)
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.3)
    ax.set_xlabel('$T_3$ (Cartan)', fontsize=10)
    ax.set_ylabel('$T_8/\\sqrt{3}$ (Cartan)', fontsize=10)
    ax.legend(loc='upper right', fontsize=9, framealpha=0.9)

    # Key fact annotation
    ax.text(0.02, 0.98, 'Each weight:\nmultiplicity = 1', transform=ax.transAxes,
           fontsize=8, verticalalignment='top', 
           bbox=dict(boxstyle='round', facecolor='#d4edda', alpha=0.8))


def plot_stella_octangula_3d(ax):
    """
    Plot 3D stella octangula showing dual interpenetrating tetrahedra
    with color-coded vertices corresponding to SU(3) weights.
    """
    ax.set_title('Stella Octangula\n(Two Dual Tetrahedra)', fontsize=11, fontweight='bold')

    # Tetrahedron T+ vertices (fundamental 3 + apex W)
    tet1 = np.array([
        [1, 1, 1],      # W (apex - singlet direction)
        [1, -1, -1],    # R
        [-1, 1, -1],    # G
        [-1, -1, 1]     # B
    ]) / np.sqrt(3)

    # Tetrahedron T- vertices (anti-fundamental 3̄ + apex W̄)
    tet2 = -tet1

    # Define faces for tetrahedra
    faces1 = [
        [tet1[0], tet1[1], tet1[2]],
        [tet1[0], tet1[1], tet1[3]],
        [tet1[0], tet1[2], tet1[3]],
        [tet1[1], tet1[2], tet1[3]]
    ]
    faces2 = [
        [tet2[0], tet2[1], tet2[2]],
        [tet2[0], tet2[1], tet2[3]],
        [tet2[0], tet2[2], tet2[3]],
        [tet2[1], tet2[2], tet2[3]]
    ]

    # Plot tetrahedra
    poly1 = Poly3DCollection(faces1, alpha=0.2, facecolor='blue', edgecolor='blue', linewidth=1.5)
    poly2 = Poly3DCollection(faces2, alpha=0.2, facecolor='red', edgecolor='red', linewidth=1.5)
    ax.add_collection3d(poly1)
    ax.add_collection3d(poly2)

    # Plot vertices with labels
    # T+ (fundamental)
    ax.scatter(*tet1[0], c='gold', s=150, edgecolors='black', linewidths=2, zorder=5)
    ax.scatter(*tet1[1], c='#e74c3c', s=120, edgecolors='black', linewidths=1.5, zorder=5)
    ax.scatter(*tet1[2], c='#27ae60', s=120, edgecolors='black', linewidths=1.5, zorder=5)
    ax.scatter(*tet1[3], c='#3498db', s=120, edgecolors='black', linewidths=1.5, zorder=5)

    # T- (anti-fundamental)
    ax.scatter(*tet2[0], c='gold', s=150, edgecolors='black', linewidths=2, marker='*', zorder=5)
    ax.scatter(*tet2[1], c='#c0392b', s=120, edgecolors='black', linewidths=1.5, marker='s', zorder=5)
    ax.scatter(*tet2[2], c='#1e8449', s=120, edgecolors='black', linewidths=1.5, marker='s', zorder=5)
    ax.scatter(*tet2[3], c='#2874a6', s=120, edgecolors='black', linewidths=1.5, marker='s', zorder=5)

    # Add vertex labels
    offset = 0.15
    ax.text(tet1[0][0]+offset, tet1[0][1]+offset, tet1[0][2]+offset, 'W', fontsize=9, fontweight='bold')
    ax.text(tet1[1][0]+offset, tet1[1][1]-offset, tet1[1][2]-offset, 'R', fontsize=9, fontweight='bold', color='#e74c3c')
    ax.text(tet1[2][0]-offset, tet1[2][1]+offset, tet1[2][2]-offset, 'G', fontsize=9, fontweight='bold', color='#27ae60')
    ax.text(tet1[3][0]-offset, tet1[3][1]-offset, tet1[3][2]+offset, 'B', fontsize=9, fontweight='bold', color='#3498db')
    
    ax.text(tet2[0][0]-offset, tet2[0][1]-offset, tet2[0][2]-offset, '$\\bar{W}$', fontsize=9, fontweight='bold')
    ax.text(tet2[1][0]-offset, tet2[1][1]+offset, tet2[1][2]+offset, '$\\bar{R}$', fontsize=9, color='#c0392b')
    ax.text(tet2[2][0]+offset, tet2[2][1]-offset, tet2[2][2]+offset, '$\\bar{G}$', fontsize=9, color='#1e8449')
    ax.text(tet2[3][0]+offset, tet2[3][1]+offset, tet2[3][2]-offset, '$\\bar{B}$', fontsize=9, color='#2874a6')

    # Set axis properties
    ax.set_xlim([-1, 1])
    ax.set_ylim([-1, 1])
    ax.set_zlim([-1, 1])
    ax.set_xlabel('X', fontsize=9)
    ax.set_ylabel('Y', fontsize=9)
    ax.set_zlabel('Z', fontsize=9)
    ax.set_xticklabels([])
    ax.set_yticklabels([])
    ax.set_zticklabels([])

    # Annotation box
    ax.text2D(0.02, 0.98,
             "8 vertices total:\n• 6 weight vertices (R,G,B,R̄,Ḡ,B̄)\n• 2 apex vertices (W,W̄)\n• Symmetry: $S_3 \\times Z_2 \\subset O_h$",
             transform=ax.transAxes, fontsize=8, verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='#d4edda', alpha=0.9))


def plot_polyhedra_classification(ax):
    """
    Classification table showing which polyhedra satisfy GR1-GR3 conditions.
    """
    ax.set_title('Polyhedra Classification\n(Geometric Realization Conditions)', fontsize=11, fontweight='bold')
    ax.axis('off')

    # Data: polyhedron, vertices, GR1, GR2, GR3, MIN1, result
    data = [
        ('Tetrahedron', '4', '✗', '✓', '✗', '✓', 'FAIL'),
        ('Octahedron', '6', '✗', '✗', '✓', '✓', 'FAIL'),
        ('Cube', '8', '✗', '✗', '✓', '✓', 'FAIL'),
        ('Stella Octangula', '8', '✓', '✓', '✓', '✓', 'PASS'),
        ('Tetrahemihexahedron', '6', '✗', '✓', '✗', '✓', 'FAIL'),
        ('Kepler-Poinsot (any)', '12-20', '✗', '✗', '✓', '✗', 'FAIL'),
        ('Compound 3 Tetra', '12', '✓', '✗', '✓', '✗', 'FAIL'),
    ]

    col_labels = ['Polyhedron', 'V', 'GR1', 'GR2', 'GR3', 'MIN1', 'Status']
    
    cell_text = []
    cell_colors = []
    
    for row in data:
        name, v, gr1, gr2, gr3, min1, result = row
        row_text = [name, v]
        row_colors = ['white', 'white']
        
        for val in [gr1, gr2, gr3, min1]:
            row_text.append(val)
            if val == '✓':
                row_colors.append('#d4edda')
            else:
                row_colors.append('#f8d7da')
        
        if result == 'PASS':
            row_text.append('✓ PASS')
            row_colors.append('#28a745')
        else:
            row_text.append('✗ FAIL')
            row_colors.append('#dc3545')
        
        cell_text.append(row_text)
        cell_colors.append(row_colors)

    table = ax.table(cellText=cell_text,
                     colLabels=col_labels,
                     cellColours=cell_colors,
                     cellLoc='center',
                     loc='center',
                     bbox=[0, 0.05, 1, 0.9])

    table.auto_set_font_size(False)
    table.set_fontsize(8)
    table.scale(1, 1.6)

    # Style header
    for j in range(len(col_labels)):
        table[(0, j)].set_facecolor('#4a90d9')
        table[(0, j)].set_text_props(color='white', fontweight='bold')

    # Highlight stella row
    for j in range(len(col_labels)):
        if cell_text[3][0] == 'Stella Octangula':
            table[(4, j)].set_facecolor('#d4edda')

    # Add legend
    ax.text(0.5, 0.01, 
           'GR1: Weight correspondence | GR2: $S_3$ symmetry | GR3: Charge conjugation | MIN1: Minimal vertices',
           transform=ax.transAxes, ha='center', fontsize=7, style='italic')


def plot_completeness_flowchart(ax):
    """
    Flowchart showing the completeness proof logic from Theorem 0.0.3b.
    """
    ax.set_title('Completeness Proof: All Structures Classified', fontsize=11, fontweight='bold')
    ax.axis('off')
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)

    def add_box(x, y, text, color='white', width=2.4, height=0.7, fontsize=8):
        rect = FancyBboxPatch((x - width/2, y - height/2), width, height,
                              boxstyle="round,pad=0.05", facecolor=color, 
                              edgecolor='black', linewidth=1.5)
        ax.add_patch(rect)
        ax.text(x, y, text, ha='center', va='center', fontsize=fontsize, 
                wrap=True, multialignment='center')

    # Top: All topological spaces
    add_box(5, 9.2, 'All Topological\nSpaces', color='#e8f4fd', width=3)

    # Split into three branches
    ax.annotate('', xy=(2, 7.8), xytext=(5, 8.7),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    ax.annotate('', xy=(5, 7.8), xytext=(5, 8.7),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    ax.annotate('', xy=(8, 7.8), xytext=(5, 8.7),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))

    add_box(2, 7.5, 'Finite\n|V| < ∞', color='#fff3cd')
    add_box(5, 7.5, 'Countably\nInfinite', color='#fce4e4')
    add_box(8, 7.5, 'Uncountable\n(Fractals)', color='#fce4e4')

    # Infinite exclusions
    ax.annotate('', xy=(5, 6.2), xytext=(5, 7.1),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    add_box(5, 5.9, '✗ EXCLUDED\n$3⊕\\bar{3}$ has dim 6', color='#f8d7da', height=0.8)

    ax.annotate('', xy=(8, 6.2), xytext=(8, 7.1),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    add_box(8, 5.9, '✗ EXCLUDED\nCardinality > 6', color='#f8d7da', height=0.8)

    # Finite branch continues
    ax.annotate('', xy=(2, 6.5), xytext=(2, 7.1),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    add_box(2, 6.2, 'Check\nGR1-GR3', color='#fff3cd')

    ax.annotate('', xy=(1, 5), xytext=(2, 5.8),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    ax.annotate('', xy=(3, 5), xytext=(2, 5.8),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))

    add_box(1, 4.7, 'V ≠ 8', color='#fce4e4', width=1.5)
    add_box(3, 4.7, 'V = 8', color='#d4edda', width=1.5)

    ax.annotate('', xy=(1, 3.7), xytext=(1, 4.3),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    add_box(1, 3.4, '✗ MIN1\nFails', color='#f8d7da', width=1.8)

    ax.annotate('', xy=(3, 3.7), xytext=(3, 4.3),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    add_box(3, 3.4, 'Check $S_3$\nSymmetry', color='#fff3cd', width=1.8)

    ax.annotate('', xy=(2.3, 2.3), xytext=(3, 3),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    ax.annotate('', xy=(3.7, 2.3), xytext=(3, 3),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.2))

    add_box(2.3, 1.9, '✗ Cube\n(fails GR2)', color='#f8d7da', width=1.8, height=0.8)
    add_box(3.7, 1.9, '✓ Stella\nOctangula', color='#28a745', width=1.8, height=0.8)

    # Final conclusion
    add_box(5, 0.7, 'UNIQUE MINIMAL GEOMETRIC REALIZATION', color='#28a745', width=5, height=0.6)
    ax.annotate('', xy=(5, 1.0), xytext=(3.7, 1.5),
               arrowprops=dict(arrowstyle='->', color='green', lw=2))


def plot_apex_interpretation(ax):
    """
    Diagram showing physical interpretation of apex vertices.
    """
    ax.set_title('Apex Vertices: Physical Interpretation', fontsize=11, fontweight='bold')
    ax.axis('off')
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)

    # Draw weight plane
    plane = FancyBboxPatch((1, 3), 8, 3, boxstyle="round,pad=0.05",
                            facecolor='#e8f4fd', edgecolor='blue', 
                            linewidth=2, alpha=0.5)
    ax.add_patch(plane)
    ax.text(5, 4.5, 'Weight Plane ($\\mathfrak{h}^*$)\n6 weight vertices', 
           ha='center', va='center', fontsize=10, fontweight='bold')

    # Draw singlet direction
    ax.annotate('', xy=(5, 8.5), xytext=(5, 6.5),
               arrowprops=dict(arrowstyle='->', color='gold', lw=3))
    ax.annotate('', xy=(5, 1.5), xytext=(5, 3.5),
               arrowprops=dict(arrowstyle='->', color='gold', lw=3))

    # Apex vertices
    ax.scatter(5, 8.5, c='gold', s=300, marker='*', edgecolors='black', 
              linewidths=2, zorder=5)
    ax.text(5.5, 8.5, '$W$ (apex)', fontsize=10, fontweight='bold', va='center')
    
    ax.scatter(5, 1.5, c='gold', s=300, marker='*', edgecolors='black', 
              linewidths=2, zorder=5)
    ax.text(5.5, 1.5, '$\\bar{W}$ (apex)', fontsize=10, fontweight='bold', va='center')

    # Label singlet direction
    ax.text(6.5, 5, 'Singlet\nDirection\n(Confinement\nRadius)', fontsize=9, 
           ha='center', va='center', style='italic',
           bbox=dict(boxstyle='round', facecolor='gold', alpha=0.3))

    # Physical interpretation box
    interp_text = (
        "Physical Meaning:\n"
        "• W, W̄ encode color singlet state\n"
        "• Project to origin in weight space\n"
        "• Required by GR3 (conjugation)\n"
        "• Enforce 3D embedding (MIN2)"
    )
    ax.text(0.5, 9.5, interp_text, fontsize=8, va='top',
           bbox=dict(boxstyle='round', facecolor='#fff3cd', alpha=0.9))


def create_combined_figure():
    """
    Create the comprehensive combined visualization for Theorems 0.0.3 and 0.0.3b.
    """
    fig = plt.figure(figsize=(18, 14))

    # Create grid: 3 rows, 3 columns
    gs = gridspec.GridSpec(3, 3, figure=fig, height_ratios=[1, 1, 0.9],
                          width_ratios=[1, 1, 1], hspace=0.35, wspace=0.3)

    # Row 1: SU(3) weight diagram, 3D stella, apex interpretation
    ax1 = fig.add_subplot(gs[0, 0])
    plot_su3_weight_diagram_enhanced(ax1)

    ax2 = fig.add_subplot(gs[0, 1], projection='3d')
    plot_stella_octangula_3d(ax2)

    ax3 = fig.add_subplot(gs[0, 2])
    plot_apex_interpretation(ax3)

    # Row 2: Classification table (left + middle), completeness flowchart (right)
    ax4 = fig.add_subplot(gs[1, :2])
    plot_polyhedra_classification(ax4)

    ax5 = fig.add_subplot(gs[1, 2])
    plot_completeness_flowchart(ax5)

    # Row 3: Summary text
    ax6 = fig.add_subplot(gs[2, :])
    ax6.axis('off')
    
    summary_text = """
    THEOREM 0.0.3 (Stella Uniqueness): The stella octangula is the unique minimal 3D geometric realization of SU(3).
    
    THEOREM 0.0.3b (Completeness): Among ALL topological spaces satisfying GR1-GR3, the stella octangula is the unique minimum.
    
    Key Results:
    ┌─────────────────────────────────────────────────────────────────────────────────────────────────────────┐
    │  • 8 vertices required: 6 weight vertices (from 3⊕3̄) + 2 apex vertices (GR3 + 3D embedding)           │
    │  • Weyl group S₃ embeds as subgroup: S₃ ⊂ O_h (full octahedral symmetry)                              │
    │  • Infinite structures excluded: 3⊕3̄ has finite dimension with multiplicity 1                        │
    │  • All standard polyhedra fail at least one condition except stella octangula                          │
    └─────────────────────────────────────────────────────────────────────────────────────────────────────────┘
    
    Implications: The stella octangula topology is DERIVED, not assumed. This is essential for the QCD-Planck hierarchy (Prop. 0.0.17t).
    """
    
    ax6.text(0.5, 0.5, summary_text, transform=ax6.transAxes, fontsize=10,
            ha='center', va='center', family='monospace',
            bbox=dict(boxstyle='round', facecolor='#f8f9fa', edgecolor='gray', alpha=0.9))

    # Main title
    fig.suptitle('Theorems 0.0.3 & 0.0.3b: Stella Octangula as Unique Minimal Geometric Realization of SU(3)\n'
                'Completeness of Classification Among All Topological Spaces',
                fontsize=14, fontweight='bold', y=0.98)

    return fig


def main():
    """Generate combined visualization for Theorems 0.0.3 and 0.0.3b."""
    print("=" * 70)
    print("THEOREMS 0.0.3 & 0.0.3b COMBINED VISUALIZATION")
    print("Stella Octangula: Unique Minimal Geometric Realization of SU(3)")
    print("=" * 70)

    # Create combined figure
    fig = create_combined_figure()

    # Save
    output_path = 'verification/plots/theorem_0_0_3_combined.png'
    fig.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"\nSaved: {output_path}")

    plt.close()

    print("\n" + "=" * 70)
    print("VISUALIZATION COMPLETE")
    print("=" * 70)
    print(f"\nGenerated plot: {output_path}")

    return output_path


if __name__ == "__main__":
    main()
