#!/usr/bin/env python3
"""
Figure: Theorem 0.0.3 Weight Diagram

Visualization for Theorem 0.0.3: Stella Octangula as Minimal Geometric Realization of SU(3)

Creates plots showing:
1. SU(3) weight diagram with fundamental and anti-fundamental triangles
2. 3D stella octangula with color-coded vertices
3. Projection from 3D to 2D weight space
4. Alternative polyhedra comparison

Source: Extracted from verification/foundations/theorem_0_0_3_visualization.py
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from pathlib import Path

# Output directory (parent of scripts folder = figures folder)
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

# Set up plotting style
plt.rcParams['figure.figsize'] = (14, 10)
plt.rcParams['font.size'] = 10
plt.rcParams['axes.titlesize'] = 12
plt.rcParams['axes.labelsize'] = 10


def plot_su3_weight_diagram(ax):
    """Plot the SU(3) weight diagram showing 3 + 3-bar representations."""

    # Fundamental representation weights (quarks)
    w_R = np.array([0.5, 1/(2*np.sqrt(3))])
    w_G = np.array([-0.5, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    # Anti-fundamental representation weights (antiquarks)
    w_Rbar = -w_R
    w_Gbar = -w_G
    w_Bbar = -w_B

    # Origin (singlet/apex vertices project here)
    origin = np.array([0, 0])

    # Plot filled triangles first (underneath everything else)
    # This creates the "Star of David" / hexagram pattern
    # Anti-fundamental first (more transparent, background)
    antifund_triangle_filled = plt.Polygon([w_Rbar, w_Gbar, w_Bbar], fill=True,
                                            facecolor='red', alpha=0.10,
                                            edgecolor='red', linewidth=2.0,
                                            linestyle='--', label=r'$\bar{\mathbf{3}}$ (anti-fundamental)', zorder=0)
    ax.add_patch(antifund_triangle_filled)

    # Fundamental on top (more visible)
    fund_triangle_filled = plt.Polygon([w_R, w_G, w_B], fill=True,
                                        facecolor='blue', alpha=0.20,
                                        edgecolor='blue', linewidth=2.5,
                                        linestyle='-', label=r'$\mathbf{3}$ (fundamental)', zorder=1)
    ax.add_patch(fund_triangle_filled)

    # Draw lines from all vertices to center (W/W̄)
    # These represent the edges connecting to apex vertices in 3D
    for w in [w_R, w_G, w_B]:
        ax.plot([w[0], 0], [w[1], 0], 'b:', linewidth=1.5, alpha=0.4, zorder=2)
    for w in [w_Rbar, w_Gbar, w_Bbar]:
        ax.plot([w[0], 0], [w[1], 0], 'r:', linewidth=1.5, alpha=0.4, zorder=2)

    # Plot vertices with colors - fundamental (circles)
    colors_fund = ['#e74c3c', '#27ae60', '#3498db']  # R, G, B (vibrant colors)
    labels_fund = [r'$\vec{w}_R$', r'$\vec{w}_G$', r'$\vec{w}_B$']
    for w, c, l in zip([w_R, w_G, w_B], colors_fund, labels_fund):
        ax.scatter(*w, c=c, s=180, zorder=5, edgecolor='black', linewidth=1.5)
        ax.annotate(l, w, xytext=(8, 8), textcoords='offset points', fontsize=11, fontweight='bold')

    # Anti-fundamental vertices (squares)
    colors_anti = ['#c0392b', '#1e8449', '#2874a6']  # Darker versions
    labels_anti = [r'$-\vec{w}_R$', r'$-\vec{w}_G$', r'$-\vec{w}_B$']
    for w, c, l in zip([w_Rbar, w_Gbar, w_Bbar], colors_anti, labels_anti):
        ax.scatter(*w, c=c, s=180, zorder=5, edgecolor='black', linewidth=1.5, marker='s')
        ax.annotate(l, w, xytext=(8, -15), textcoords='offset points', fontsize=11, fontweight='bold')

    # Draw charge conjugation arrows (curved) - shows GR3 condition
    # These connect each weight to its conjugate: w → -w
    weights_3 = [w_R, w_G, w_B]
    weights_3bar = [w_Rbar, w_Gbar, w_Bbar]
    for i, (w3, w3bar) in enumerate(zip(weights_3, weights_3bar)):
        # Only add label to first arrow for legend
        ax.annotate('', xy=w3bar, xytext=w3,
                   arrowprops=dict(arrowstyle='->', color='purple', alpha=0.6,
                                  connectionstyle='arc3,rad=0.25', lw=1.5,
                                  shrinkA=12, shrinkB=12),
                   zorder=15)
    # Add a dummy line for the legend entry
    ax.plot([], [], color='purple', linestyle='-', linewidth=1.5, alpha=0.6,
            label=r'Charge conjugation ($\vec{w} \to -\vec{w}$)')

    # Origin marker - the apex vertices W and W̄ both project here
    ax.scatter(0, 0, c='gold', s=200, marker='*', zorder=10, edgecolor='black', linewidth=2,
               label=r'Singlet (apex $W, \bar{W}$)')
    ax.annotate(r'$\vec{0}$', (0, 0), xytext=(-25, -20), textcoords='offset points', fontsize=11,
                bbox=dict(boxstyle='round', facecolor='gold', alpha=0.5), zorder=10)

    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.8, 0.8)
    ax.set_xlabel(r'$h_1^*$ (Cartan coordinate)', fontsize=11)
    ax.set_ylabel(r'$h_2^*$ (Cartan coordinate)', fontsize=11)
    ax.set_title(r'SU(3) Weight Diagram: $\mathbf{3} \oplus \bar{\mathbf{3}}$', fontsize=12, fontweight='bold')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.legend(loc='upper right', fontsize=9)
    ax.axhline(y=0, color='gray', linestyle='--', linewidth=0.5, alpha=0.5)
    ax.axvline(x=0, color='gray', linestyle='--', linewidth=0.5, alpha=0.5)
    
    # Add multiplicity annotation (key for Theorem 0.0.3b)
    ax.text(0.02, 0.98, 'Each weight has\nmultiplicity 1', transform=ax.transAxes,
           fontsize=9, verticalalignment='top', 
           bbox=dict(boxstyle='round', facecolor='#d4edda', alpha=0.8))


def plot_stella_octangula_3d(ax):
    """Plot 3D stella octangula with color-coded vertices and chirality arrows."""
    from mpl_toolkits.mplot3d.art3d import Line3DCollection

    # Tetrahedron T+ vertices
    # Index 0 = W (apex), 1 = R, 2 = G, 3 = B
    T_plus = np.array([
        [1, 1, 1],      # apex (W vertex - singlet)
        [1, -1, -1],    # R
        [-1, 1, -1],    # G
        [-1, -1, 1]     # B
    ])

    # Tetrahedron T- vertices (dual)
    T_minus = np.array([
        [-1, -1, -1],   # apex (W-bar vertex - singlet)
        [-1, 1, 1],     # R-bar
        [1, -1, 1],     # G-bar
        [1, 1, -1]      # B-bar
    ])

    # Define faces for each tetrahedron
    def get_tetra_faces(verts):
        return [
            [verts[0], verts[1], verts[2]],
            [verts[0], verts[1], verts[3]],
            [verts[0], verts[2], verts[3]],
            [verts[1], verts[2], verts[3]]
        ]

    # Plot T+ (blue, transparent)
    faces_plus = get_tetra_faces(T_plus)
    poly_plus = Poly3DCollection(faces_plus, alpha=0.2, facecolor='blue',
                                  edgecolor='blue', linewidth=1)
    ax.add_collection3d(poly_plus)

    # Plot T- (red, transparent)
    faces_minus = get_tetra_faces(T_minus)
    poly_minus = Poly3DCollection(faces_minus, alpha=0.2, facecolor='red',
                                   edgecolor='red', linewidth=1)
    ax.add_collection3d(poly_minus)

    # Plot vertices
    # T+ vertices
    ax.scatter(*T_plus[0], c='gold', s=250, marker='o', label='W (singlet)', edgecolor='black', linewidth=2, zorder=5)
    ax.scatter(*T_plus[1], c='red', s=200, label='R', edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_plus[2], c='green', s=200, label='G', edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_plus[3], c='blue', s=200, label='B', edgecolor='black', linewidth=1, zorder=5)

    # T- vertices
    ax.scatter(*T_minus[0], c='gold', s=250, marker='o', label=r'$\bar{W}$ (singlet)', edgecolor='black', linewidth=2, zorder=5)
    ax.scatter(*T_minus[1], c='#FF6666', s=200, marker='s', label=r'$\bar{R}$', edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_minus[2], c='#66FF66', s=200, marker='s', label=r'$\bar{G}$', edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_minus[3], c='#6666FF', s=200, marker='s', label=r'$\bar{B}$', edgecolor='black', linewidth=1, zorder=5)

    # Draw edges explicitly for clarity
    edges_plus = [(0,1), (0,2), (0,3), (1,2), (2,3), (3,1)]
    for i, j in edges_plus:
        ax.plot3D(*zip(T_plus[i], T_plus[j]), 'b-', linewidth=2, alpha=0.7)

    edges_minus = [(0,1), (0,2), (0,3), (1,2), (2,3), (3,1)]
    for i, j in edges_minus:
        ax.plot3D(*zip(T_minus[i], T_minus[j]), 'r--', linewidth=2, alpha=0.7)

    # Draw chirality arrows on the base triangle (R-G-B) - right-handed: R→G→B→R
    def draw_3d_arrow(start, end, color='purple', offset_scale=0.15):
        """Draw an arrow slightly offset from the edge to show direction."""
        midpoint = (start + end) / 2
        direction = end - start
        direction = direction / np.linalg.norm(direction)
        # Offset perpendicular to edge and toward center of triangle
        center = (T_plus[1] + T_plus[2] + T_plus[3]) / 3
        to_center = center - midpoint
        to_center = to_center / np.linalg.norm(to_center)
        # Move outward (away from center)
        offset = -to_center * offset_scale
        arrow_start = midpoint + offset - direction * 0.15
        arrow_end = midpoint + offset + direction * 0.15
        ax.quiver(arrow_start[0], arrow_start[1], arrow_start[2],
                  (arrow_end - arrow_start)[0], (arrow_end - arrow_start)[1], (arrow_end - arrow_start)[2],
                  color=color, arrow_length_ratio=0.4, linewidth=2.5)

    # R→G, G→B, B→R (right-handed chirality on fundamental triangle)
    draw_3d_arrow(T_plus[1], T_plus[2])  # R → G
    draw_3d_arrow(T_plus[2], T_plus[3])  # G → B
    draw_3d_arrow(T_plus[3], T_plus[1])  # B → R

    # Add vertex labels
    label_offset = 0.2
    ax.text(T_plus[0][0]+label_offset, T_plus[0][1]+label_offset, T_plus[0][2]+label_offset, 'W', fontsize=11, fontweight='bold')
    ax.text(T_plus[1][0]+label_offset, T_plus[1][1]-label_offset, T_plus[1][2]-label_offset, 'R', fontsize=11, fontweight='bold', color='red')
    ax.text(T_plus[2][0]-label_offset, T_plus[2][1]+label_offset, T_plus[2][2]-label_offset, 'G', fontsize=11, fontweight='bold', color='green')
    ax.text(T_plus[3][0]-label_offset, T_plus[3][1]-label_offset, T_plus[3][2]+label_offset, 'B', fontsize=11, fontweight='bold', color='blue')

    ax.text(T_minus[0][0]-label_offset, T_minus[0][1]-label_offset, T_minus[0][2]-label_offset, r'$\bar{W}$', fontsize=11, fontweight='bold')
    ax.text(T_minus[1][0]-label_offset, T_minus[1][1]+label_offset, T_minus[1][2]+label_offset, r'$\bar{R}$', fontsize=10, color='#CC0000')
    ax.text(T_minus[2][0]+label_offset, T_minus[2][1]-label_offset, T_minus[2][2]+label_offset, r'$\bar{G}$', fontsize=10, color='#008800')
    ax.text(T_minus[3][0]+label_offset, T_minus[3][1]+label_offset, T_minus[3][2]-label_offset, r'$\bar{B}$', fontsize=10, color='#0000CC')

    ax.set_xlabel('X', fontsize=10)
    ax.set_ylabel('Y', fontsize=10)
    ax.set_zlabel('Z', fontsize=10)
    ax.set_title('Stella Octangula\n(Right-handed chirality: R→G→B→R)', fontsize=12, fontweight='bold')

    # Set equal aspect ratio and limits
    ax.set_box_aspect([1,1,1])
    ax.set_xlim([-1.5, 1.5])
    ax.set_ylim([-1.5, 1.5])
    ax.set_zlim([-1.5, 1.5])


def plot_projection_diagram(ax):
    """Show projection from 3D stella octangula to 2D weight space."""

    # 3D vertices (simplified representation)
    T_plus = np.array([
        [1, 1, 1],      # W (apex)
        [1, -1, -1],    # R
        [-1, 1, -1],    # G
        [-1, -1, 1]     # B
    ])

    # Projection direction (along [1,1,1])
    n = np.array([1, 1, 1]) / np.sqrt(3)

    # Projection matrix
    P = np.eye(3) - np.outer(n, n)

    # Project vertices
    projected = T_plus @ P.T

    # Plot 3D positions (x-axis represents height along [1,1,1])
    heights = T_plus @ n

    # Create a 2D representation showing projection
    # X-axis: height along singlet direction
    # Y-axis: radial distance in weight plane

    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5, label='Weight plane')
    ax.axvline(x=0, color='gray', linestyle=':', alpha=0.5)

    # Plot vertices with their projections
    colors = ['gold', 'red', 'green', 'blue']
    labels = ['W (apex)', 'R', 'G', 'B']

    for i, (v, c, l) in enumerate(zip(T_plus, colors, labels)):
        height = np.dot(v, n)
        radial = np.linalg.norm(P @ v)

        # 3D vertex
        ax.scatter(height, radial, c=c, s=150, zorder=5, edgecolor='black')

        # Projection line
        ax.plot([height, height], [radial, 0], 'k:', alpha=0.5)

        # Projected point
        ax.scatter(height, 0, c=c, s=80, marker='x', zorder=5)

        ax.annotate(l, (height + 0.05, radial + 0.05), fontsize=10)

    ax.set_xlabel('Height along [1,1,1] (singlet direction)', fontsize=10)
    ax.set_ylabel('Distance from singlet axis', fontsize=10)
    ax.set_title('Projection to Weight Space\n(W and W̄ project to origin)', fontsize=12, fontweight='bold')
    ax.set_xlim(-2, 2)
    ax.set_ylim(-0.5, 2)
    ax.grid(True, alpha=0.3)

    # Add annotation about 6+2 structure
    ax.annotate('6 vertices → weight plane\n2 vertices → origin (singlet)',
                xy=(0.5, 1.5), fontsize=9, bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))


def plot_alternative_comparison(ax):
    """Compare stella octangula with alternative polyhedra."""

    alternatives = [
        ('Two Triangles\n(6 vertices)', 'FAIL\nMIN2', 'red'),
        ('Octahedron\n(6 vertices)', 'FAIL\nGR1', 'red'),
        ('Cube\n(8 vertices)', 'FAIL\nGR2', 'red'),
        ('Prism\n(6 vertices)', 'FAIL\nGR3', 'red'),
        ('Separate Tetra\n(8 vertices)', 'FAIL\nConnected', 'red'),
        ('Stella Octangula\n(8 vertices)', 'PASS\nAll Criteria', 'green')
    ]

    x_pos = np.arange(len(alternatives))

    colors = [c for _, _, c in alternatives]

    bars = ax.bar(x_pos, [1]*len(alternatives), color=colors, alpha=0.7, edgecolor='black')

    ax.set_xticks(x_pos)
    ax.set_xticklabels([name for name, _, _ in alternatives], fontsize=9)
    ax.set_ylim(0, 1.5)
    ax.set_yticks([])

    # Add status labels on bars
    for i, (_, status, _) in enumerate(alternatives):
        ax.text(i, 0.5, status, ha='center', va='center', fontsize=9, fontweight='bold')

    ax.set_title('Alternative Polyhedra Elimination\n(Only Stella Octangula Satisfies All Constraints)',
                 fontsize=12, fontweight='bold')

    # Add legend for criteria
    criteria_text = """Criteria:
GR1: Weight correspondence
GR2: Symmetry preservation (S₃)
GR3: Charge conjugation
MIN1-3: Minimality conditions"""

    ax.text(0.02, 0.98, criteria_text, transform=ax.transAxes, fontsize=8,
            verticalalignment='top', bbox=dict(boxstyle='round', facecolor='lightgray', alpha=0.5))


def create_summary_figure():
    """Create comprehensive summary figure."""

    fig = plt.figure(figsize=(16, 12))

    # 2x2 grid of subplots
    ax1 = fig.add_subplot(2, 2, 1)
    ax2 = fig.add_subplot(2, 2, 2, projection='3d')
    ax3 = fig.add_subplot(2, 2, 3)
    ax4 = fig.add_subplot(2, 2, 4)

    # Plot each component
    plot_su3_weight_diagram(ax1)
    plot_stella_octangula_3d(ax2)
    plot_projection_diagram(ax3)
    plot_alternative_comparison(ax4)

    # Main title
    fig.suptitle('Theorem 0.0.3: Uniqueness of Stella Octangula\nas Minimal Geometric Realization of SU(3)',
                 fontsize=14, fontweight='bold', y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.96])

    return fig


def main():
    """Generate and save verification plots."""

    print("Generating Theorem 0.0.3 visualization...")

    # Figure 1: SU(3) Weight Diagram (referenced at main.tex line 656)
    fig1, ax1 = plt.subplots(figsize=(8, 8))
    plot_su3_weight_diagram(ax1)
    for ext in ['pdf', 'png']:
        output_path = output_dir / f"fig_su3_weight_diagram.{ext}"
        fig1.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"  Saved: {output_path}")
    plt.close(fig1)

    # Note: 3D Stella Octangula figure (fig_thm_0_0_2_stella_3d) is generated
    # by a separate script: fig_thm_0_0_2_stella_3d.py

    print("  All plots generated successfully!")


if __name__ == "__main__":
    main()
