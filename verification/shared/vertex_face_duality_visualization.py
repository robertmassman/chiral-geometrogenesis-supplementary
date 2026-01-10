#!/usr/bin/env python3
"""
Vertex-Face Duality Visualization

This script creates a comprehensive visualization comparing vertex coloring
(standard weight diagram) with face coloring (depression zones), demonstrating
the vertex-face duality from Definition 0.1.3 Section 7 and Definition 0.1.4.

Author: Verification Suite
Date: December 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, FancyArrowPatch, Circle, Wedge
from matplotlib.collections import PatchCollection
import matplotlib.patches as mpatches
import os

# Phase factors (cube roots of unity)
OMEGA = np.exp(2j * np.pi / 3)

# Weight vectors (SU(3) fundamental representation)
W_R = np.array([1/2, 1/(2*np.sqrt(3))])
W_G = np.array([-1/2, 1/(2*np.sqrt(3))])
W_B = np.array([0, -1/np.sqrt(3)])

# Colors
COLORS = {'R': '#e74c3c', 'G': '#27ae60', 'B': '#3498db'}
ANTI_COLORS = {'R': '#1abc9c', 'G': '#9b59b6', 'B': '#f39c12'}  # Complementary


def create_comparison_figure():
    """Create side-by-side comparison of vertex and face coloring."""
    fig, axes = plt.subplots(1, 3, figsize=(16, 5.5))

    # === Panel 1: Vertex Coloring (Standard Weight Diagram) ===
    ax1 = axes[0]
    draw_vertex_colored_diagram(ax1)
    ax1.set_title('Vertex Coloring\n(Standard Weight Diagram)', fontsize=13, fontweight='bold')

    # === Panel 2: Face Coloring (Depression Zones) ===
    ax2 = axes[1]
    draw_face_colored_diagram(ax2)
    ax2.set_title('Face Coloring\n(Color Domain Representation)', fontsize=13, fontweight='bold')

    # === Panel 3: Duality Correspondence ===
    ax3 = axes[2]
    draw_duality_arrows(ax3)
    ax3.set_title('Vertex-Face Duality\n(Definition 0.1.4)', fontsize=13, fontweight='bold')

    plt.tight_layout()
    return fig


def draw_vertex_colored_diagram(ax):
    """
    Draw vertex-colored representation.
    Colors are placed at VERTICES (points where color pressure is maximum).
    This is the standard SU(3) weight diagram representation.
    """
    weights = {'R': W_R, 'G': W_G, 'B': W_B}

    # Draw filled triangle (light gray)
    triangle = plt.Polygon([W_R, W_G, W_B], fill=True, facecolor='#f5f5f5',
                          edgecolor='black', linewidth=2)
    ax.add_patch(triangle)

    # Draw arrows from center to each vertex
    for name, w in weights.items():
        ax.annotate('', xy=(w[0], w[1]), xytext=(0, 0),
                   arrowprops=dict(arrowstyle='->', color=COLORS[name],
                                  lw=2.5, mutation_scale=15))

    # Draw colored vertices (large markers)
    for name, w in weights.items():
        circle = Circle((w[0], w[1]), 0.06, color=COLORS[name],
                        ec='black', linewidth=2, zorder=10)
        ax.add_patch(circle)
        # Label
        offset = w / np.linalg.norm(w) * 0.15
        ax.text(w[0] + offset[0], w[1] + offset[1], name,
               fontsize=14, fontweight='bold', ha='center', va='center',
               color=COLORS[name])

    # Center point
    ax.plot(0, 0, 'ko', markersize=8, zorder=5)
    ax.text(0.05, -0.08, 'O', fontsize=10)

    # Labels
    ax.text(0.55, -0.6, 'Color at VERTEX\n(pressure source)',
           fontsize=10, style='italic', ha='center',
           bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    _style_axis(ax)


def draw_face_colored_diagram(ax):
    """
    Draw face-colored representation.
    Each face (region) is colored by the color that DOMINATES there.
    The face opposite vertex c is where color c is DEPRESSED.
    """
    weights = {'R': W_R, 'G': W_G, 'B': W_B}

    # Draw the three color domains as pie slices
    # Each domain subtends 120° centered on its weight vector

    for name, w in weights.items():
        # Angle of weight vector
        angle = np.degrees(np.arctan2(w[1], w[0]))

        # Draw wedge (pie slice) for this domain
        wedge = Wedge((0, 0), 0.65, angle - 60, angle + 60,
                     facecolor=COLORS[name], alpha=0.35,
                     edgecolor=COLORS[name], linewidth=2)
        ax.add_patch(wedge)

        # Domain label inside the wedge
        label_r = 0.4
        label_angle = np.radians(angle)
        ax.text(label_r * np.cos(label_angle), label_r * np.sin(label_angle),
               f'D_{name}', fontsize=12, fontweight='bold',
               ha='center', va='center', color=COLORS[name])

    # Draw triangle outline
    triangle = plt.Polygon([W_R, W_G, W_B], fill=False,
                          edgecolor='black', linewidth=2.5)
    ax.add_patch(triangle)

    # Mark face centers (depression zones) with anti-color
    face_centers = {
        'R': (W_G + W_B) / 2,  # Face opposite R
        'G': (W_R + W_B) / 2,  # Face opposite G
        'B': (W_R + W_G) / 2,  # Face opposite B
    }

    for name, fc in face_centers.items():
        # Small square marker in anti-color
        ax.plot(fc[0], fc[1], 's', color=ANTI_COLORS[name],
               markersize=10, markeredgecolor='black', markeredgewidth=1.5)
        # Label
        ax.text(fc[0] - 0.12, fc[1] - 0.08, f'E_{name}',
               fontsize=9, color='gray')

    # Center
    ax.plot(0, 0, 'ko', markersize=8, zorder=5)

    # Labels
    ax.text(0.55, -0.6, 'Face shows DOMAIN\n(where color dominates)',
           fontsize=10, style='italic', ha='center',
           bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    _style_axis(ax)


def draw_duality_arrows(ax):
    """
    Draw the vertex-face duality correspondence.
    Shows how vertex (source) corresponds to opposite face (depression zone).
    """
    weights = {'R': W_R, 'G': W_G, 'B': W_B}
    face_centers = {
        'R': (W_G + W_B) / 2,
        'G': (W_R + W_B) / 2,
        'B': (W_R + W_G) / 2,
    }

    # Draw light triangle
    triangle = plt.Polygon([W_R, W_G, W_B], fill=True, facecolor='#fafafa',
                          edgecolor='black', linewidth=2)
    ax.add_patch(triangle)

    # Draw duality arrows: from each vertex through center to opposite face
    for name in ['R', 'G', 'B']:
        v = weights[name]
        f = face_centers[name]

        # Vertex marker
        circle = Circle((v[0], v[1]), 0.05, color=COLORS[name],
                        ec='black', linewidth=2, zorder=10)
        ax.add_patch(circle)

        # Face center marker
        ax.plot(f[0], f[1], 's', color=ANTI_COLORS[name],
               markersize=12, markeredgecolor='black', markeredgewidth=2, zorder=10)

        # Dashed arrow from vertex toward face (through center)
        ax.annotate('', xy=(f[0] * 0.95, f[1] * 0.95),
                   xytext=(v[0] * 0.85, v[1] * 0.85),
                   arrowprops=dict(arrowstyle='->', color=COLORS[name],
                                  lw=2.5, ls='--', mutation_scale=15))

        # Labels
        v_offset = v / np.linalg.norm(v) * 0.12
        ax.text(v[0] + v_offset[0], v[1] + v_offset[1], f'x_{name}',
               fontsize=11, fontweight='bold', color=COLORS[name])

    # Center point
    ax.plot(0, 0, 'ko', markersize=10, zorder=5)
    ax.text(0.08, -0.05, 'O', fontsize=10)

    # Legend
    legend_elements = [
        mpatches.Patch(facecolor=COLORS['R'], edgecolor='black',
                      label='Vertex: Color SOURCE'),
        mpatches.Patch(facecolor=ANTI_COLORS['R'], edgecolor='black',
                      label='Face: Color DEPRESSED'),
    ]
    ax.legend(handles=legend_elements, loc='lower right', fontsize=9,
             framealpha=0.9)

    # Annotation
    ax.text(0, -0.7, 'Vertex x_c → Face E_c\n(through center O)',
           fontsize=10, style='italic', ha='center',
           bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    _style_axis(ax)


def _style_axis(ax):
    """Apply common styling to axis."""
    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2, linewidth=0.5)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2, linewidth=0.5)
    ax.set_xlim(-0.85, 0.85)
    ax.set_ylim(-0.85, 0.75)
    ax.set_aspect('equal')
    ax.set_xlabel('T₃', fontsize=11)
    ax.set_ylabel('T₈', fontsize=11)
    ax.grid(True, alpha=0.15)


def create_detailed_duality_figure():
    """Create a more detailed figure showing the mathematical content."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # === Panel 1: Weight diagram with phases ===
    ax1 = axes[0, 0]
    draw_phases_on_weight_diagram(ax1)
    ax1.set_title('Phase Factors at Vertices\n(Definition 0.1.2)', fontsize=12, fontweight='bold')

    # === Panel 2: Pressure distribution ===
    ax2 = axes[0, 1]
    draw_pressure_landscape(ax2)
    ax2.set_title('Pressure Landscape P_total(x)\n(Definition 0.1.3)', fontsize=12, fontweight='bold')

    # === Panel 3: Depression zones ===
    ax3 = axes[1, 0]
    draw_depression_zones(ax3)
    ax3.set_title('Depression Zones E_c\n(Definition 0.1.4)', fontsize=12, fontweight='bold')

    # === Panel 4: Summary table ===
    ax4 = axes[1, 1]
    draw_summary_table(ax4)
    ax4.set_title('Vertex-Face Duality Summary', fontsize=12, fontweight='bold')

    plt.tight_layout()
    return fig


def draw_phases_on_weight_diagram(ax):
    """Show phase factors at each vertex."""
    weights = {'R': W_R, 'G': W_G, 'B': W_B}
    phases = {'R': 1, 'G': OMEGA, 'B': OMEGA**2}

    # Draw triangle
    triangle = plt.Polygon([W_R, W_G, W_B], fill=True, facecolor='#f8f8f8',
                          edgecolor='black', linewidth=2)
    ax.add_patch(triangle)

    # Draw vertices with phase info
    for name, w in weights.items():
        # Vertex
        circle = Circle((w[0], w[1]), 0.06, color=COLORS[name],
                        ec='black', linewidth=2, zorder=10)
        ax.add_patch(circle)

        # Phase value
        phase = phases[name]
        phase_str = {
            'R': '1 = e^{i0}',
            'G': 'ω = e^{i2π/3}',
            'B': 'ω² = e^{i4π/3}'
        }[name]

        offset = w / np.linalg.norm(w) * 0.2
        ax.text(w[0] + offset[0], w[1] + offset[1],
               f'{name}\n{phase_str}',
               fontsize=9, ha='center', va='center',
               color=COLORS[name], fontweight='bold')

    # Sum annotation
    ax.text(0, -0.55, '1 + ω + ω² = 0\n(Color Neutrality)',
           fontsize=11, ha='center', style='italic',
           bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    _style_axis(ax)


def draw_pressure_landscape(ax):
    """Draw pressure function P_c as contours."""
    # Create grid
    x = np.linspace(-0.7, 0.7, 100)
    y = np.linspace(-0.7, 0.7, 100)
    X, Y = np.meshgrid(x, y)

    # Calculate pressure (using 2D projection)
    epsilon = 0.1
    P_total = np.zeros_like(X)

    for name, w in {'R': W_R, 'G': W_G, 'B': W_B}.items():
        dist_sq = (X - w[0])**2 + (Y - w[1])**2
        P_total += 1 / (dist_sq + epsilon**2)

    # Contour plot
    levels = np.linspace(P_total.min(), P_total.max(), 15)
    cs = ax.contourf(X, Y, P_total, levels=levels, cmap='YlOrRd', alpha=0.7)
    ax.contour(X, Y, P_total, levels=levels[::2], colors='black', alpha=0.3, linewidths=0.5)

    # Mark vertices
    for name, w in {'R': W_R, 'G': W_G, 'B': W_B}.items():
        ax.plot(w[0], w[1], 'o', color='white', markersize=12,
               markeredgecolor=COLORS[name], markeredgewidth=3)
        ax.text(w[0], w[1] + 0.08, name, fontsize=11, ha='center',
               fontweight='bold', color=COLORS[name])

    # Center
    ax.plot(0, 0, 'k+', markersize=10, markeredgewidth=2)

    cbar = plt.colorbar(cs, ax=ax, shrink=0.8)
    cbar.set_label('P_total', fontsize=10)

    _style_axis(ax)


def draw_depression_zones(ax):
    """Show depression zones with color coding."""
    weights = {'R': W_R, 'G': W_G, 'B': W_B}
    face_centers = {
        'R': (W_G + W_B) / 2,
        'G': (W_R + W_B) / 2,
        'B': (W_R + W_G) / 2,
    }

    # Draw triangle with face coloring
    # Each face is colored by the anti-color (showing depression)

    # Face opposite R (edge G-B)
    ax.fill([W_G[0], W_B[0], 0], [W_G[1], W_B[1], 0],
           color=ANTI_COLORS['R'], alpha=0.4, label='E_R')
    # Face opposite G (edge R-B)
    ax.fill([W_R[0], W_B[0], 0], [W_R[1], W_B[1], 0],
           color=ANTI_COLORS['G'], alpha=0.4, label='E_G')
    # Face opposite B (edge R-G)
    ax.fill([W_R[0], W_G[0], 0], [W_R[1], W_G[1], 0],
           color=ANTI_COLORS['B'], alpha=0.4, label='E_B')

    # Triangle outline
    triangle = plt.Polygon([W_R, W_G, W_B], fill=False,
                          edgecolor='black', linewidth=2.5)
    ax.add_patch(triangle)

    # Vertices
    for name, w in weights.items():
        ax.plot(w[0], w[1], 'o', color=COLORS[name], markersize=12,
               markeredgecolor='black', markeredgewidth=2)

    # Face center labels
    for name, fc in face_centers.items():
        ax.text(fc[0], fc[1], f'E_{name}',
               fontsize=11, fontweight='bold', ha='center', va='center',
               bbox=dict(boxstyle='round', facecolor='white', alpha=0.7))

    ax.legend(loc='lower right', fontsize=9)
    _style_axis(ax)


def draw_summary_table(ax):
    """Draw a summary table of the duality."""
    ax.axis('off')

    table_data = [
        ['Color', 'Vertex\n(Source)', 'Face Center\n(Depression)', 'Duality'],
        ['R', 'x_R = (1,1,1)/√3', '-x_R/3', 'D_R ↔ E_R'],
        ['G', 'x_G = (1,-1,-1)/√3', '-x_G/3', 'D_G ↔ E_G'],
        ['B', 'x_B = (-1,1,-1)/√3', '-x_B/3', 'D_B ↔ E_B'],
    ]

    colors_list = [['lightgray'] * 4,
                   [COLORS['R'], '#ffcccc', ANTI_COLORS['R'], 'white'],
                   [COLORS['G'], '#ccffcc', ANTI_COLORS['G'], 'white'],
                   [COLORS['B'], '#ccccff', ANTI_COLORS['B'], 'white']]

    table = ax.table(cellText=table_data,
                    cellColours=colors_list,
                    loc='center',
                    cellLoc='center')
    table.auto_set_font_size(False)
    table.set_fontsize(10)
    table.scale(1.2, 2)

    # Key equations below table
    ax.text(0.5, 0.15,
           'Key Result: Face opposite to x_c is where color c is DEPRESSED\n\n'
           'D_c = {x : P_c(x) ≥ P_c′(x)} — Domain where c dominates\n'
           'E_c = {x : P_c(x) ≤ P_c′(x)} — Zone where c is suppressed\n\n'
           'Vertex coloring shows SOURCES, Face coloring shows DYNAMICS',
           transform=ax.transAxes, fontsize=11, ha='center', va='top',
           bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))


def main():
    """Generate all visualizations."""
    os.makedirs('verification/plots', exist_ok=True)

    print("Generating vertex-face duality visualizations...")

    # Main comparison figure
    fig1 = create_comparison_figure()
    fig1.savefig('verification/plots/vertex_face_duality_comparison.png',
                dpi=150, bbox_inches='tight')
    plt.close(fig1)
    print("  Saved: verification/plots/vertex_face_duality_comparison.png")

    # Detailed figure
    fig2 = create_detailed_duality_figure()
    fig2.savefig('verification/plots/vertex_face_duality_detailed.png',
                dpi=150, bbox_inches='tight')
    plt.close(fig2)
    print("  Saved: verification/plots/vertex_face_duality_detailed.png")

    print("\nVisualization complete!")


if __name__ == "__main__":
    main()
