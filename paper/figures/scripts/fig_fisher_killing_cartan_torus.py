#!/usr/bin/env python3
"""
Figure: Fisher-Killing Equivalence on the Cartan Torus

Visualizes the core result: for S_N-symmetric statistical manifolds, the Fisher
information metric equals the Killing form metric of SU(N). For N=3, this
manifests on the 2D Cartan torus as a flat metric where geodesics are straight lines.

Key physics:
- The Cartan torus T² is the natural phase space for SU(3) color field evolution
- Fisher metric (information geometry) = Killing metric (Lie algebra) = flat
- Geodesics are straight lines on this flat torus
- Phase wheels show the physical meaning: R, G, B color field phases

Proof Document: docs/proofs/foundations/Lemma-Fisher-Killing-Equivalence.md
Paper Section: Part II - Emergent Quantum Structure

Output: fig_fisher_killing_cartan_torus.pdf, fig_fisher_killing_cartan_torus.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
from matplotlib.lines import Line2D
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'serif',
    'font.serif': ['Times New Roman', 'DejaVu Serif'],
    'font.size': 11,
    'axes.labelsize': 12,
    'axes.titlesize': 14,
    'legend.fontsize': 10,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# Color palette
COLOR_RED = '#E74C3C'      # Red color field
COLOR_GREEN = '#27AE60'    # Green color field
COLOR_BLUE = '#3498DB'     # Blue color field


def draw_phase_wheel(ax, cx, cy, psi1, psi2, radius=18, edge_color='gray'):
    """
    Draw a phase wheel showing R, G, B phases at position (cx, cy).

    The wheel shows the three color field phases on a circle:
    - φ_R = 0 (reference, at 3 o'clock position)
    - φ_G = ψ₁
    - φ_B = ψ₁ + ψ₂

    cx, cy: center position in data coordinates (degrees)
    psi1, psi2: phase differences in radians
    radius: wheel radius in data coordinates
    """
    from matplotlib.patches import Wedge

    # Draw wheel background
    lw = 2.5 if edge_color != 'gray' else 1
    wheel_bg = Circle((cx, cy), radius, facecolor='white',
                     edgecolor=edge_color, linewidth=lw, alpha=0.9, zorder=15)
    ax.add_patch(wheel_bg)

    # Phase positions (normalized to [0, 2π))
    phi_R = 0
    phi_G = psi1 % (2 * np.pi)
    phi_B = (psi1 + psi2) % (2 * np.pi)

    # Draw phase markers as colored dots on the wheel edge
    marker_radius = radius * 0.7
    marker_size = radius * 0.18  # Size of the split circle (match dot size)

    # Check for overlapping phases (within tolerance)
    tolerance = 0.1  # radians (~6 degrees)

    def phases_overlap(p1, p2):
        diff = abs(p1 - p2)
        return diff < tolerance or abs(diff - 2*np.pi) < tolerance

    # Check all overlap combinations
    RG_overlap = phases_overlap(phi_R, phi_G)
    RB_overlap = phases_overlap(phi_R, phi_B)
    GB_overlap = phases_overlap(phi_G, phi_B)

    # Case 1: All three overlap (triplet split)
    if RG_overlap and RB_overlap and GB_overlap:
        x = cx + marker_radius * np.cos(phi_R)
        y = cy + marker_radius * np.sin(phi_R)
        # Three equal wedges (120° each)
        wedge_R = Wedge((x, y), marker_size, 0, 120,
                        facecolor=COLOR_RED, edgecolor='white', linewidth=1, zorder=20)
        wedge_G = Wedge((x, y), marker_size, 120, 240,
                        facecolor=COLOR_GREEN, edgecolor='white', linewidth=1, zorder=20)
        wedge_B = Wedge((x, y), marker_size, 240, 360,
                        facecolor=COLOR_BLUE, edgecolor='white', linewidth=1, zorder=20)
        ax.add_patch(wedge_R)
        ax.add_patch(wedge_G)
        ax.add_patch(wedge_B)

    # Case 2: R and G overlap (but not B)
    elif RG_overlap and not RB_overlap:
        x = cx + marker_radius * np.cos(phi_R)
        y = cy + marker_radius * np.sin(phi_R)
        angle = np.degrees(phi_R)
        # Two half circles for R and G
        wedge1 = Wedge((x, y), marker_size, angle + 90, angle + 270,
                       facecolor=COLOR_RED, edgecolor='white', linewidth=1, zorder=20)
        wedge2 = Wedge((x, y), marker_size, angle - 90, angle + 90,
                       facecolor=COLOR_GREEN, edgecolor='white', linewidth=1, zorder=20)
        ax.add_patch(wedge1)
        ax.add_patch(wedge2)
        # Draw B separately
        x_b = cx + marker_radius * np.cos(phi_B)
        y_b = cy + marker_radius * np.sin(phi_B)
        ax.plot(x_b, y_b, 'o', color=COLOR_BLUE, markersize=7,
               markeredgecolor='white', markeredgewidth=1, zorder=20)

    # Case 3: R and B overlap (but not G)
    elif RB_overlap and not RG_overlap:
        x = cx + marker_radius * np.cos(phi_R)
        y = cy + marker_radius * np.sin(phi_R)
        angle = np.degrees(phi_R)
        # Two half circles for R and B
        wedge1 = Wedge((x, y), marker_size, angle + 90, angle + 270,
                       facecolor=COLOR_RED, edgecolor='white', linewidth=1, zorder=20)
        wedge2 = Wedge((x, y), marker_size, angle - 90, angle + 90,
                       facecolor=COLOR_BLUE, edgecolor='white', linewidth=1, zorder=20)
        ax.add_patch(wedge1)
        ax.add_patch(wedge2)
        # Draw G separately
        x_g = cx + marker_radius * np.cos(phi_G)
        y_g = cy + marker_radius * np.sin(phi_G)
        ax.plot(x_g, y_g, 'o', color=COLOR_GREEN, markersize=7,
               markeredgecolor='white', markeredgewidth=1, zorder=20)

    # Case 4: G and B overlap (but not R)
    elif GB_overlap and not RG_overlap:
        x = cx + marker_radius * np.cos(phi_G)
        y = cy + marker_radius * np.sin(phi_G)
        angle = np.degrees(phi_G)
        # Two half circles for G and B
        wedge1 = Wedge((x, y), marker_size, angle + 90, angle + 270,
                       facecolor=COLOR_GREEN, edgecolor='white', linewidth=1, zorder=20)
        wedge2 = Wedge((x, y), marker_size, angle - 90, angle + 90,
                       facecolor=COLOR_BLUE, edgecolor='white', linewidth=1, zorder=20)
        ax.add_patch(wedge1)
        ax.add_patch(wedge2)
        # Draw R separately
        x_r = cx + marker_radius * np.cos(phi_R)
        y_r = cy + marker_radius * np.sin(phi_R)
        ax.plot(x_r, y_r, 'o', color=COLOR_RED, markersize=7,
               markeredgecolor='white', markeredgewidth=1, zorder=20)

    # Case 5: No overlaps - draw all three as separate dots
    else:
        phases = [(phi_R, COLOR_RED), (phi_G, COLOR_GREEN), (phi_B, COLOR_BLUE)]
        for phi, color in phases:
            x = cx + marker_radius * np.cos(phi)
            y = cy + marker_radius * np.sin(phi)
            ax.plot(x, y, 'o', color=color, markersize=7,
                   markeredgecolor='white', markeredgewidth=1, zorder=20)


def compute_geodesic(start, direction, n_points=100, length=2*np.pi):
    """
    Compute geodesic on flat torus starting from 'start' in 'direction'.
    On a flat torus, geodesics are straight lines (mod torus identification).
    """
    t = np.linspace(0, length, n_points)
    psi1 = (start[0] + direction[0] * t) % (2 * np.pi)
    psi2 = (start[1] + direction[1] * t) % (2 * np.pi)
    return psi1, psi2


def create_figure():
    """
    Create single-panel figure showing Fisher-Killing equivalence.

    Core message: On the Cartan torus, geodesics are straight lines
    because g_Fisher = g_Killing = flat metric.
    """
    fig, ax = plt.subplots(1, 1, figsize=(8, 8))

    # Add probability distribution as background
    n_grid = 200
    psi1_range = np.linspace(0, 2*np.pi, n_grid)
    psi2_range = np.linspace(0, 2*np.pi, n_grid)
    PSI1, PSI2 = np.meshgrid(psi1_range, psi2_range)

    # Probability p = |chi_R + chi_G + chi_B|^2
    chi_total = 1 + np.exp(1j * PSI1) + np.exp(1j * (PSI1 + PSI2))
    P = np.abs(chi_total)**2

    ax.imshow(P, extent=[0, 360, 0, 360], origin='lower',
              cmap='viridis', aspect='equal', alpha=0.3, vmin=0, vmax=9, zorder=0)

    # Draw multiple geodesics from different starting points
    np.random.seed(42)
    n_geodesics = 6

    # Use light grey for all background geodesics
    geodesic_colors = ['#AAAAAA'] * 6

    for i in range(n_geodesics):
        # Different starting points spread across the torus
        start = np.array([
            (i * 0.7 + 0.3) % (2*np.pi),
            (i * 0.5 + 0.2) % (2*np.pi)
        ])

        # Different directions
        angle = i * np.pi / n_geodesics + 0.2
        direction = np.array([np.cos(angle), np.sin(angle)])

        # Shorten the grey geodesic (i=5) to avoid wrapping
        geo_length = 1.8*np.pi if i == 5 else 2.5*np.pi
        psi1_geo, psi2_geo = compute_geodesic(start, direction, n_points=200, length=geo_length)

        # Plot geodesic
        ax.plot(np.degrees(psi1_geo), np.degrees(psi2_geo),
                color=geodesic_colors[i], linewidth=2, alpha=0.7, zorder=5)

        # Add arrows along the geodesic to show direction
        arrow_indices = [40, 100, 160]
        for arr_idx in arrow_indices:
            if arr_idx + 5 < len(psi1_geo):
                ax.annotate('',
                    xy=(np.degrees(psi1_geo[arr_idx+5]), np.degrees(psi2_geo[arr_idx+5])),
                    xytext=(np.degrees(psi1_geo[arr_idx]), np.degrees(psi2_geo[arr_idx])),
                    arrowprops=dict(arrowstyle='->', color=geodesic_colors[i], lw=2),
                    zorder=6)

        # Starting point marker
        ax.plot(np.degrees(start[0]), np.degrees(start[1]), 'o',
                color=geodesic_colors[i], markersize=8, markeredgecolor='white',
                markeredgewidth=1.5, zorder=10)

    # Grid of phase wheels showing phase patterns across the torus
    # Grid from (0, 0) to (360, 360) at 60° intervals
    grid_values = [0, 60, 120, 180, 240, 300, 360]

    for cx in grid_values:
        for cy in grid_values:
            psi1_rad = np.radians(cx)
            psi2_rad = np.radians(cy)
            # Highlight color-neutral configurations at (120, 120) and (240, 240)
            if (cx, cy) in [(120, 120), (240, 240)]:
                edge_color = '#FFD700'  # Gold
            else:
                edge_color = 'gray'
            draw_phase_wheel(ax, cx, cy, psi1_rad, psi2_rad, radius=20, edge_color=edge_color)

    # Legend for phase wheel markers
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_RED,
               markersize=10, markeredgecolor='white', label=r'$\phi_R = 0$ (ref)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_GREEN,
               markersize=10, markeredgecolor='white', label=r'$\phi_G = \psi_1$'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_BLUE,
               markersize=10, markeredgecolor='white', label=r'$\phi_B = \psi_1 + \psi_2$'),
    ]
    legend = ax.legend(handles=legend_elements, loc='lower center', fontsize=10,
                       title='Phase markers', title_fontsize=10,
                       framealpha=1.0, facecolor='white', edgecolor='gray',
                       bbox_to_anchor=(0.5, 1.02), ncol=3)
    legend.set_zorder(100)  # Put legend on top of all elements

    ax.set_xlabel(r'$\psi_1 = \phi_G - \phi_R$ (degrees)')
    ax.set_ylabel(r'$\psi_2 = \phi_B - \phi_G$ (degrees)')
    ax.set_title(r'Fisher-Killing Equivalence on the Cartan Torus $\mathbb{T}^2$', fontsize=14, pad=50)
    ax.set_xlim(-30, 390)
    ax.set_ylim(-30, 390)
    ax.set_xticks([0, 60, 120, 180, 240, 300, 360])
    ax.set_yticks([0, 60, 120, 180, 240, 300, 360])
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3, linestyle='-', linewidth=0.5)

    # Key result - placed outside the graph
    fig.text(0.5, 0.02, r'$g_{ij}^{\mathrm{Fisher}} = g_{ij}^{\mathrm{Killing}} = \delta_{ij}$'
             r'$\quad \Rightarrow \quad$'
             r'Flat metric $\Rightarrow$ Geodesics are straight lines',
             ha='center', fontsize=12, fontweight='bold',
             bbox=dict(boxstyle='round,pad=0.4', facecolor='lightyellow',
                      edgecolor='goldenrod', linewidth=2, alpha=0.95))

    plt.tight_layout(rect=[0, 0.06, 1, 0.88])  # Leave space at bottom for text and top for legend
    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    # Save in both formats
    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_fisher_killing_cartan_torus.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {output_path}")

    plt.close('all')


if __name__ == '__main__':
    main()
