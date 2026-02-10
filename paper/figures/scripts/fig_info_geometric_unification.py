#!/usr/bin/env python3
"""
Figure: Information-Geometric Unification of Space and Time

Visualizes how spatial adjacency and temporal succession both emerge from
geodesic structure on the Cartan torus equipped with the Fisher metric.

Key physics:
- Configuration space is the Cartan torus T² with flat metric g = δᵢⱼ
- Geodesics are straight lines (flat metric)
- Time = arc length along geodesics
- Space = directions perpendicular to geodesic (minimal KL divergence)
- One geometric structure → both space and time

Proof Document: docs/proofs/foundations/Theorem-0.0.17-Information-Geometric-Unification.md
Paper Section: Section 4.5 - Information-Geometric Unification of Space and Time

Output: fig_info_geometric_unification.pdf, fig_info_geometric_unification.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Circle, Rectangle, FancyBboxPatch
from matplotlib.lines import Line2D
import os

# Create output directory
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style
plt.rcParams.update({
    'font.family': 'serif',
    'font.serif': ['Times New Roman', 'DejaVu Serif'],
    'font.size': 11,
    'axes.labelsize': 12,
    'axes.titlesize': 13,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# Colors
COLOR_TIME = '#C0392B'      # Red for time/geodesic
COLOR_SPACE = '#2980B9'     # Blue for space/adjacency
COLOR_DARK = '#1C2833'
COLOR_GRAY = '#7F8C8D'
COLOR_LIGHT = '#F4F6F7'


def create_figure():
    """
    Create figure showing unification of space and time from geodesic structure.

    Single panel showing the Cartan torus with:
    - A geodesic trajectory (time direction)
    - Perpendicular directions (spatial adjacency)
    - Clear labeling showing both emerge from same metric
    """
    fig, ax = plt.subplots(1, 1, figsize=(7, 6.5))

    # Draw the torus as a square [0, 2π] × [0, 2π] with periodic boundaries
    torus_size = 2 * np.pi

    # Light background for the torus
    torus_bg = Rectangle((0, 0), torus_size, torus_size,
                          facecolor=COLOR_LIGHT, edgecolor=COLOR_DARK,
                          linewidth=2, zorder=1)
    ax.add_patch(torus_bg)

    # Draw periodic boundary indicators (dashed lines showing identification)
    for i in range(1, 3):
        # Vertical dashed lines at edges
        ax.axvline(0, color=COLOR_GRAY, linestyle='--', lw=1, alpha=0.5)
        ax.axvline(torus_size, color=COLOR_GRAY, linestyle='--', lw=1, alpha=0.5)
        # Horizontal dashed lines at edges
        ax.axhline(0, color=COLOR_GRAY, linestyle='--', lw=1, alpha=0.5)
        ax.axhline(torus_size, color=COLOR_GRAY, linestyle='--', lw=1, alpha=0.5)

    # === GEODESIC (TIME DIRECTION) ===
    # Draw a geodesic - straight line on the flat torus
    # Use a slope that wraps nicely
    slope = 0.6
    t_vals = np.linspace(0, 8, 200)

    # Starting point
    x0, y0 = 0.8, 0.5

    # Geodesic coordinates (mod 2π for wrapping)
    geo_x = (x0 + t_vals) % torus_size
    geo_y = (y0 + slope * t_vals) % torus_size

    # Find discontinuities (where wrapping occurs) and plot segments
    dx = np.diff(geo_x)
    dy = np.diff(geo_y)
    breaks = np.where((np.abs(dx) > np.pi) | (np.abs(dy) > np.pi))[0]

    segments = np.split(np.arange(len(t_vals)), breaks + 1)

    for seg in segments:
        if len(seg) > 1:
            ax.plot(geo_x[seg], geo_y[seg], '-', color=COLOR_TIME, lw=3, zorder=5)

    # Add arrows along the geodesic to show time direction
    arrow_positions = [0.5, 2.0, 3.5, 5.0, 6.5]
    for t_arr in arrow_positions:
        xa = (x0 + t_arr) % torus_size
        ya = (y0 + slope * t_arr) % torus_size
        # Direction vector (normalized)
        dx_arr = 1.0 / np.sqrt(1 + slope**2)
        dy_arr = slope / np.sqrt(1 + slope**2)
        # Check we're not at a wrap point
        xa_next = (x0 + t_arr + 0.3) % torus_size
        if abs(xa_next - xa) < 1:  # Not wrapping
            ax.annotate('', xy=(xa + 0.25*dx_arr, ya + 0.25*dy_arr),
                       xytext=(xa, ya),
                       arrowprops=dict(arrowstyle='->', color=COLOR_TIME, lw=2),
                       zorder=6)

    # === SPATIAL DIRECTIONS (PERPENDICULAR TO GEODESIC) ===
    # At a few points along the geodesic, show perpendicular directions
    spatial_points = [1.5, 4.0]
    perp_dx = -slope / np.sqrt(1 + slope**2)
    perp_dy = 1.0 / np.sqrt(1 + slope**2)

    for t_sp in spatial_points:
        xp = (x0 + t_sp) % torus_size
        yp = (y0 + slope * t_sp) % torus_size

        # Draw perpendicular line segment
        perp_len = 0.8
        x1 = xp - perp_len * perp_dx
        y1 = yp - perp_len * perp_dy
        x2 = xp + perp_len * perp_dx
        y2 = yp + perp_len * perp_dy

        ax.plot([x1, x2], [y1, y2], '-', color=COLOR_SPACE, lw=2.5, zorder=4)

        # Arrows on both ends
        ax.annotate('', xy=(x2, y2), xytext=(xp, yp),
                   arrowprops=dict(arrowstyle='->', color=COLOR_SPACE, lw=2),
                   zorder=6)
        ax.annotate('', xy=(x1, y1), xytext=(xp, yp),
                   arrowprops=dict(arrowstyle='->', color=COLOR_SPACE, lw=2),
                   zorder=6)

        # Point on geodesic
        ax.plot(xp, yp, 'o', color=COLOR_TIME, markersize=10,
               markeredgecolor='white', markeredgewidth=2, zorder=10)

    # === LABELS ===
    # Time label along geodesic (positioned in upper left area)
    ax.text(0.4, 4.8, r'$\tau$ (time)',
           fontsize=12, color=COLOR_TIME, fontweight='bold',
           ha='left', va='top')
    ax.text(0.4, 4.45, r'arc length along geodesic',
           fontsize=10, color=COLOR_TIME, ha='left', va='top')

    # Space label perpendicular (near the upper spatial arrows)
    t_sp = spatial_points[1]
    xsp = (x0 + t_sp) % torus_size
    ysp = (y0 + slope * t_sp) % torus_size
    ax.text(xsp + perp_len * perp_dx + 0.2, ysp + perp_len * perp_dy + 0.25,
           r'spatial adjacency',
           fontsize=11, color=COLOR_SPACE, fontweight='bold',
           ha='center', va='bottom')

    # === METRIC BOX ===
    # Show the metric that unifies both (positioned in lower right, clear of geodesic)
    box_x, box_y = 4.5, 0.25
    box_w, box_h = 1.6, 1.1
    metric_box = FancyBboxPatch((box_x, box_y), box_w, box_h,
                                 boxstyle="round,pad=0.05,rounding_size=0.1",
                                 facecolor='white', edgecolor=COLOR_DARK,
                                 linewidth=1.5, zorder=8)
    ax.add_patch(metric_box)
    ax.text(box_x + box_w/2, box_y + box_h - 0.15, r'Fisher metric',
           fontsize=10, fontweight='bold', ha='center', va='top', color=COLOR_DARK, zorder=9)
    ax.text(box_x + box_w/2, box_y + box_h/2,
           r'$g_{ij} = \delta_{ij}$',
           fontsize=12, ha='center', va='center', color=COLOR_DARK, zorder=9)
    ax.text(box_x + box_w/2, box_y + 0.15, r'(flat)',
           fontsize=9, ha='center', va='bottom', color=COLOR_GRAY, style='italic', zorder=9)

    # === AXIS LABELS ===
    ax.set_xlabel(r'$\psi_1 = \phi_G - \phi_R$', fontsize=12)
    ax.set_ylabel(r'$\psi_2 = \phi_B - \phi_G$', fontsize=12)

    # Axis setup
    margin = 0.3
    ax.set_xlim(-margin, torus_size + margin)
    ax.set_ylim(-margin, torus_size + margin)
    ax.set_xticks([0, np.pi, 2*np.pi])
    ax.set_xticklabels([r'$0$', r'$\pi$', r'$2\pi$'])
    ax.set_yticks([0, np.pi, 2*np.pi])
    ax.set_yticklabels([r'$0$', r'$\pi$', r'$2\pi$'])
    ax.set_aspect('equal')

    # Title
    ax.set_title(r'Cartan Torus $T^2$: Geodesics Unify Space and Time',
                fontsize=13, fontweight='bold', pad=10)

    # Legend
    legend_elements = [
        Line2D([0], [0], color=COLOR_TIME, lw=3, label=r'Geodesic $\to$ time ($\tau$)'),
        Line2D([0], [0], color=COLOR_SPACE, lw=2.5, label=r'Perpendicular $\to$ space'),
    ]
    ax.legend(handles=legend_elements, loc='upper left', fontsize=10,
             framealpha=0.95, edgecolor=COLOR_GRAY)

    plt.tight_layout()

    # Bottom annotation (after tight_layout)
    fig.text(0.5, 0.02,
             r'One metric, one structure $\Rightarrow$ both spatial adjacency and temporal succession',
             ha='center', va='bottom', fontsize=11, style='italic', color=COLOR_DARK)

    plt.subplots_adjust(bottom=0.12)

    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_info_geometric_unification.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {output_path}")

    plt.close('all')


if __name__ == '__main__':
    main()
