#!/usr/bin/env python3
"""
Figure: Winding Number Origin of Cosmic Asymmetries

Visualizes the topological winding number w = +1 of the color phase cycle
R → G → B, which is the single geometric invariant underlying three cosmic
asymmetries (weak chirality, time's arrow, matter dominance).

Key physics:
- Color phases φ_R = 0, φ_G = 2π/3, φ_B = 4π/3 are fixed by Z_3 symmetry
- Going R → G → B → R accumulates total phase 2π → winding number w = +1
- This is a topological invariant: cannot be deformed to w = 0 without
  breaking Z_3 symmetry
- The sign of w determines the sign of all three asymmetries

Proof Document: docs/proofs/foundations/Theorem-0.0.5-Chirality-Selection-From-Geometry.md
Paper Section: Section on Topological Chirality (Trinity of Asymmetry)

Output: fig_trinity_asymmetry.pdf, fig_trinity_asymmetry.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, Arc, Wedge
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
    'axes.labelsize': 13,
    'axes.titlesize': 13,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# Colors
COLOR_RED = '#C0392B'
COLOR_GREEN = '#27AE60'
COLOR_BLUE = '#2980B9'
COLOR_DARK = '#1C2833'
COLOR_GRAY = '#7F8C8D'


def create_figure():
    """
    Create a two-panel figure showing the winding number.

    Left: Phase circle with R, G, B positions and winding direction
    Right: Unwrapped phase showing linear accumulation → w = 1
    """
    fig, axes = plt.subplots(1, 2, figsize=(9, 5.2))

    # ============ LEFT PANEL: Phase Circle ============
    ax1 = axes[0]
    ax1.set_xlim(-1.6, 1.6)
    ax1.set_ylim(-1.6, 1.6)
    ax1.set_aspect('equal')
    ax1.axis('off')

    # Draw unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), color=COLOR_GRAY, lw=1.5, zorder=1)

    # Phase positions
    phases = [
        (0, COLOR_RED, r'R', r'$\phi_R = 0$'),
        (2*np.pi/3, COLOR_GREEN, r'G', r'$\phi_G = \frac{2\pi}{3}$'),
        (4*np.pi/3, COLOR_BLUE, r'B', r'$\phi_B = \frac{4\pi}{3}$'),
    ]

    # Draw phase points and labels
    for phi, color, label, phase_label in phases:
        x, y = np.cos(phi), np.sin(phi)
        # Point on circle
        ax1.plot(x, y, 'o', color=color, markersize=14,
                markeredgecolor='white', markeredgewidth=2, zorder=10)
        # Color label (R, G, B) inside
        ax1.text(x, y, label, ha='center', va='center',
                fontsize=9, fontweight='bold', color='white', zorder=11)
        # Phase value outside
        label_r = 1.35
        lx, ly = label_r * np.cos(phi), label_r * np.sin(phi)
        ax1.text(lx, ly, phase_label, ha='center', va='center',
                fontsize=10, color=color)

    # Draw arrows showing the cycle R → G → B → R
    arrow_r = 0.75  # radius for arrows (inside the circle)
    arrow_style = dict(arrowstyle='->', color=COLOR_DARK, lw=2,
                       mutation_scale=15, connectionstyle='arc3,rad=0.3')

    # R → G
    ax1.annotate('',
                xy=(arrow_r * np.cos(2*np.pi/3 - 0.15), arrow_r * np.sin(2*np.pi/3 - 0.15)),
                xytext=(arrow_r * np.cos(0.15), arrow_r * np.sin(0.15)),
                arrowprops=arrow_style, zorder=5)
    # G → B
    ax1.annotate('',
                xy=(arrow_r * np.cos(4*np.pi/3 - 0.15), arrow_r * np.sin(4*np.pi/3 - 0.15)),
                xytext=(arrow_r * np.cos(2*np.pi/3 + 0.15), arrow_r * np.sin(2*np.pi/3 + 0.15)),
                arrowprops=arrow_style, zorder=5)
    # B → R (completing the cycle)
    ax1.annotate('',
                xy=(arrow_r * np.cos(-0.15), arrow_r * np.sin(-0.15)),
                xytext=(arrow_r * np.cos(4*np.pi/3 + 0.15), arrow_r * np.sin(4*np.pi/3 + 0.15)),
                arrowprops=arrow_style, zorder=5)

    # Phase increments - positioned outside the arrows (between arrows and circle edge)
    label_r = 0.52  # inside the arrow path
    # R → G: midpoint angle ~ π/3
    ax1.text(label_r * np.cos(np.pi/3), label_r * np.sin(np.pi/3),
            r'$+\frac{2\pi}{3}$', ha='center', va='center',
            fontsize=9, color=COLOR_DARK)
    # G → B: midpoint angle ~ π
    ax1.text(label_r * np.cos(np.pi), label_r * np.sin(np.pi),
            r'$+\frac{2\pi}{3}$', ha='center', va='center',
            fontsize=9, color=COLOR_DARK)
    # B → R: midpoint angle ~ 5π/3
    ax1.text(label_r * np.cos(5*np.pi/3), label_r * np.sin(5*np.pi/3),
            r'$+\frac{2\pi}{3}$', ha='center', va='center',
            fontsize=9, color=COLOR_DARK)

    # Center annotation
    ax1.text(0, 0, r'$w = +1$', ha='center', va='center',
            fontsize=14, fontweight='bold', color=COLOR_DARK,
            bbox=dict(boxstyle='round,pad=0.3', facecolor='#F9E79F',
                     edgecolor='#F4D03F', linewidth=2))

    ax1.set_title(r'(a) Phase circle: $\phi_c$ mod $2\pi$', fontsize=12, pad=10)

    # ============ RIGHT PANEL: Unwrapped Phase ============
    ax2 = axes[1]

    # x-axis: color index (R=0, G=1, B=2, R=3)
    # y-axis: accumulated phase

    colors_x = [0, 1, 2, 3]
    phases_y = [0, 2*np.pi/3, 4*np.pi/3, 2*np.pi]
    colors = [COLOR_RED, COLOR_GREEN, COLOR_BLUE, COLOR_RED]
    labels = ['R', 'G', 'B', 'R']

    # Plot the staircase / linear increase
    ax2.plot(colors_x, phases_y, '-', color=COLOR_DARK, lw=2, zorder=2)

    # Plot points
    for i, (x, y, c, lab) in enumerate(zip(colors_x, phases_y, colors, labels)):
        ax2.plot(x, y, 'o', color=c, markersize=12,
                markeredgecolor='white', markeredgewidth=2, zorder=10)
        ax2.text(x, y, lab, ha='center', va='center',
                fontsize=8, fontweight='bold', color='white', zorder=11)

    # Dashed line showing the slope = 2π/3 per step
    x_line = np.linspace(-0.2, 3.2, 50)
    y_line = (2*np.pi/3) * x_line
    ax2.plot(x_line, y_line, '--', color=COLOR_GRAY, lw=1, alpha=0.7, zorder=1)

    # Annotations
    ax2.annotate('', xy=(3, 2*np.pi), xytext=(0, 0),
                arrowprops=dict(arrowstyle='->', color='#E74C3C', lw=2.5,
                              connectionstyle='arc3,rad=0'))
    # Calculate rotation angle accounting for axis aspect ratio
    # Line goes from (0,0) to (3, 2π) in data coordinates
    # Need to convert to display angle
    x_range = 4.0  # xlim is -0.4 to 3.6
    y_range = 2*np.pi + 1.5  # ylim is -0.5 to 2π+1
    data_slope = (2*np.pi) / 3
    display_slope = data_slope * (x_range / y_range)
    rotation_angle = np.degrees(np.arctan(display_slope))
    ax2.text(1.5, np.pi, r'Total: $\Delta\phi = 2\pi$',
            ha='center', va='bottom', fontsize=11, color='#E74C3C',
            fontweight='bold', rotation=rotation_angle)

    # Winding number formula
    ax2.text(2.5, 0.8, r'$w = \frac{\Delta\phi}{2\pi} = \frac{2\pi}{2\pi} = 1$',
            ha='center', va='center', fontsize=11, color=COLOR_DARK,
            bbox=dict(boxstyle='round,pad=0.3', facecolor='#F9E79F',
                     edgecolor='#F4D03F', linewidth=2))

    # Axis setup
    ax2.set_xlim(-0.4, 3.6)
    ax2.set_ylim(-0.5, 2*np.pi + 1)
    ax2.set_xticks([0, 1, 2, 3])
    ax2.set_xticklabels(['R', 'G', 'B', 'R'])
    ax2.set_yticks([0, 2*np.pi/3, 4*np.pi/3, 2*np.pi])
    ax2.set_yticklabels([r'$0$', r'$\frac{2\pi}{3}$', r'$\frac{4\pi}{3}$', r'$2\pi$'])
    ax2.set_xlabel('Color index (cyclic)', fontsize=11)
    ax2.set_ylabel(r'Accumulated phase $\phi$', fontsize=11)
    ax2.set_title(r'(b) Unwrapped: one full winding', fontsize=12, pad=10)
    ax2.grid(True, alpha=0.3, linestyle='-')
    ax2.set_axisbelow(True)

    # Add horizontal lines at multiples of 2π/3
    for y in [2*np.pi/3, 4*np.pi/3, 2*np.pi]:
        ax2.axhline(y, color=COLOR_GRAY, lw=0.5, alpha=0.5, zorder=0)

    plt.tight_layout()

    # Add overall caption at bottom
    fig.text(0.5, 0.02,
             r'The $\mathbb{Z}_3$-symmetric phases complete one cycle: '
             r'$w = +1$ is topologically protected.',
             ha='center', va='bottom', fontsize=10, style='italic',
             color=COLOR_DARK)

    plt.subplots_adjust(bottom=0.15)

    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_trinity_asymmetry.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {output_path}")

    plt.close('all')


if __name__ == '__main__':
    main()
