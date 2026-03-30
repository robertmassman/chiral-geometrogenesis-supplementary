#!/usr/bin/env python3
"""
Figure: E² Cancellation in e⁺e⁻ → W⁺W⁻ Gauge Boson Production

Visualizes the three Feynman diagrams contributing to W pair production
and how their high-energy amplitudes cancel exactly due to gauge invariance.

Key physics:
- Three diagrams: t-channel ν exchange, s-channel γ, s-channel Z
- Each grows as E² individually at high energy
- Total amplitude: a_ν + a_γ + a_Z = 1 - sin²θ_W - cos²θ_W = 0
- Cancellation automatic from SU(2)_L × U(1)_Y gauge structure (D₄ root system)

Proof Document: docs/proofs/Phase6/Theorem-6.6.1-Electroweak-Scattering.md (§4.3)
Paper Section: Section 6.4 (W Pair Production and Gauge Cancellations)

Output: fig_ww_e2_cancellation.pdf, fig_ww_e2_cancellation.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Circle, FancyBboxPatch, Arc
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
    'font.size': 12,
    'axes.labelsize': 14,
    'axes.titlesize': 14,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# Colors
COLOR_ELECTRON = '#2980B9'  # Blue - electrons/positrons
COLOR_W_BOSON = '#E74C3C'   # Red - W bosons
COLOR_NEUTRINO = '#27AE60'  # Green - neutrino
COLOR_PHOTON = '#F39C12'    # Orange - photon
COLOR_Z_BOSON = '#9B59B6'   # Purple - Z boson
COLOR_DARK = '#1C2833'
COLOR_POSITIVE = '#27AE60'  # Green for positive
COLOR_NEGATIVE = '#E74C3C'  # Red for negative


def draw_wavy_line(ax, x1, y1, x2, y2, color='black', lw=2, n_waves=4, amplitude=0.08):
    """Draw a wavy line representing a boson propagator."""
    t = np.linspace(0, 1, 100)
    x = x1 + (x2 - x1) * t
    y = y1 + (y2 - y1) * t

    # Perpendicular direction for waves
    dx, dy = x2 - x1, y2 - y1
    length = np.sqrt(dx**2 + dy**2)
    nx, ny = -dy / length, dx / length

    # Add sinusoidal perpendicular displacement
    wave = amplitude * np.sin(n_waves * 2 * np.pi * t)
    x_wave = x + wave * nx
    y_wave = y + wave * ny

    ax.plot(x_wave, y_wave, color=color, lw=lw, solid_capstyle='round')


def draw_fermion_line(ax, x1, y1, x2, y2, color='black', lw=2, arrow_pos=0.5):
    """Draw a fermion line with arrow at specified position."""
    ax.plot([x1, x2], [y1, y2], color=color, lw=lw, solid_capstyle='round')

    # Arrow at midpoint
    mid_x = x1 + (x2 - x1) * arrow_pos
    mid_y = y1 + (y2 - y1) * arrow_pos
    dx = (x2 - x1) * 0.01
    dy = (y2 - y1) * 0.01
    ax.annotate('', xy=(mid_x + dx, mid_y + dy), xytext=(mid_x, mid_y),
                arrowprops=dict(arrowstyle='->', color=color, lw=lw,
                              mutation_scale=12))


def draw_vertex(ax, x, y, size=0.06, color=COLOR_DARK):
    """Draw an interaction vertex."""
    vertex = Circle((x, y), size, facecolor=color,
                   edgecolor='white', linewidth=1.5, zorder=10)
    ax.add_patch(vertex)


def draw_t_channel_diagram(ax, x_offset=0, y_offset=0):
    """Draw t-channel neutrino exchange diagram."""
    # Coordinates
    e_in = (x_offset - 0.8, y_offset + 0.6)   # e⁻ incoming
    e_out = (x_offset + 0.8, y_offset + 0.6)  # W⁻ outgoing
    p_in = (x_offset - 0.8, y_offset - 0.6)   # e⁺ incoming
    p_out = (x_offset + 0.8, y_offset - 0.6)  # W⁺ outgoing
    v1 = (x_offset - 0.2, y_offset + 0.3)     # Top vertex
    v2 = (x_offset + 0.2, y_offset - 0.3)     # Bottom vertex

    # Incoming e⁻
    draw_fermion_line(ax, e_in[0], e_in[1], v1[0], v1[1],
                     color=COLOR_ELECTRON, lw=2)
    # Neutrino propagator (dashed)
    ax.plot([v1[0], v2[0]], [v1[1], v2[1]], '--',
           color=COLOR_NEUTRINO, lw=2.5)
    # Incoming e⁺
    draw_fermion_line(ax, p_in[0], p_in[1], v2[0], v2[1],
                     color=COLOR_ELECTRON, lw=2)
    # Outgoing W⁻
    draw_wavy_line(ax, v1[0], v1[1], e_out[0], e_out[1],
                  color=COLOR_W_BOSON, lw=2)
    # Outgoing W⁺
    draw_wavy_line(ax, v2[0], v2[1], p_out[0], p_out[1],
                  color=COLOR_W_BOSON, lw=2)

    # Vertices
    draw_vertex(ax, v1[0], v1[1])
    draw_vertex(ax, v2[0], v2[1])

    # Labels
    ax.text(e_in[0] - 0.12, e_in[1], r'$e^-$', fontsize=13, ha='right', va='center')
    ax.text(p_in[0] - 0.12, p_in[1], r'$e^+$', fontsize=13, ha='right', va='center')
    ax.text(e_out[0] + 0.12, e_out[1], r'$W^-$', fontsize=13, ha='left', va='center',
           color=COLOR_W_BOSON)
    ax.text(p_out[0] + 0.12, p_out[1], r'$W^+$', fontsize=13, ha='left', va='center',
           color=COLOR_W_BOSON)
    ax.text((v1[0] + v2[0])/2 - 0.18, (v1[1] + v2[1])/2, r'$\nu_e$',
           fontsize=13, ha='right', va='center', color=COLOR_DARK)


def draw_s_channel_diagram(ax, x_offset=0, y_offset=0, propagator_label=r'$\gamma$',
                           propagator_color=COLOR_PHOTON):
    """Draw s-channel diagram (γ or Z exchange)."""
    # Coordinates
    e_in = (x_offset - 0.8, y_offset + 0.6)   # e⁻ incoming
    p_in = (x_offset - 0.8, y_offset - 0.6)   # e⁺ incoming
    e_out = (x_offset + 0.8, y_offset + 0.6)  # W⁻ outgoing
    p_out = (x_offset + 0.8, y_offset - 0.6)  # W⁺ outgoing
    v1 = (x_offset - 0.25, y_offset)          # Left vertex
    v2 = (x_offset + 0.25, y_offset)          # Right vertex

    # Incoming e⁻
    draw_fermion_line(ax, e_in[0], e_in[1], v1[0], v1[1],
                     color=COLOR_ELECTRON, lw=2)
    # Incoming e⁺
    draw_fermion_line(ax, p_in[0], p_in[1], v1[0], v1[1],
                     color=COLOR_ELECTRON, lw=2)
    # γ/Z propagator
    draw_wavy_line(ax, v1[0], v1[1], v2[0], v2[1],
                  color=propagator_color, lw=2.5, n_waves=3)
    # Outgoing W⁻
    draw_wavy_line(ax, v2[0], v2[1], e_out[0], e_out[1],
                  color=COLOR_W_BOSON, lw=2)
    # Outgoing W⁺
    draw_wavy_line(ax, v2[0], v2[1], p_out[0], p_out[1],
                  color=COLOR_W_BOSON, lw=2)

    # Vertices
    draw_vertex(ax, v1[0], v1[1])
    draw_vertex(ax, v2[0], v2[1])

    # Labels
    ax.text(e_in[0] - 0.12, e_in[1], r'$e^-$', fontsize=13, ha='right', va='center')
    ax.text(p_in[0] - 0.12, p_in[1], r'$e^+$', fontsize=13, ha='right', va='center')
    ax.text(e_out[0] + 0.12, e_out[1], r'$W^-$', fontsize=13, ha='left', va='center',
           color=COLOR_W_BOSON)
    ax.text(p_out[0] + 0.12, p_out[1], r'$W^+$', fontsize=13, ha='left', va='center',
           color=COLOR_W_BOSON)
    ax.text((v1[0] + v2[0])/2, (v1[1] + v2[1])/2 + 0.18, propagator_label,
           fontsize=13, ha='center', va='bottom', color=COLOR_DARK)


def create_figure():
    """
    Create the E² cancellation figure with Feynman diagrams and bar chart.

    Layout:
    - Top row: Three Feynman diagrams (ν, γ, Z channels)
    - Bottom: Bar chart showing amplitude coefficients and cancellation
    """
    fig = plt.figure(figsize=(10, 7))

    # Create grid: 3 diagrams on top, bar chart below
    gs = fig.add_gridspec(2, 3, height_ratios=[1.2, 1],
                          hspace=0.35, wspace=0.25,
                          left=0.08, right=0.95, top=0.92, bottom=0.12)

    # ============ TOP ROW: FEYNMAN DIAGRAMS ============

    # t-channel (neutrino)
    ax1 = fig.add_subplot(gs[0, 0])
    ax1.set_xlim(-1.1, 1.1)
    ax1.set_ylim(-0.9, 0.9)
    ax1.set_aspect('equal')
    ax1.axis('off')
    draw_t_channel_diagram(ax1)
    ax1.set_title(r'(a) $t$-channel: $\nu_e$ exchange', fontsize=13, pad=8)
    ax1.text(0, -0.85, r'$a_\nu = +1$', fontsize=14, ha='center', va='top',
            color=COLOR_POSITIVE, fontweight='bold')

    # s-channel (photon)
    ax2 = fig.add_subplot(gs[0, 1])
    ax2.set_xlim(-1.1, 1.1)
    ax2.set_ylim(-0.9, 0.9)
    ax2.set_aspect('equal')
    ax2.axis('off')
    draw_s_channel_diagram(ax2, propagator_label=r'$\gamma$',
                          propagator_color=COLOR_PHOTON)
    ax2.set_title(r'(b) $s$-channel: $\gamma$ exchange', fontsize=13, pad=8)
    ax2.text(0, -0.85, r'$a_\gamma = -\sin^2\theta_W$', fontsize=14, ha='center', va='top',
            color=COLOR_NEGATIVE, fontweight='bold')

    # s-channel (Z)
    ax3 = fig.add_subplot(gs[0, 2])
    ax3.set_xlim(-1.1, 1.1)
    ax3.set_ylim(-0.9, 0.9)
    ax3.set_aspect('equal')
    ax3.axis('off')
    draw_s_channel_diagram(ax3, propagator_label=r'$Z^0$',
                          propagator_color=COLOR_Z_BOSON)
    ax3.set_title(r'(c) $s$-channel: $Z$ exchange', fontsize=13, pad=8)
    ax3.text(0, -0.85, r'$a_Z = -\cos^2\theta_W$', fontsize=14, ha='center', va='top',
            color=COLOR_NEGATIVE, fontweight='bold')

    # ============ BOTTOM: BAR CHART ============

    ax4 = fig.add_subplot(gs[1, :])

    # Values (using MS-bar sin²θ_W = 0.2312)
    sin2_theta = 0.2312
    cos2_theta = 1 - sin2_theta

    a_nu = 1.0
    a_gamma = -sin2_theta
    a_z = -cos2_theta
    a_total = a_nu + a_gamma + a_z

    # Bar positions and data
    labels = [r'$a_\nu$' + '\n(t-channel)',
              r'$a_\gamma$' + '\n(s-channel γ)',
              r'$a_Z$' + '\n(s-channel Z)',
              r'$\Sigma$' + '\n(Total)']
    values = [a_nu, a_gamma, a_z, a_total]
    colors = [COLOR_POSITIVE, COLOR_NEGATIVE, COLOR_NEGATIVE, COLOR_DARK]
    x_pos = [0, 1, 2, 3.5]  # Gap before total

    bars = ax4.bar(x_pos, values, width=0.6, color=colors, edgecolor='white', linewidth=2)

    # Add value labels on bars
    for x, val, bar in zip(x_pos, values, bars):
        va = 'bottom' if val >= 0 else 'top'
        offset = 0.03 if val >= 0 else -0.03
        ax4.text(x, val + offset, f'{val:+.4f}', ha='center', va=va,
                fontsize=13, fontweight='bold')

    # Highlight the cancellation
    ax4.axhline(0, color=COLOR_DARK, lw=1.5, ls='-', zorder=1)

    # Add equation annotation
    eq_box = ax4.text(3.5, -0.45,
                      r'$1 - (\sin^2\!\theta_W + \cos^2\!\theta_W) = 1 - 1 = 0$',
                      fontsize=13, ha='center', va='top',
                      bbox=dict(boxstyle='round,pad=0.4', facecolor='#F9E79F',
                               edgecolor='#F4D03F', linewidth=2))

    # Axis formatting
    ax4.set_xticks(x_pos)
    ax4.set_xticklabels(labels, fontsize=12)
    ax4.set_ylabel(r'$E^2$ coefficient', fontsize=14)
    ax4.set_ylim(-1.0, 1.2)
    ax4.set_xlim(-0.6, 4.3)
    ax4.spines['top'].set_visible(False)
    ax4.spines['right'].set_visible(False)
    ax4.set_title(r'(d) High-energy amplitude coefficients: exact cancellation',
                 fontsize=13, pad=10)

    # Add plus signs between diagrams
    fig.text(0.33, 0.72, r'$+$', fontsize=24, ha='center', va='center',
            fontweight='bold', color=COLOR_DARK)
    fig.text(0.64, 0.72, r'$+$', fontsize=24, ha='center', va='center',
            fontweight='bold', color=COLOR_DARK)

    # Overall title
    fig.suptitle(r'Gauge Cancellation in $e^+e^- \to W^+W^-$: Unitarity from Geometry',
                fontsize=15, fontweight='bold', y=0.98)

    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_ww_e2_cancellation.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {output_path}")

    plt.close('all')


if __name__ == '__main__':
    main()
