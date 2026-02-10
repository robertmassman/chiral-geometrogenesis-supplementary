#!/usr/bin/env python3
"""
Figure: Anthropic Window for R_stella (Proposition 0.0.36)

Visualizes the range of R_stella values compatible with observer existence,
showing the three independent nuclear physics constraints (deuteron binding,
di-proton stability, Hoyle state resonance) and the positions of the observed
value and bootstrap predictions.

Key physics:
- Upper bound (R < 0.48 fm): Deuteron unbinds if ΛQCD decreases by ~6%
- Lower bound (R > 0.42 fm): Di-proton binds / Hoyle state shifts at ~4%
- Observed R_stella = 0.44847 fm sits at 48% of window (centered)
- Corrected bootstrap (0.454 fm) inside window; uncorrected (0.41 fm) outside

Proof Document: docs/proofs/foundations/Proposition-0.0.36-Anthropic-Bounds-On-R-Stella.md
Paper Section: Section 9.9.1 (String Tension from Casimir Energy)

Output: fig_anthropic_window.pdf, fig_anthropic_window.png
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch
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
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# ============================================================================
# Physical values from Proposition 0.0.36
# ============================================================================
R_OBS = 0.44847       # Observed R_stella (fm)
R_BOOT_CORR = 0.454   # Corrected bootstrap prediction (fm)
R_BOOT_RAW = 0.41     # Uncorrected 1-loop bootstrap (fm)

# Conservative combined window
R_MIN_CONS = 0.42     # Lower bound (di-proton + Hoyle)
R_MAX_CONS = 0.48     # Upper bound (deuteron + Hoyle)

# Tighter Hoyle-only window
R_MIN_HOYLE = 0.43    # Hoyle lower
R_MAX_HOYLE = 0.47    # Hoyle upper

# Corresponding sqrt(sigma) values (MeV) = hbar*c / R
HBARC = 197.327  # MeV·fm
SQRT_SIGMA_OBS = HBARC / R_OBS
SQRT_SIGMA_MIN = HBARC / R_MAX_CONS   # Note: larger R → smaller sqrt(sigma)
SQRT_SIGMA_MAX = HBARC / R_MIN_CONS

# Window position of observed value
WINDOW_POS = (R_OBS - R_MIN_CONS) / (R_MAX_CONS - R_MIN_CONS)

# ============================================================================
# Color palette (no purple per CLAUDE.md)
# ============================================================================
COLOR_WINDOW_LIGHT = '#D6EAF8'    # Light blue - conservative window
COLOR_WINDOW_DARK = '#85C1E9'     # Medium blue - Hoyle window
COLOR_OBS = '#1A5276'             # Dark blue - observed value
COLOR_BOOT_CORR = '#117A65'       # Teal - corrected bootstrap
COLOR_BOOT_RAW = '#7F8C8D'        # Gray - uncorrected bootstrap
COLOR_DEUTERON = '#C0392B'        # Red - deuteron constraint
COLOR_DIPROTON = '#E67E22'        # Orange - di-proton constraint
COLOR_HOYLE = '#27AE60'           # Green - Hoyle state constraint
COLOR_AXIS = '#2C3E50'            # Dark - axis elements


def create_figure():
    """Create the anthropic window figure."""
    fig, ax = plt.subplots(1, 1, figsize=(7, 5.0))

    # Axis range
    r_lo, r_hi = 0.395, 0.505
    y_lo, y_hi = -0.6, 2.4

    # ====================================================================
    # Shaded windows (no label= here; legend uses proxy artists below)
    # ====================================================================
    ax.axvspan(R_MIN_CONS, R_MAX_CONS, alpha=0.25, color=COLOR_WINDOW_LIGHT,
               zorder=0)
    ax.axvspan(R_MIN_HOYLE, R_MAX_HOYLE, alpha=0.30, color=COLOR_WINDOW_DARK,
               zorder=1)

    # ====================================================================
    # Constraint boundaries (vertical lines only — labels go in legend)
    # ====================================================================
    ax.axvline(R_MAX_CONS, color=COLOR_DEUTERON, linestyle='--', linewidth=1.5,
               alpha=0.8, zorder=2)
    ax.axvline(R_MIN_CONS, color=COLOR_DIPROTON, linestyle='--', linewidth=1.5,
               alpha=0.8, zorder=2)
    ax.axvline(R_MIN_HOYLE, color=COLOR_HOYLE, linestyle=':', linewidth=1.2,
               alpha=0.7, zorder=2)
    ax.axvline(R_MAX_HOYLE, color=COLOR_HOYLE, linestyle=':', linewidth=1.2,
               alpha=0.7, zorder=2)

    # Hoyle bracket (visual only)
    bracket_y = 1.85
    ax.plot([R_MIN_HOYLE, R_MIN_HOYLE], [bracket_y - 0.12, bracket_y + 0.12],
            color=COLOR_HOYLE, linewidth=1.5, zorder=3)
    ax.plot([R_MAX_HOYLE, R_MAX_HOYLE], [bracket_y - 0.12, bracket_y + 0.12],
            color=COLOR_HOYLE, linewidth=1.5, zorder=3)
    ax.plot([R_MIN_HOYLE, R_MAX_HOYLE], [bracket_y, bracket_y],
            color=COLOR_HOYLE, linewidth=1.5, zorder=3)

    # ====================================================================
    # Key values (vertical lines + markers only — labels go in legend)
    # ====================================================================
    # Observed R_stella
    ax.axvline(R_OBS, color=COLOR_OBS, linewidth=2.5, zorder=5, alpha=0.9)
    ax.plot(R_OBS, 0, 'o', color=COLOR_OBS, markersize=10, zorder=6,
            markeredgecolor='white', markeredgewidth=1.5)

    # Corrected bootstrap
    ax.axvline(R_BOOT_CORR, color=COLOR_BOOT_CORR, linewidth=1.8,
               linestyle='--', zorder=4, alpha=0.85)
    ax.plot(R_BOOT_CORR, 0, 's', color=COLOR_BOOT_CORR, markersize=8,
            zorder=6, markeredgecolor='white', markeredgewidth=1)

    # Uncorrected bootstrap
    ax.axvline(R_BOOT_RAW, color=COLOR_BOOT_RAW, linewidth=1.5,
               linestyle=':', zorder=4, alpha=0.7)
    ax.plot(R_BOOT_RAW, 0, 'D', color=COLOR_BOOT_RAW, markersize=7,
            zorder=6, markeredgecolor='white', markeredgewidth=1)

    # ====================================================================
    # Window width annotation (below axis)
    # ====================================================================
    annot_y = -0.35
    ax.annotate('', xy=(R_MIN_CONS, annot_y), xytext=(R_MAX_CONS, annot_y),
                arrowprops=dict(arrowstyle='<->', color=COLOR_AXIS, lw=1.5))
    ax.text((R_MIN_CONS + R_MAX_CONS) / 2, annot_y - 0.08,
            '$\\Delta R / R \\approx \\pm 7\\%$',
            fontsize=10, ha='center', va='top', color=COLOR_AXIS,
            fontweight='bold', zorder=10,
            bbox=dict(facecolor='white', edgecolor='none', alpha=0.9, pad=3))

    # ====================================================================
    # Legend with proxy artists
    # ====================================================================
    from matplotlib.lines import Line2D
    from matplotlib.patches import Patch

    legend_handles = [
        Line2D([0], [0], color=COLOR_OBS, linewidth=2.5, marker='o',
               markersize=7, markeredgecolor='white', markeredgewidth=1,
               label='Observed  $R_{\\mathrm{stella}} = 0.449$ fm'),
        Line2D([0], [0], color=COLOR_BOOT_CORR, linewidth=1.8,
               linestyle='--', marker='s', markersize=6,
               markeredgecolor='white', markeredgewidth=1,
               label='Bootstrap (corrected)  $0.454$ fm'),
        Line2D([0], [0], color=COLOR_BOOT_RAW, linewidth=1.5,
               linestyle=':', marker='D', markersize=5,
               markeredgecolor='white', markeredgewidth=1,
               label='Bootstrap (1-loop)  $0.41$ fm'),
        Line2D([0], [0], color=COLOR_DEUTERON, linewidth=1.5,
               linestyle='--', label='Deuteron unbinds ($R > 0.48$ fm)'),
        Line2D([0], [0], color=COLOR_DIPROTON, linewidth=1.5,
               linestyle='--', label='Di-proton binds ($R < 0.42$ fm)'),
        Patch(facecolor=COLOR_WINDOW_DARK, alpha=0.35,
              label='$^{12}$C Hoyle state ($\\pm 4\\%$)'),
        Patch(facecolor=COLOR_WINDOW_LIGHT, alpha=0.30,
              label='Combined window ($\\pm 7\\%$)'),
    ]

    ax.legend(handles=legend_handles, loc='upper center',
              bbox_to_anchor=(0.5, -0.22), fontsize=8, ncol=2,
              framealpha=0.92, edgecolor='gray', fancybox=True,
              borderpad=0.6, labelspacing=0.4, columnspacing=1.5)

    # ====================================================================
    # Secondary axis: sqrt(sigma) in MeV (top)
    # ====================================================================
    ax2 = ax.twiny()
    sigma_ticks_fm = np.array([0.40, 0.42, 0.44, 0.46, 0.48, 0.50])
    sigma_ticks_mev = HBARC / sigma_ticks_fm
    ax2.set_xlim(r_lo, r_hi)
    ax2.set_xticks(sigma_ticks_fm)
    ax2.set_xticklabels([f'{v:.0f}' for v in sigma_ticks_mev], fontsize=9)
    ax2.set_xlabel('$\\sqrt{\\sigma}$ (MeV)', fontsize=11, labelpad=8)

    # ====================================================================
    # Formatting
    # ====================================================================
    ax.set_xlim(r_lo, r_hi)
    ax.set_ylim(y_lo, y_hi)
    ax.set_xlabel('$R_{\\mathrm{stella}}$ (fm)', fontsize=12)
    ax.set_yticks([])
    ax.spines['left'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['top'].set_visible(False)

    # Horizontal baseline
    ax.axhline(0, color=COLOR_AXIS, linewidth=0.8, zorder=1)

    ax.set_title('Anthropic Window for $R_{\\mathrm{stella}}$ (Prop. 0.0.36)',
                 fontsize=12, fontweight='bold', pad=30)

    fig.subplots_adjust(bottom=0.38)
    return fig


def main():
    fig = create_figure()
    fig.savefig(os.path.join(OUTPUT_DIR, 'fig_anthropic_window.png'),
                dpi=300, bbox_inches='tight', facecolor='white')
    fig.savefig(os.path.join(OUTPUT_DIR, 'fig_anthropic_window.pdf'),
                bbox_inches='tight', facecolor='white')
    plt.close('all')

    print("Figure saved successfully!")
    print(f"Key values:")
    print(f"  Observed R_stella = {R_OBS} fm (sqrt(sigma) = {SQRT_SIGMA_OBS:.0f} MeV)")
    print(f"  Conservative window: {R_MIN_CONS}--{R_MAX_CONS} fm")
    print(f"  Hoyle window: {R_MIN_HOYLE}--{R_MAX_HOYLE} fm")
    print(f"  Window position: {WINDOW_POS*100:.1f}%")
    print(f"  Corrected bootstrap: {R_BOOT_CORR} fm")
    print(f"  Uncorrected bootstrap: {R_BOOT_RAW} fm")


if __name__ == '__main__':
    main()
