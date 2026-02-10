#!/usr/bin/env python3
"""
Figure: Electroweak Scale from Central Charge Flow

Physically accurate visualization of how a small central charge change
Δa_eff = 1/120 generates the large hierarchy v_H/√σ = 560.

Physics basis (from Proposition 0.0.21):
- Komargodski-Schwimmer a-theorem: a_UV > a_IR along RG flow
- Effective Δa_eff = c(physical Higgs) = 1/120
- Hierarchy formula: v_H/√σ = exp(1/4 + 1/(2π²Δa))
- Small Δa in denominator → large exponent → exponential hierarchy

The key mechanism: exp(1/Δa) amplifies tiny central charge changes into
large scale separations. This is why Δa = 1/120 produces a factor of 560.

Proof Document: docs/proofs/foundations/Proposition-0.0.21-Unified-Electroweak-Scale-Derivation.md
Paper Section: §subsec:ew-scale Electroweak Scale from Central Charge Flow

Output: fig_ew_scale_central_charge.pdf, fig_ew_scale_central_charge.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
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
COLOR_MAIN = '#2C3E50'
COLOR_PHYSICAL = '#E74C3C'
COLOR_GAUGE = '#9B59B6'
COLOR_TOTAL = '#27AE60'


def create_figure():
    """
    Show the physical mechanism: how small Δa generates large hierarchy.

    Left panel: The amplification function exp(1/(2π²Δa)) vs Δa
    Right panel: The two contributions building the total exponent
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # === LEFT PANEL: The amplification mechanism ===

    # Physical values
    delta_a_physical = 1/120  # = 0.00833
    gauge_term = 1/4  # = 0.250
    rg_contribution = 1/(2 * np.pi**2 * delta_a_physical)  # = 6.079
    total_exponent = gauge_term + rg_contribution  # = 6.329
    hierarchy = np.exp(total_exponent)  # = 560.5

    # Plot exp(1/(2π²Δa)) as function of Δa
    delta_a = np.linspace(0.005, 0.1, 500)
    rg_term = 1 / (2 * np.pi**2 * delta_a)
    amplification = np.exp(rg_term)

    ax1.semilogy(delta_a, amplification, color=COLOR_MAIN, lw=2.5,
                 label=r'$\exp\left(\frac{1}{2\pi^2 \Delta a}\right)$: Smaller $\Delta a$ $\rightarrow$ larger hierarchy')

    # Mark the physical point Δa = 1/120
    amp_at_physical = np.exp(1/(2 * np.pi**2 * delta_a_physical))
    ax1.plot(delta_a_physical, amp_at_physical, 'o', color=COLOR_PHYSICAL,
             markersize=12, markeredgecolor='white', markeredgewidth=2, zorder=5,
             label=rf'$\Delta a_{{\rm eff}} = \frac{{1}}{{120}} \rightarrow {amp_at_physical:.0f}\times$')

    # Dashed lines to axes
    ax1.axhline(amp_at_physical, color=COLOR_PHYSICAL, ls='--', lw=1.5, alpha=0.7)
    ax1.axvline(delta_a_physical, color=COLOR_PHYSICAL, ls='--', lw=1.5, alpha=0.7)

    ax1.set_xlabel(r'Effective central charge change $\Delta a_{\rm eff}$', fontsize=12)
    ax1.set_ylabel(r'RG amplification factor', fontsize=12)
    ax1.set_xlim(0.005, 0.1)
    ax1.set_ylim(1, 1e4)
    ax1.grid(True, alpha=0.3, which='both')
    ax1.set_title('RG amplification from central charge flow', fontsize=12,
                  fontweight='bold', color=COLOR_MAIN, pad=10)
    ax1.legend(loc='upper right', fontsize=10)

    # === RIGHT PANEL: The two contributions ===

    # Bar chart showing gauge + RG = total
    contributions = [gauge_term, rg_contribution, total_exponent]
    labels = [r'$\frac{1}{\dim(\mathrm{adj}_{EW})} = \frac{1}{4}$',
              r'$\frac{1}{2\pi^2 \Delta a} = \frac{120}{2\pi^2}$',
              r'Total exponent']
    colors = [COLOR_GAUGE, COLOR_MAIN, COLOR_TOTAL]

    x_pos = [0, 1, 2.2]
    bars = ax2.bar(x_pos, contributions, width=0.6, color=colors,
                   edgecolor='white', linewidth=2, alpha=0.85)

    # Value labels on bars
    for i, (x, val) in enumerate(zip(x_pos, contributions)):
        ax2.text(x, val + 0.15, f'{val:.3f}', ha='center', va='bottom',
                fontsize=11, fontweight='bold', color=colors[i])

    # Plus and equals signs
    ax2.text(0.5, 3.5, '+', fontsize=20, ha='center', va='center',
             fontweight='bold', color=COLOR_MAIN)
    ax2.text(1.6, 3.5, '=', fontsize=20, ha='center', va='center',
             fontweight='bold', color=COLOR_MAIN)

    # Title showing the final result
    ax2.set_title(rf'Hierarchy factor: $e^{{{total_exponent:.3f}}} = {hierarchy:.0f} = v_H/\sqrt{{\sigma}}$',
                  fontsize=12, fontweight='bold', color=COLOR_MAIN, pad=10)

    # Physical interpretation labels below
    ax2.text(0, -0.8, 'Gauge\nstructure', ha='center', va='top', fontsize=10, color=COLOR_GAUGE)
    ax2.text(1, -0.8, 'Central charge\nflow', ha='center', va='top', fontsize=10, color=COLOR_MAIN)
    ax2.text(2.2, -0.8, rf'$v_H/\sqrt{{\sigma}}$', ha='center', va='top', fontsize=11,
             fontweight='bold', color=COLOR_TOTAL)

    ax2.set_xticks(x_pos)
    ax2.set_xticklabels(['', '', ''])
    ax2.set_ylabel('Exponent contribution', fontsize=12)
    ax2.set_xlim(-0.5, 3.0)
    ax2.set_ylim(-0.3, 7.5)
    ax2.grid(True, alpha=0.3, axis='y')

    # Panel labels
    ax1.text(-0.12, 1.02, '(a)', transform=ax1.transAxes,
             fontsize=14, fontweight='bold', va='bottom')
    ax2.text(-0.12, 1.02, '(b)', transform=ax2.transAxes,
             fontsize=14, fontweight='bold', va='bottom')

    plt.tight_layout()
    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_ew_scale_central_charge.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {output_path}")

    plt.close('all')


if __name__ == '__main__':
    main()
