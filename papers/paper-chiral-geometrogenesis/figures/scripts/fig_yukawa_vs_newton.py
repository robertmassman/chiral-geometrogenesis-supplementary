#!/usr/bin/env python3
"""
Figure: Yukawa vs Newtonian Gravitational Potential

Shows why the graviton must be massless: a massive mediator gives an
exponentially-decaying Yukawa potential, while observations require
the long-range 1/r Newtonian potential.

References:
- Proposition 5.2.4b (Spin-2 From Stress-Energy Conservation)
- LIGO graviton mass bound: m_g < 1.76 × 10^{-23} eV
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Style configuration
plt.rcParams.update({
    'font.size': 10,
    'axes.titlesize': 12,
    'axes.labelsize': 10,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'legend.fontsize': 9,
    'figure.titlesize': 14,
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# Output directory
OUTPUT_DIR = Path(__file__).parent.parent
OUTPUT_DIR.mkdir(exist_ok=True)


def create_yukawa_vs_newton_figure():
    """
    Create 2-panel figure comparing Yukawa and Newtonian potentials.

    Left panel: Linear scale showing potential shapes
    Right panel: Log scale showing exponential suppression at large r
    """
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Left panel: Potential comparison (linear scale)
    ax1 = axes[0]

    r = np.linspace(0.1, 10, 500)  # Distance in Compton wavelengths

    # Newtonian potential: Phi = -1/r (normalized)
    phi_newton = -1 / r

    # Yukawa potentials with different masses
    mass_params = [0.5, 1.0, 2.0]  # m * lambda_compton values
    colors = ['#e74c3c', '#f39c12', '#9b59b6']

    ax1.plot(r, phi_newton, 'b-', linewidth=2.5,
             label='Newton: $-1/r$ (massless)', zorder=10)

    for m, color in zip(mass_params, colors):
        phi_yukawa = -np.exp(-m * r) / r
        ax1.plot(r, phi_yukawa, '--', color=color, linewidth=2,
                 label=f'Yukawa: $m\\lambda = {m}$')

    ax1.set_xlabel('$r / \\lambda$ (distance in Compton wavelengths)')
    ax1.set_ylabel('$\\Phi(r) / \\Phi_0$ (normalized potential)')
    ax1.set_title('Gravitational Potential: Massive vs Massless Mediator')
    ax1.set_xlim(0, 10)
    ax1.set_ylim(-2, 0.1)
    ax1.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
    ax1.legend(loc='lower right')
    ax1.grid(True, alpha=0.3)

    # Add annotation
    ax1.annotate('Massive mediator:\nexponential suppression\nat large $r$',
                 xy=(6, -0.55), fontsize=9, ha='center',
                 bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    # Right panel: Log scale to show exponential decay
    ax2 = axes[1]

    r_log = np.linspace(0.5, 20, 500)
    phi_newton_log = 1 / r_log  # |Phi|

    ax2.semilogy(r_log, phi_newton_log, 'b-', linewidth=2.5,
                 label='Newton: $|\\Phi| \\propto 1/r$')

    for m, color in zip(mass_params, colors):
        phi_yukawa_log = np.exp(-m * r_log) / r_log
        ax2.semilogy(r_log, phi_yukawa_log, '--', color=color, linewidth=2,
                     label=f'Yukawa: $m\\lambda = {m}$')

    ax2.set_xlabel('$r / \\lambda$ (distance in Compton wavelengths)')
    ax2.set_ylabel('$|\\Phi(r)| / \\Phi_0$ (log scale)')
    ax2.set_title('Exponential Suppression of Yukawa Potential')
    ax2.set_xlim(0, 20)
    ax2.set_ylim(1e-10, 10)
    ax2.legend(loc='lower left', bbox_to_anchor=(0, 0))
    ax2.grid(True, alpha=0.3, which='both')

    # Add observational constraint annotation
    ax2.annotate('LIGO bound:\n$m_g < 1.76 \\times 10^{-23}$ eV\n$\\lambda > 10^{16}$ m',
                 xy=(14, 1e-3), fontsize=9, ha='center',
                 bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.7))

    plt.tight_layout()

    # Save PNG and PDF
    png_path = OUTPUT_DIR / "fig_yukawa_vs_newton.png"
    pdf_path = OUTPUT_DIR / "fig_yukawa_vs_newton.pdf"

    plt.savefig(png_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(pdf_path, bbox_inches='tight', facecolor='white')

    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")
    plt.close()


if __name__ == "__main__":
    print("=" * 60)
    print("Generating Yukawa vs Newton Figure")
    print("Proposition 5.2.4b: Massless Graviton Requirement")
    print("=" * 60)

    create_yukawa_vs_newton_figure()

    print("\nDone!")
