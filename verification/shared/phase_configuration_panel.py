#!/usr/bin/env python3
"""
Standalone visualization of Panel 2: Phase Configuration at O
From the Theorem 0.2.3 verification plots.

Shows the 120° phase separation of R, G, B fields and time emergence.
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patheffects as pe
from pathlib import Path


def create_phase_configuration_plot(output_path: str = None):
    """
    Create the Phase Configuration at O polar plot.

    Shows:
    - Three phase vectors at 0°, 120°, 240° (R, G, B)
    - Sum equals zero at center (destructive interference)
    - Time emergence from phase evolution
    """
    fig, ax = plt.subplots(figsize=(8, 8), subplot_kw={'projection': 'polar'})

    # The three phase angles (120° separation)
    phases = [0, 2*np.pi/3, 4*np.pi/3]
    colors = ['red', 'green', 'blue']
    labels = ['φ_R = 0°', 'φ_G = 120°', 'φ_B = 240°']

    # Draw phase vectors as arrows from origin
    for phi, c, lbl in zip(phases, colors, labels):
        ax.annotate('', xy=(phi, 1), xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=c, lw=3))
        ax.scatter(phi, 1, color=c, s=200, zorder=5, edgecolors='black', linewidths=2)
        ax.text(phi, 1.25, lbl, fontsize=10, ha='center', fontweight='bold', color=c)

    # Show the sum equals zero (center point)
    ax.scatter(0, 0, color='gold', s=300, marker='*', zorder=10, edgecolors='black', linewidths=2)
    ax.text(0.3, 0.3, 'Σχ = 0', fontsize=12, fontweight='bold', color='gold',
            path_effects=[pe.withStroke(linewidth=2, foreground='black')])

    # Internal time emerges from phase evolution (at r=1.0, same as phase vectors)
    theta_arrow = np.linspace(0, 2*np.pi, 100)
    r_arrow = np.ones_like(theta_arrow) * 1.0
    ax.plot(theta_arrow, r_arrow, 'purple', alpha=0.5, linewidth=2, linestyle='--')
    ax.annotate('', xy=(np.pi/4, 1.0), xytext=(0, 1.0),
                arrowprops=dict(arrowstyle='->', color='purple', lw=2))
    ax.text(np.pi/4, 0.75, 't = ∫dλ/ω', fontsize=10, color='purple', fontweight='bold')

    ax.set_title('Phase Configuration at O\n120° separation → Time emergence', fontsize=14)
    ax.set_ylim([0, 1.5])

    plt.tight_layout()

    if output_path:
        plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved to: {output_path}")

    plt.show()
    plt.close()


if __name__ == "__main__":
    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)
    output_path = output_dir / "phase_configuration_panel2.png"
    create_phase_configuration_plot(str(output_path))
