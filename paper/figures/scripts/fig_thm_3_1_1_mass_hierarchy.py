#!/usr/bin/env python3
"""
Figure 3: Mass Hierarchy Pattern

Generates publication-quality figure showing the fermion mass hierarchy
and its relationship to the Wolfenstein parameter λ.

Pattern: m_n ∝ λ^{2n} where λ ≈ 0.22

Source Theorems:
- Theorem 3.1.1: Phase-gradient mass generation mass formula
- Theorem 3.1.2: Mass hierarchy from geometry

Output: fig_thm_3_1_1_mass_hierarchy.pdf, fig_thm_3_1_1_mass_hierarchy.png
"""

import numpy as np
import matplotlib.pyplot as plt
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'serif',
    'font.serif': ['Times New Roman', 'DejaVu Serif'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# ============================================================================
# PHYSICAL CONSTANTS AND PARAMETERS
# ============================================================================

# Golden ratio
PHI = (1 + np.sqrt(5)) / 2  # 1.618034...

# Wolfenstein parameter from geometry
LAMBDA_GEOMETRIC = (1 / PHI**3) * np.sin(np.radians(72))  # 0.2245
LAMBDA_PDG = 0.22497  # PDG 2024

# Fermion masses (GeV) - PDG 2024
MASSES = {
    'top': 172.69,
    'bottom': 4.18,
    'charm': 1.27,
    'strange': 0.093,
    'up': 0.00216,
    'down': 0.00467,
    'tau': 1.777,
    'muon': 0.1057,
    'electron': 0.000511,
}


def create_figure_3():
    """
    Show mass hierarchy pattern m_f vs generation index.

    Pattern: m_n ∝ λ^{2n} where λ ≈ 0.22

    Two panels:
    - Panel (a): Clean log-mass plot with dashed prediction lines
    - Panel (b): Normalized mass ratios m/m₃ showing λ^(2n) pattern clearly
    """
    fig, axes = plt.subplots(1, 2, figsize=(7, 3.5))

    # Panel (a): Log plot of masses with clean prediction lines
    ax1 = axes[0]

    generations = np.array([1, 2, 3])

    # Observed masses
    up_masses = np.array([MASSES['up'], MASSES['charm'], MASSES['top']])
    down_masses = np.array([MASSES['down'], MASSES['strange'], MASSES['bottom']])
    lepton_masses = np.array([MASSES['electron'], MASSES['muon'], MASSES['tau']])

    # Plot observed data with markers
    ax1.semilogy(generations, up_masses, 'o-', color='#e74c3c', lw=2, markersize=8,
                 markeredgecolor='black', markeredgewidth=0.5, label='Up-type (u, c, t)')
    ax1.semilogy(generations, down_masses, 's-', color='#3498db', lw=2, markersize=8,
                 markeredgecolor='black', markeredgewidth=0.5, label='Down-type (d, s, b)')
    ax1.semilogy(generations, lepton_masses, '^-', color='#2ecc71', lw=2, markersize=8,
                 markeredgecolor='black', markeredgewidth=0.5, label='Leptons (e, μ, τ)')

    # Theoretical prediction lines: m_n = m_3 * λ^{2(3-n)}
    gen_fine = np.linspace(1, 3, 50)
    lambda_val = LAMBDA_PDG

    for base_mass, color in [
        (MASSES['top'], '#e74c3c'),
        (MASSES['bottom'], '#3498db'),
        (MASSES['tau'], '#2ecc71')
    ]:
        pred_masses = base_mass * lambda_val**(2*(3-gen_fine))
        ax1.semilogy(gen_fine, pred_masses, '--', color=color, alpha=0.6, lw=1.5)

    ax1.set_xlabel('Generation')
    ax1.set_ylabel('Mass (GeV)')
    ax1.set_xticks([1, 2, 3])
    ax1.set_xticklabels(['1st', '2nd', '3rd'])
    ax1.set_title('(a) Fermion Mass Hierarchy')
    ax1.legend(loc='lower right', fontsize=8)
    ax1.grid(True, alpha=0.3, which='both')
    ax1.set_ylim(1e-4, 1e3)
    ax1.set_xlim(0.8, 3.2)

    # Add λ^(2n) annotation
    ax1.text(1.5, 5e2, r'Dashed: $m_n \propto \lambda^{2(3-n)}$', fontsize=8,
             style='italic', color='gray')

    # Panel (b): Normalized masses m/m₃ showing λ^(2n) pattern
    ax2 = axes[1]

    # Normalize to 3rd generation
    up_norm = up_masses / MASSES['top']
    down_norm = down_masses / MASSES['bottom']
    lepton_norm = lepton_masses / MASSES['tau']

    # Plot observed normalized masses
    ax2.semilogy(generations, up_norm, 'o-', color='#e74c3c', lw=2, markersize=8,
                 markeredgecolor='black', markeredgewidth=0.5, label='Up-type')
    ax2.semilogy(generations, down_norm, 's-', color='#3498db', lw=2, markersize=8,
                 markeredgecolor='black', markeredgewidth=0.5, label='Down-type')
    ax2.semilogy(generations, lepton_norm, '^-', color='#2ecc71', lw=2, markersize=8,
                 markeredgecolor='black', markeredgewidth=0.5, label='Leptons')

    # Theoretical prediction: λ^{2(3-n)} pattern
    pred_norm = lambda_val**(2*(3-gen_fine))
    ax2.semilogy(gen_fine, pred_norm, 'k--', lw=2, alpha=0.8,
                 label=f'$\\lambda^{{2(3-n)}}$, $\\lambda={lambda_val:.3f}$')

    ax2.set_xlabel('Generation')
    ax2.set_ylabel('$m / m_3$')
    ax2.set_xticks([1, 2, 3])
    ax2.set_xticklabels(['1st', '2nd', '3rd'])
    ax2.set_title('(b) Normalized Mass Pattern')
    ax2.legend(loc='lower right', fontsize=8)
    ax2.grid(True, alpha=0.3, which='both')
    ax2.set_ylim(1e-5, 2)
    ax2.set_xlim(0.8, 3.2)

    plt.tight_layout()

    for ext in ['pdf', 'png']:
        plt.savefig(f'{OUTPUT_DIR}/fig_thm_3_1_1_mass_hierarchy.{ext}')
    plt.close()
    print(f"✓ Figure 3 saved to {OUTPUT_DIR}/fig_thm_3_1_1_mass_hierarchy.pdf")
    print(f"✓ Figure 3 saved to {OUTPUT_DIR}/fig_thm_3_1_1_mass_hierarchy.png")


if __name__ == '__main__':
    create_figure_3()
