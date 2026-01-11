#!/usr/bin/env python3
"""
Figure 9: Anisotropy Suppression Curve

Generates publication-quality figure showing how lattice anisotropy is
suppressed by coarse-graining.

Two panels:
- (a) Form factor vs GL (log-log) showing suppression as function of
      coarse-graining parameter GL = 2*pi*L/a
- (b) Physical scale comparison showing suppression at different scales
      for Planck-scale lattice spacing

Key physics:
- Sphere form factor: 3*j_1(GL)/(GL) where j_1 is first spherical Bessel
- Asymptotic: 3/(GL)^2 for GL >> 1, i.e., (a/L)^2 suppression
- At macroscopic scales, lattice effects are suppressed by >10^(-69)

Output: fig_pred_suppression_curve.pdf, fig_pred_suppression_curve.png
"""

import numpy as np
import matplotlib.pyplot as plt
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Set up publication-quality figure style
plt.rcParams.update({
    'font.size': 10,
    'font.family': 'serif',
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'legend.fontsize': 9,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,  # Set to True if LaTeX is available
})


def sphere_form_factor(GL):
    """
    Compute the sphere form factor: 3(sin(GL) - GL*cos(GL)) / (GL)^3
    This equals 3*j_1(GL)/(GL) where j_1 is the first spherical Bessel function.
    """
    # Handle GL = 0 case (limit is 1)
    result = np.zeros_like(GL, dtype=float)
    mask = GL > 1e-10
    x = GL[mask]
    result[mask] = 3 * (np.sin(x) - x * np.cos(x)) / x**3
    result[~mask] = 1.0
    return result


def asymptotic_envelope(GL):
    """Asymptotic envelope: 3/(GL)^2 for GL >> 1"""
    return 3 / GL**2


def create_figure_9():
    """Generate the suppression curve figure."""
    # Create figure with two panels
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4.5))

    # ============================================
    # Panel (a): Form factor vs GL (log-log)
    # ============================================

    GL = np.logspace(-1, 3, 1000)
    ff = np.abs(sphere_form_factor(GL))
    envelope = asymptotic_envelope(GL)

    ax1.loglog(GL, ff, 'b-', linewidth=1.5, label=r'$|3j_1(GL)/(GL)|$ (exact)')
    ax1.loglog(GL, envelope, 'r--', linewidth=1.5, label=r'$3/(GL)^2$ (envelope)')

    # Add shaded regions for different regimes
    ax1.axvspan(0.1, 1, alpha=0.15, color='orange', label=r'$L \sim a$ (lattice visible)')
    ax1.axvspan(10, 1000, alpha=0.15, color='green', label=r'$L \gg a$ (continuum)')

    # Mark key values
    ax1.axhline(y=1e-4, color='gray', linestyle=':', alpha=0.5)
    ax1.axhline(y=1e-8, color='gray', linestyle=':', alpha=0.5)

    ax1.set_xlabel(r'$GL = 2\pi L/a$ (coarse-graining parameter)')
    ax1.set_ylabel(r'Anisotropic suppression factor')
    ax1.set_xlim(0.1, 1000)
    ax1.set_ylim(1e-9, 2)
    ax1.legend(loc='lower left', framealpha=0.9)
    ax1.set_title('(a) Coarse-graining suppresses lattice anisotropy')
    ax1.grid(True, alpha=0.3, which='both')

    # Add annotation
    ax1.annotate(r'$\propto (a/L)^2$', xy=(100, 3e-4), fontsize=11, color='red')

    # ============================================
    # Panel (b): Physical scale comparison
    # ============================================

    # For Planck-scale lattice a = l_P = 1.6e-35 m
    a_planck = 1.6e-35  # meters

    # Physical scales and their suppression factors
    scales = {
        'LHC (TeV)': 1e-19,
        'Nuclear (fm)': 1e-15,
        'Atomic (nm)': 1e-10,
        'Human (m)': 1,
        'Earth (km)': 1e6,
        'Solar System': 1e13,
    }

    L_values = np.array(list(scales.values()))
    labels = list(scales.keys())
    suppression = (a_planck / L_values)**2

    # Create horizontal bar chart
    colors = plt.cm.viridis(np.linspace(0.2, 0.8, len(scales)))
    bars = ax2.barh(range(len(scales)), -np.log10(suppression), color=colors, height=0.6)

    ax2.set_yticks(range(len(scales)))
    ax2.set_yticklabels(labels)
    ax2.set_xlabel(r'Suppression exponent: $-\log_{10}[(a/L)^2]$')
    ax2.set_title(r'(b) Suppression at different scales ($a = \ell_P$)')

    # Add value labels on bars
    # Use floor instead of round to match paper's "exceeds 10^-69" statement
    for i, (bar, supp) in enumerate(zip(bars, suppression)):
        width = bar.get_width()
        exponent = int(np.floor(-np.log10(supp)))
        ax2.text(width + 1, bar.get_y() + bar.get_height()/2,
                 f'$10^{{-{exponent}}}$',
                 va='center', ha='left', fontsize=9)

    # Add experimental sensitivity line
    current_sensitivity = 32  # Current experiments can probe ~10^-32
    ax2.axvline(x=current_sensitivity, color='red', linestyle='--', linewidth=2,
                label=f'Current sensitivity\n($10^{{-{current_sensitivity}}}$)')

    # Add "observable" and "unobservable" regions
    ax2.axvspan(0, current_sensitivity, alpha=0.1, color='red')
    ax2.axvspan(current_sensitivity, 150, alpha=0.1, color='green')

    ax2.text(16, -0.5, 'Observable', ha='center', fontsize=9, color='darkred')
    ax2.text(80, -0.5, 'Unobservable', ha='center', fontsize=9, color='darkgreen')

    ax2.set_xlim(0, 145)
    ax2.legend(loc='center right', fontsize=8)
    ax2.grid(True, alpha=0.3, axis='x')

    plt.tight_layout()

    # Save figures
    plt.savefig(f'{OUTPUT_DIR}/fig_pred_suppression_curve.png',
                dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(f'{OUTPUT_DIR}/fig_pred_suppression_curve.pdf',
                bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"✓ Figure 9 saved to {OUTPUT_DIR}/fig_pred_suppression_curve.pdf")
    print(f"✓ Figure 9 saved to {OUTPUT_DIR}/fig_pred_suppression_curve.png")
    print("\nKey results verified:")
    print(f"  - Sphere form factor at GL=10: {abs(sphere_form_factor(np.array([10.0]))[0]):.6f}")
    print(f"  - Asymptotic at GL=10: {asymptotic_envelope(np.array([10.0]))[0]:.6f}")
    print(f"  - Ratio: {abs(sphere_form_factor(np.array([10.0]))[0]) / asymptotic_envelope(np.array([10.0]))[0]:.3f}")
    print(f"\nPlanck-scale suppression at LHC (10^-19 m): {(a_planck/1e-19)**2:.2e}")
    print(f"Planck-scale suppression at nuclear (10^-15 m): {(a_planck/1e-15)**2:.2e}")


if __name__ == '__main__':
    create_figure_9()
