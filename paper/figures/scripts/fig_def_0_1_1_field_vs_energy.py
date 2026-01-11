#!/usr/bin/env python3
"""
Figure: Field vs Energy (Coherent vs Incoherent)

Shows |χ_total|² (coherent) vs ρ (incoherent energy density).

Key insight: The coherent field vanishes at center due to destructive
interference of the three 120°-separated phases, but the incoherent
energy density (sum of individual intensities) remains non-zero.

Source: Extracted from papers/paper-2-dynamics/figures/paper_2_publication_plots.py
Originally derived from verification/Phase0/theorem_0_2_3_stable_convergence_point.py
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Output directory (parent of scripts folder = figures folder)
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

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
})


def create_fig_def_0_1_1_field_vs_energy():
    """
    Show |χ_total|² (coherent) vs ρ (incoherent energy density).

    Key insight: The coherent field vanishes at center due to destructive
    interference of the three 120°-separated phases, but the incoherent
    energy density (sum of individual intensities) remains non-zero.
    """
    # Stella octangula color vertices (normalized to unit sphere)
    X_R = np.array([1, 1, 1]) / np.sqrt(3)
    X_G = np.array([1, -1, -1]) / np.sqrt(3)
    X_B = np.array([-1, 1, -1]) / np.sqrt(3)

    EPSILON = 0.50  # Regularization parameter
    A0 = 1.0  # Field amplitude

    def pressure_function(x, x_c, epsilon=EPSILON):
        """P_c(x) = 1 / (|x - x_c|² + ε²)"""
        r_squared = np.sum((x - x_c) ** 2)
        return 1.0 / (r_squared + epsilon ** 2)

    def total_field_magnitude_squared(x, a0=A0, epsilon=EPSILON):
        """
        |χ_total|² = (a0²/2) * [(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]
        Coherent sum with interference.
        """
        P_R = pressure_function(x, X_R, epsilon)
        P_G = pressure_function(x, X_G, epsilon)
        P_B = pressure_function(x, X_B, epsilon)
        return (a0 ** 2 / 2) * ((P_R - P_G) ** 2 + (P_G - P_B) ** 2 + (P_B - P_R) ** 2)

    def energy_density(x, a0=A0, epsilon=EPSILON):
        """
        ρ(x) = a0² * Σ_c P_c(x)²
        Incoherent sum (no interference).
        """
        P_R = pressure_function(x, X_R, epsilon)
        P_G = pressure_function(x, X_G, epsilon)
        P_B = pressure_function(x, X_B, epsilon)
        return a0 ** 2 * (P_R ** 2 + P_G ** 2 + P_B ** 2)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8, 4))

    # Higher resolution for smooth gradients
    n_points = 300
    x_range = np.linspace(-1, 1, n_points)
    X, Y = np.meshgrid(x_range, x_range)

    chi_squared_grid = np.zeros_like(X)
    rho_grid = np.zeros_like(X)

    for i in range(len(x_range)):
        for j in range(len(x_range)):
            point = np.array([X[i, j], Y[i, j], 0])
            chi_squared_grid[i, j] = total_field_magnitude_squared(point)
            rho_grid[i, j] = energy_density(point)

    # Panel 1: |χ|² - vanishes at center
    im1 = ax1.imshow(chi_squared_grid, extent=[-1, 1, -1, 1], origin='lower',
                     cmap='viridis', aspect='equal', interpolation='bilinear')
    ax1.set_xlabel('$x$', fontsize=11)
    ax1.set_ylabel('$y$', fontsize=11)
    ax1.set_title('$|\\chi_{total}|^2$ (Coherent)\nVanishes at center', fontsize=11)
    cbar1 = plt.colorbar(im1, ax=ax1, shrink=0.8)
    ax1.plot(0, 0, 'w*', markersize=14, markeredgecolor='black', markeredgewidth=0.5)
    ax1.text(0.95, 0.95, 'Center', transform=ax1.transAxes, fontsize=9,
             ha='right', va='top', color='white',
             bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.5))

    # Panel 2: ρ - non-zero at center
    im2 = ax2.imshow(rho_grid, extent=[-1, 1, -1, 1], origin='lower',
                     cmap='plasma', aspect='equal', interpolation='bilinear')
    ax2.set_xlabel('$x$', fontsize=11)
    ax2.set_ylabel('$y$', fontsize=11)
    ax2.set_title('$\\rho$ (Incoherent Energy)\nNon-zero at center', fontsize=11)
    cbar2 = plt.colorbar(im2, ax=ax2, shrink=0.8)
    ax2.plot(0, 0, 'w*', markersize=14, markeredgecolor='black', markeredgewidth=0.5)
    ax2.text(0.95, 0.95, 'Center', transform=ax2.transAxes, fontsize=9,
             ha='right', va='top', color='white',
             bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.5))

    plt.tight_layout()

    for ext in ['pdf', 'png']:
        plt.savefig(output_dir / f'fig_def_0_1_1_field_vs_energy.{ext}', dpi=300)
    plt.close()
    print(f"Figure: Field vs Energy - saved to {output_dir}")


if __name__ == '__main__':
    create_fig_def_0_1_1_field_vs_energy()
