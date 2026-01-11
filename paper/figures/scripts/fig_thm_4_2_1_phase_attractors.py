#!/usr/bin/env python3
"""
Figure 6: Phase Space Attractors (Time's Arrow)

Generates publication-quality figure showing the two-attractor structure
in phase space demonstrating time-reversal symmetry breaking.

From Theorem 2.2.1: Sakaguchi-Kuramoto model with alpha = 2*pi/3 produces
two stable attractors corresponding to fundamental and anti-fundamental
SU(3) representations.

Key features:
- Phase portrait on T^2 torus
- Vector field showing flow direction
- Two stable fixed points at (120, 120) and (240, 240) degrees
- Entropy increase showing irreversibility

Output: fig_thm_4_2_1_phase_attractors.pdf, fig_thm_4_2_1_phase_attractors.png
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import odeint
from matplotlib.patches import Polygon
from matplotlib.lines import Line2D
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


def phase_difference_dynamics(psi, t, K):
    """
    Phase-difference dynamics from SYMMETRIC Sakaguchi-Kuramoto model.

    psi_1 = phi_G - phi_R,  psi_2 = phi_B - phi_G

    From symmetric model (all pairs use same alpha = 2*pi/3):
    d(phi_i)/dt = omega + (K/2) * sum_{j!=i} sin(phi_j - phi_i - alpha)

    This produces two stable attractors at (120 deg, 120 deg) and (240 deg, 240 deg).
    """
    psi1, psi2 = psi
    alpha = 2 * np.pi / 3  # 120 degrees

    # From the symmetric model derivation
    # dpsi1 = dphi_G - dphi_R
    dpsi1 = (K/2) * (
        np.sin(-psi1 - alpha) + np.sin(psi2 - alpha)  # from dphi_G
        - np.sin(psi1 - alpha) - np.sin(psi1 + psi2 - alpha)  # minus dphi_R
    )

    # dpsi2 = dphi_B - dphi_G
    dpsi2 = (K/2) * (
        np.sin(-psi1 - psi2 - alpha) + np.sin(-psi2 - alpha)  # from dphi_B
        - np.sin(-psi1 - alpha) - np.sin(psi2 - alpha)  # minus dphi_G
    )

    return np.array([dpsi1, dpsi2])


def create_figure_6():
    """
    Show two-attractor structure in phase space demonstrating T-breaking.

    From Theorem 2.2.1: Sakaguchi-Kuramoto with alpha = 2*pi/3
    Rich visualization with SU(3) weight structure overlay.
    """
    fig, axes = plt.subplots(1, 2, figsize=(8, 4))

    K = 1.0

    # Panel (a): Phase portrait with SU(3) structure
    ax1 = axes[0]

    # ===========================================
    # BACKGROUND: Basin coloring
    # ===========================================
    # Highlight the basins of attraction
    fund_region = Polygon([(0, 0), (180, 0), (180, 180), (0, 180)],
                          fill=True, facecolor='blue', alpha=0.08,
                          edgecolor='none', zorder=0)
    ax1.add_patch(fund_region)

    anti_region = Polygon([(180, 180), (360, 180), (360, 360), (180, 360)],
                          fill=True, facecolor='red', alpha=0.08,
                          edgecolor='none', zorder=0)
    ax1.add_patch(anti_region)

    # ===========================================
    # VECTOR FIELD
    # ===========================================
    n_grid = 20
    psi1_grid = np.linspace(0, 2*np.pi, n_grid)
    psi2_grid = np.linspace(0, 2*np.pi, n_grid)
    PSI1, PSI2 = np.meshgrid(psi1_grid, psi2_grid)

    DPSI1 = np.zeros_like(PSI1)
    DPSI2 = np.zeros_like(PSI2)

    for i in range(n_grid):
        for j in range(n_grid):
            psi = np.array([PSI1[i, j], PSI2[i, j]])
            dpsi = phase_difference_dynamics(psi, 0, K)
            DPSI1[i, j] = dpsi[0]
            DPSI2[i, j] = dpsi[1]

    magnitude = np.sqrt(DPSI1**2 + DPSI2**2)
    magnitude[magnitude == 0] = 1
    DPSI1_norm = DPSI1 / magnitude
    DPSI2_norm = DPSI2 / magnitude

    ax1.quiver(np.degrees(PSI1), np.degrees(PSI2), DPSI1_norm, DPSI2_norm,
               magnitude, cmap='viridis', alpha=0.5, scale=25, zorder=1)

    # ===========================================
    # TRAJECTORIES with color-coded attractors
    # ===========================================
    np.random.seed(42)
    t_span = np.linspace(0, 40, 400)

    for _ in range(20):
        psi0 = np.random.uniform(0, 2*np.pi, 2)
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))

        # Determine which attractor
        final = solution[-1] % (2*np.pi)
        dist1 = np.linalg.norm(final - np.array([2*np.pi/3, 2*np.pi/3]))
        dist2 = np.linalg.norm(final - np.array([4*np.pi/3, 4*np.pi/3]))
        color = 'blue' if dist1 < dist2 else 'red'

        ax1.plot(np.degrees(solution[:, 0] % (2*np.pi)),
                np.degrees(solution[:, 1] % (2*np.pi)),
                color=color, alpha=0.5, linewidth=1.0, zorder=5)

    # ===========================================
    # FIXED POINTS with SU(3) labels
    # ===========================================
    # Stable FP1: Fundamental
    ax1.plot(120, 120, 'o', color='#1976D2', markersize=14,
            markeredgecolor='black', markeredgewidth=2, zorder=20)
    ax1.annotate(r'FP$_1$: R→G→B' + '\n(Fund.)', (125, 95), fontsize=8,
                fontweight='bold', color='#1976D2',
                bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.9),
                zorder=25)

    # Stable FP2: Anti-fundamental
    ax1.plot(240, 240, 'o', color='#D32F2F', markersize=14,
            markeredgecolor='black', markeredgewidth=2, zorder=20)
    ax1.annotate(r'FP$_2$: R→B→G' + '\n(Anti-fund.)', (245, 215), fontsize=8,
                fontweight='bold', color='#D32F2F',
                bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.9),
                zorder=25)

    # Unstable FP: synchronized
    ax1.plot(0, 0, 's', color='gray', markersize=8,
            markeredgecolor='black', markeredgewidth=1.5, zorder=20)

    # Saddle points
    saddles = [(120, 240), (240, 120)]
    for s in saddles:
        ax1.plot(s[0], s[1], 'd', color='orange', markersize=8,
                markeredgecolor='black', markeredgewidth=1.5, zorder=15, alpha=0.8)

    # Diagonal line showing symmetric configurations
    ax1.plot([0, 360], [0, 360], 'k--', alpha=0.2, linewidth=1.5, zorder=2)

    ax1.set_xlabel(r'$\psi_1 = \phi_G - \phi_R$ (degrees)')
    ax1.set_ylabel(r'$\psi_2 = \phi_B - \phi_G$ (degrees)')
    ax1.set_title(r'(a) Phase Portrait on $\mathbb{T}^2$')
    ax1.set_xlim(0, 360)
    ax1.set_ylim(0, 360)
    ax1.set_xticks([0, 60, 120, 180, 240, 300, 360])
    ax1.set_yticks([0, 60, 120, 180, 240, 300, 360])
    ax1.grid(True, alpha=0.3)
    ax1.set_aspect('equal')

    # Compact legend
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#1976D2',
               markersize=8, markeredgecolor='black', label='Stable FP (Fund.)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#D32F2F',
               markersize=8, markeredgecolor='black', label='Stable FP (Anti-fund.)'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='gray',
               markersize=6, markeredgecolor='black', label='Unstable FP'),
        Line2D([0], [0], marker='d', color='w', markerfacecolor='orange',
               markersize=6, markeredgecolor='black', label='Saddle point'),
    ]
    ax1.legend(handles=legend_elements, loc='upper right', fontsize=6)

    # Panel (b): Lyapunov function / entropy
    ax2 = axes[1]

    t = np.linspace(0, 10, 200)

    # Trajectories from different initial conditions
    for psi0 in [2.5, 2.0, 1.5, 1.0]:
        # Approximate decay to attractor
        psi_t = psi0 * np.exp(-0.5 * t)  # Simplified exponential decay
        entropy = 1 - np.exp(-0.5 * t)  # Entropy increases
        ax2.plot(t, entropy, lw=1.5, alpha=0.7)

    ax2.axhline(1.0, color='green', ls='--', lw=2, alpha=0.7, label='Equilibrium')

    ax2.set_xlabel(r'Time $\lambda$')
    ax2.set_ylabel(r'Entropy $S/S_{eq}$')
    ax2.set_title('(b) Entropy Increase')
    ax2.legend(loc='lower right')
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 1.1)
    ax2.grid(True, alpha=0.3)

    # Add dS/dt > 0 annotation
    # From Theorem 2.2.3 Sec 5.4.5: sigma = 3K/4 (phase-space contraction rate)
    # Therefore dS/dt = k_B * sigma = 3*k_B*K/4
    ax2.text(2, 0.3, r'$\frac{dS}{dt} = \frac{3k_B K}{4} > 0$', fontsize=11,
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    plt.tight_layout()

    for ext in ['pdf', 'png']:
        plt.savefig(f'{OUTPUT_DIR}/fig_thm_4_2_1_phase_attractors.{ext}')
    plt.close()
    print(f"✓ Figure 6 saved to {OUTPUT_DIR}/fig_thm_4_2_1_phase_attractors.pdf")
    print(f"✓ Figure 6 saved to {OUTPUT_DIR}/fig_thm_4_2_1_phase_attractors.png")


if __name__ == '__main__':
    create_figure_6()
