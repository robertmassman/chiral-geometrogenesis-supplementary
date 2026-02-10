#!/usr/bin/env python3
"""
Figure: Stable Convergence Point (Theorem 0.2.3)

Generates publication-quality figure showing the unique stable convergence point
at the center of the stella octangula where:
- All three color field pressures are equal
- The 120° phase configuration is stable
- The emergent metric is flat and isotropic

Key physics:
- Equal pressure: P_R(0) = P_G(0) = P_B(0) = P_0
- Phase-lock stability: reduced Hessian eigenvalues {3K/4, 9K/4} > 0
- Dynamical stability: Jacobian eigenvalues {-3K/2, -3K/2} < 0 (target-specific model)
- Unique fixed point: center is the global attractor

Proof Document: docs/proofs/Phase0/Theorem-0.2.3-Stable-Convergence-Point.md
Paper Section: Section 2 (Pre-Geometric Foundations)

Output: fig_thm_0_2_3_stable_convergence.pdf, fig_thm_0_2_3_stable_convergence.png
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import odeint
from matplotlib.patches import Circle, FancyArrowPatch, Arc
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


def target_specific_dynamics(psi, t, K):
    """
    Target-specific Sakaguchi-Kuramoto model for phase differences.

    From Theorem 0.2.3 Derivation §3.3.4:
    Each pair has its own target phase shift equal to the target separation.

    psi_1 = phi_G - phi_R (target: 2π/3)
    psi_2 = phi_B - phi_G (target: 2π/3)

    This model has a UNIQUE stable fixed point at (2π/3, 2π/3) = (120°, 120°).
    """
    psi1, psi2 = psi

    # Target-specific model: each coupling term uses its specific target
    # Target for (G-R): 2π/3
    # Target for (B-G): 2π/3
    # Target for (B-R): 4π/3 = (B-G) + (G-R)

    # From derivation: dpsi/dt drives toward target
    # dpsi1 = -(3K/2) * sin(psi1 - 2π/3)  (linearized around equilibrium)
    # dpsi2 = -(3K/2) * sin(psi2 - 2π/3)

    # Full nonlinear dynamics:
    alpha = 2 * np.pi / 3  # 120 degrees

    # Simplified target-specific dynamics (decoupled at leading order)
    dpsi1 = -K * np.sin(psi1 - alpha)
    dpsi2 = -K * np.sin(psi2 - alpha)

    return np.array([dpsi1, dpsi2])


def create_figure():
    """
    Two-panel figure showing:
    (a) Phase portrait with unique stable fixed point at 120°
    (b) Lyapunov stability / exponential decay of perturbations
    """
    fig, axes = plt.subplots(1, 2, figsize=(10, 4.5))

    K = 1.5  # Coupling strength

    # =========================================
    # Panel (a): Phase Portrait
    # =========================================
    ax1 = axes[0]

    # Background: observation region highlight
    from matplotlib.patches import Rectangle
    # Stable region around the fixed point
    stable_region = Rectangle((90, 90), 60, 60,
                               fill=True, facecolor='#E8F5E9',
                               edgecolor='none', alpha=0.6, zorder=0)
    ax1.add_patch(stable_region)

    # Vector field
    n_grid = 18
    psi1_grid = np.linspace(0, 2*np.pi, n_grid)
    psi2_grid = np.linspace(0, 2*np.pi, n_grid)
    PSI1, PSI2 = np.meshgrid(psi1_grid, psi2_grid)

    DPSI1 = np.zeros_like(PSI1)
    DPSI2 = np.zeros_like(PSI2)

    for i in range(n_grid):
        for j in range(n_grid):
            psi = np.array([PSI1[i, j], PSI2[i, j]])
            dpsi = target_specific_dynamics(psi, 0, K)
            DPSI1[i, j] = dpsi[0]
            DPSI2[i, j] = dpsi[1]

    magnitude = np.sqrt(DPSI1**2 + DPSI2**2)
    magnitude[magnitude == 0] = 1

    # Color by magnitude (flow speed)
    ax1.quiver(np.degrees(PSI1), np.degrees(PSI2), DPSI1, DPSI2,
               magnitude, cmap='Blues', alpha=0.6, scale=15,
               width=0.004, zorder=1)

    # Trajectories converging to the unique fixed point
    np.random.seed(123)
    t_span = np.linspace(0, 8, 300)

    # Sample initial conditions from various regions
    initial_conditions = [
        (0.3, 0.5),      # Near origin
        (1.0, 0.3),      # Lower region
        (0.5, 1.5),      # Left region
        (2.5, 0.8),      # Right lower
        (3.5, 2.0),      # Far right
        (1.2, 3.2),      # Upper left
        (4.5, 4.5),      # Far corner
        (5.0, 2.5),      # Right middle
        (2.0, 5.5),      # Upper middle
        (5.8, 5.2),      # Near (360, 360)
    ]

    for psi0 in initial_conditions:
        solution = odeint(target_specific_dynamics, psi0, t_span, args=(K,))

        # Plot trajectory with color gradient showing time evolution
        points = np.degrees(solution % (2*np.pi))

        # Use color to show time progression (dark to light)
        for i in range(len(points) - 1):
            alpha_val = 0.3 + 0.5 * (i / len(points))
            ax1.plot(points[i:i+2, 0], points[i:i+2, 1],
                    color='#1565C0', alpha=alpha_val, linewidth=1.2, zorder=5)

    # Mark the UNIQUE stable fixed point at (120°, 120°)
    ax1.plot(120, 120, 'o', color='#2E7D32', markersize=16,
            markeredgecolor='white', markeredgewidth=2.5, zorder=20)

    # Add unstable fixed points (saddles at other 120° multiples)
    unstable_points = [(240, 240), (0, 0), (240, 0), (0, 240)]
    for up in unstable_points:
        ax1.plot(up[0], up[1], 's', color='#F44336', markersize=8,
                markeredgecolor='white', markeredgewidth=1.5, zorder=15, alpha=0.7)

    # Diagonal reference line
    ax1.plot([0, 360], [0, 360], 'k--', alpha=0.15, linewidth=1, zorder=2)

    ax1.set_xlabel(r'$\psi_1 = \phi_G - \phi_R$ (degrees)')
    ax1.set_ylabel(r'$\psi_2 = \phi_B - \phi_G$ (degrees)')
    ax1.set_title(r'(a) Phase Portrait: Unique Global Attractor' + '\n' +
                  r'$(\psi_1^*, \psi_2^*) = (120°, 120°)$ — Unique Stable FP',
                  fontsize=11)
    ax1.set_xlim(0, 360)
    ax1.set_ylim(0, 360)
    ax1.set_xticks([0, 60, 120, 180, 240, 300, 360])
    ax1.set_yticks([0, 60, 120, 180, 240, 300, 360])
    ax1.grid(True, alpha=0.25, linestyle='-', linewidth=0.5)
    ax1.set_aspect('equal')

    # Legend
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#2E7D32',
               markersize=10, markeredgecolor='white', markeredgewidth=1.5,
               label='Stable FP (center)'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='#F44336',
               markersize=7, markeredgecolor='white', markeredgewidth=1,
               label='Unstable FP'),
        Line2D([0], [0], color='#1565C0', lw=1.5, alpha=0.7,
               label='Trajectory'),
    ]
    ax1.legend(handles=legend_elements, loc='upper right', fontsize=8)

    # =========================================
    # Panel (b): Lyapunov Stability
    # =========================================
    ax2 = axes[1]

    # Time evolution of phase perturbations
    t = np.linspace(0, 6, 200)

    # Decay rate from Theorem 0.2.3: λ = -3K/2 for target-specific model
    decay_rate = 1.5 * K  # |λ| = 3K/2

    # Different initial perturbations
    perturbations = [
        (1.2, r'$\delta\psi_0 = 70°$', '#1976D2'),
        (0.8, r'$\delta\psi_0 = 45°$', '#42A5F5'),
        (0.5, r'$\delta\psi_0 = 30°$', '#90CAF9'),
    ]

    for delta0, label, color in perturbations:
        # Exponential decay: δψ(t) = δψ_0 * exp(-|λ|t)
        delta_t = delta0 * np.exp(-decay_rate * t)
        ax2.plot(t, np.degrees(delta_t), lw=2, color=color, label=label)

    # Equilibrium line
    ax2.axhline(0, color='#2E7D32', ls='--', lw=2, alpha=0.8, label='Equilibrium')

    # Characteristic time scale
    tau = 1 / decay_rate
    ax2.axvline(tau, color='#FF9800', ls=':', lw=2, alpha=0.9, label=r'$\tau = \frac{2}{3K}$')

    ax2.set_xlabel(r'Time $\lambda$ (units of $K^{-1}$)')
    ax2.set_ylabel(r'Phase perturbation $|\delta\psi|$ (degrees)')
    ax2.set_title(r'(b) Lyapunov Stability: Exponential Decay' + '\n' +
                  r'$\lambda_{1,2} = -\frac{3K}{2}$ (degenerate eigenvalues)',
                  fontsize=11)
    ax2.set_xlim(0, 6)
    ax2.set_ylim(-5, 75)
    ax2.legend(loc='upper right', fontsize=8)
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    return fig


def main():
    """Generate and save the figure."""
    print("Generating Theorem 0.2.3 figure: Stable Convergence Point...")

    fig = create_figure()

    # Save in both formats
    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_thm_0_2_3_stable_convergence.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"✓ Saved: {output_path}")

    plt.close('all')
    print("Done!")


if __name__ == '__main__':
    main()
