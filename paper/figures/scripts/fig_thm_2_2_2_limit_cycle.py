#!/usr/bin/env python3
"""
Figure: Phase Space Limit Cycle (Theorem 2.2.2)

Visualizes the globally stable limit cycle in the coupled three-phase
color field system. The R→G→B phases maintain 120° separation while
rotating collectively at frequency ω.

Key physics:
- Three color phases lock at 120° separation (Theorem 2.2.1)
- Collective rotation forms a limit cycle in lab frame
- Co-rotating frame shows fixed point structure

Panel (a): 3D trajectory in T³ showing convergence to limit cycle
Panel (b): Phase portrait on T² showing flow to stable fixed points

Proof Document: docs/proofs/Phase2/Theorem-2.2.2-Limit-Cycle.md
Paper Section: Phase Dynamics

Output: fig_thm_2_2_2_limit_cycle.pdf, fig_thm_2_2_2_limit_cycle.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from matplotlib.lines import Line2D
from mpl_toolkits.mplot3d import Axes3D
from scipy.integrate import odeint
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

# Color palette for R, G, B phases
COLOR_R = '#E74C3C'  # Red
COLOR_G = '#27AE60'  # Green
COLOR_B = '#3498DB'  # Blue
COLOR_CYCLE = '#9B59B6'  # Purple for limit cycle
COLOR_ATTRACTOR = '#1976D2'  # Blue for FP1 attractor marker


def phase_difference_dynamics(psi, t, K, omega=1.0):
    """
    Symmetric Sakaguchi-Kuramoto model in phase-difference coordinates.

    Coordinates: psi_1 = phi_G - phi_R, psi_2 = phi_B - phi_G
    (Following Theorem 2.2.1's coordinate convention)

    From the symmetric model where all pairs use alpha = 2π/3:
      d(phi_i)/dt = omega + (K/2) * sum_{j!=i} sin(phi_j - phi_i - alpha)

    Fixed points:
      - Stable: (120°, 120°) and (240°, 240°)
      - Unstable: (0°, 0°)
      - Saddle: (240°, 120°)
    """
    psi1, psi2 = psi
    alpha = 2 * np.pi / 3  # 120 degrees

    # From the symmetric Sakaguchi-Kuramoto model:
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


def full_phase_dynamics(phi, t, K, omega=1.0):
    """
    Full 3-phase dynamics in lab frame.

    d(phi_i)/dt = omega + (K/2) * sum_j sin(phi_j - phi_i - target_ij)
    """
    phi_R, phi_G, phi_B = phi
    alpha = 2 * np.pi / 3

    dphi_R = omega + (K/2) * (
        np.sin(phi_G - phi_R - alpha) +
        np.sin(phi_B - phi_R - 2*alpha)
    )
    dphi_G = omega + (K/2) * (
        np.sin(phi_R - phi_G + alpha) +
        np.sin(phi_B - phi_G - alpha)
    )
    dphi_B = omega + (K/2) * (
        np.sin(phi_R - phi_B + 2*alpha) +
        np.sin(phi_G - phi_B + alpha)
    )

    return np.array([dphi_R, dphi_G, dphi_B])


def create_figure():
    """
    Create two-panel figure showing the limit cycle structure.

    (a) 3D limit cycle in phase space
    (b) Phase portrait on T² showing convergence
    """
    fig = plt.figure(figsize=(12, 5.5))

    # Use GridSpec for better control over panel sizes
    from matplotlib.gridspec import GridSpec
    gs = GridSpec(1, 2, figure=fig, width_ratios=[1.0, 1.0], wspace=0.25)

    K = 1.0
    omega = 1.0

    # =========================================
    # Panel (a): 3D Limit Cycle Trajectory
    # =========================================
    ax1 = fig.add_subplot(gs[0], projection='3d')

    # Initial condition off equilibrium
    phi0 = np.array([0, np.pi/3, np.pi/2])  # Not at 120° separation

    # Integrate to show convergence then cycling
    t_span = np.linspace(0, 20, 2000)
    solution = odeint(full_phase_dynamics, phi0, t_span, args=(K, omega))

    # Normalize phases to [0, 2π]
    phi_R = solution[:, 0] % (2*np.pi)
    phi_G = solution[:, 1] % (2*np.pi)
    phi_B = solution[:, 2] % (2*np.pi)

    # Plot trajectory in 3D phase space
    ax1.plot(phi_R, phi_G, phi_B, color=COLOR_CYCLE, alpha=0.7, linewidth=1.5,
             label='Trajectory')

    # Mark starting point
    ax1.scatter([phi0[0]], [phi0[1]], [phi0[2]],
                color='black', s=80, marker='o', zorder=10, label='Start')

    # Show the limit cycle (ideal 120° separation rotating)
    t_cycle = np.linspace(0, 2*np.pi, 100)
    phi_R_lc = t_cycle % (2*np.pi)
    phi_G_lc = (t_cycle + 2*np.pi/3) % (2*np.pi)
    phi_B_lc = (t_cycle + 4*np.pi/3) % (2*np.pi)

    ax1.plot(phi_R_lc, phi_G_lc, phi_B_lc, color=COLOR_ATTRACTOR,
             linewidth=3, alpha=0.9, label='Limit Cycle', linestyle='--')

    # Add diagonal line (synchronized state - unstable)
    diag = np.linspace(0, 2*np.pi, 50)
    ax1.plot(diag, diag, diag, 'k--', alpha=0.3, linewidth=1, label='Sync (unstable)')

    ax1.set_xlabel(r'$\phi_R$', fontsize=11)
    ax1.set_ylabel(r'$\phi_G$', fontsize=11)
    ax1.set_zlabel(r'$\phi_B$', fontsize=11)
    ax1.set_title(r'(a) Limit Cycle in $\mathbb{T}^3$', fontsize=12, fontweight='bold')

    # Set ticks
    ax1.set_xticks([0, np.pi, 2*np.pi])
    ax1.set_xticklabels(['0', r'$\pi$', r'$2\pi$'])
    ax1.set_yticks([0, np.pi, 2*np.pi])
    ax1.set_yticklabels(['0', r'$\pi$', r'$2\pi$'])
    ax1.set_zticks([0, np.pi, 2*np.pi])
    ax1.set_zticklabels(['0', r'$\pi$', r'$2\pi$'])

    ax1.legend(loc='upper left', fontsize=8)

    # =========================================
    # Panel (b): Phase Portrait on T²
    # =========================================
    ax2 = fig.add_subplot(gs[1])

    # Vector field in phase-difference coordinates
    n_grid = 18
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

    # Streamplot for smooth flow visualization (grayscale gradient)
    # Note: streamplot expects U[i,j] at position (X[j], Y[i]), which matches our meshgrid indexing
    ax2.streamplot(np.degrees(psi1_grid), np.degrees(psi2_grid),
                   DPSI1, DPSI2, color=magnitude, cmap='Greys',
                   density=1.2, linewidth=0.8, arrowsize=0.8)

    # Sample trajectories converging to attractors
    t_traj = np.linspace(0, 40, 800)

    # Define starting points spread across phase space
    # Mix of points that go to FP1 (120,120) and FP2 (240,240)
    starting_points = [
        # Going to FP1 (120°, 120°)
        (50, 50),    # Near unstable -> FP1
        (30, 150),   # Upper left -> FP1
        (150, 30),   # Lower right -> FP1
        (80, 200),   # Mid-upper -> FP1
        (180, 60),   # Lower middle -> FP1
        (280, 60),   # Lower right quadrant -> FP1
        # Going to FP2 (240°, 240°)
        (310, 310),  # Near unstable (wrapped) -> FP2
        (200, 320),  # Upper middle -> FP2
        (320, 200),  # Right middle -> FP2
        (60, 280),   # Upper left quadrant -> FP2
        (280, 280),  # Upper right -> FP2
        (350, 250),  # Far right -> FP2
        (250, 350),  # Far top -> FP2
        (300, 340),  # Upper right corner -> FP2
        (340, 300),  # Right upper -> FP2
        (180, 300),  # Upper center -> FP2
        (220, 280),  # Near FP2 -> FP2
        (350, 350),  # Corner -> FP2
    ]

    # Colors based on which attractor they go to
    COLOR_FP1 = COLOR_ATTRACTOR  # Blue for FP1
    COLOR_FP2 = '#D32F2F'        # Red for FP2

    for idx, (psi1_deg, psi2_deg) in enumerate(starting_points):
        psi0 = np.array([np.radians(psi1_deg), np.radians(psi2_deg)])
        sol = odeint(phase_difference_dynamics, psi0, t_traj, args=(K,))

        # Determine which attractor this trajectory goes to
        final_psi1 = np.degrees(sol[-1, 0] % (2*np.pi))
        final_psi2 = np.degrees(sol[-1, 1] % (2*np.pi))
        dist_to_fp1 = np.sqrt((final_psi1 - 120)**2 + (final_psi2 - 120)**2)
        dist_to_fp2 = np.sqrt((final_psi1 - 240)**2 + (final_psi2 - 240)**2)
        traj_color = COLOR_FP1 if dist_to_fp1 < dist_to_fp2 else COLOR_FP2

        # Plot trajectory
        ax2.plot(np.degrees(sol[:, 0] % (2*np.pi)),
                np.degrees(sol[:, 1] % (2*np.pi)),
                color=traj_color, alpha=0.7, linewidth=2.0, zorder=6)

        # Starting point (larger, with black edge)
        ax2.scatter(psi1_deg, psi2_deg,
                   color=traj_color, s=100, marker='o',
                   edgecolors='black', linewidths=1.5, zorder=15)

    # Mark fixed points (in coordinates ψ₁ = φ_G - φ_R, ψ₂ = φ_B - φ_G)
    # FP1: Stable (R→G→B) at ψ1=120°, ψ2=120°
    ax2.plot(120, 120, 'o', color=COLOR_ATTRACTOR, markersize=14,
             markeredgecolor='black', markeredgewidth=2, zorder=20)

    # FP2: Stable (R→B→G) at ψ1=240°, ψ2=240°
    ax2.plot(240, 240, 'o', color='#D32F2F', markersize=14,
             markeredgecolor='black', markeredgewidth=2, zorder=20)

    # FP3: Unstable (all aligned) at (0°, 0°)
    ax2.plot(0, 0, 's', color='gray', markersize=10,
             markeredgecolor='black', markeredgewidth=1.5, zorder=20)
    ax2.annotate('Unstable', (10, 25), fontsize=8, color='gray')

    # Saddle point at (240°, 120°)
    ax2.plot(240, 120, 'd', color='orange', markersize=10,
             markeredgecolor='black', markeredgewidth=1.5, zorder=15)
    ax2.annotate('Saddle', (250, 130), fontsize=8, color='orange')

    ax2.set_xlabel(r'$\psi_1 = \phi_G - \phi_R$ (degrees)', fontsize=11)
    ax2.set_ylabel(r'$\psi_2 = \phi_B - \phi_G$ (degrees)', fontsize=11)
    ax2.set_title(r'(b) Phase Portrait on $\mathbb{T}^2$', fontsize=12, fontweight='bold')
    ax2.set_xlim(0, 360)
    ax2.set_ylim(0, 360)
    ax2.set_xticks([0, 60, 120, 180, 240, 300, 360])
    ax2.set_yticks([0, 60, 120, 180, 240, 300, 360])
    ax2.set_aspect('equal')
    ax2.grid(True, alpha=0.3)

    # Legend - positioned above the plot
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_ATTRACTOR,
               markersize=10, markeredgecolor='black', label=r'FP$_1$: Stable (R→G→B)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#D32F2F',
               markersize=10, markeredgecolor='black', label=r'FP$_2$: Stable (R→B→G)'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='gray',
               markersize=8, markeredgecolor='black', label='Unstable'),
        Line2D([0], [0], marker='d', color='w', markerfacecolor='orange',
               markersize=8, markeredgecolor='black', label='Saddle'),
    ]
    ax2.legend(handles=legend_elements, loc='upper center', bbox_to_anchor=(0.5, -0.12),
               ncol=2, fontsize=8, frameon=True, fancybox=True)

    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    # Save in both formats
    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_thm_2_2_2_limit_cycle.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {output_path}")

    plt.close('all')
    print("\nFigure generation complete!")


if __name__ == '__main__':
    main()
