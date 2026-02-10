#!/usr/bin/env python3
"""
Unified Geometry Diagram with Energy Density Overlay
=====================================================

A single plot showing:
- Background: Energy density ρ = Σ|χ_c|² (showing energy persists everywhere)
- Foreground: Phase trajectories converging to color-neutral origin
- Weight diagram structure overlaid

The physical interpretation:
- The vertices (R, G, B) are where color fields are localized (energy peaks)
- The center has MINIMUM but NON-ZERO energy
- Trajectories show phase dynamics converging to this energy minimum
- Time (λ) is driven by this persistent energy

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patheffects as path_effects
from matplotlib.patches import Polygon, Circle
from matplotlib.colors import LinearSegmentedColormap
from scipy.integrate import odeint
from pathlib import Path

# ============================================================================
# CONSTANTS
# ============================================================================

ALPHA = 2 * np.pi / 3  # 120°

# ============================================================================
# DYNAMICAL SYSTEM
# ============================================================================

def phase_difference_dynamics(psi: np.ndarray, t: float, K: float) -> np.ndarray:
    """Phase-difference dynamics from Sakaguchi-Kuramoto model."""
    psi1, psi2 = psi
    alpha = ALPHA

    dpsi1 = (K/2) * (
        np.sin(-psi1 - alpha) + np.sin(psi2 - alpha)
        - np.sin(psi1 - alpha) - np.sin(psi1 + psi2 - alpha)
    )

    dpsi2 = (K/2) * (
        np.sin(-psi1 - psi2 - alpha) + np.sin(-psi2 - alpha)
        - np.sin(-psi1 - alpha) - np.sin(psi2 - alpha)
    )

    return np.array([dpsi1, dpsi2])


def compute_incoherent_energy(x, y, vertices, sigma=0.35):
    """
    Compute ρ = Σ|χ_c|² - the INCOHERENT sum (energy density).
    Each color field is a Gaussian localized at its vertex.
    """
    rho = 0
    for v in vertices:
        r2 = (x - v[0])**2 + (y - v[1])**2
        amplitude = np.exp(-r2 / (2 * sigma**2))
        rho += amplitude**2
    return rho


# ============================================================================
# MAIN PLOT
# ============================================================================

def create_unified_diagram_with_energy():
    """
    Create unified diagram with energy density as background.
    """
    fig, ax = plt.subplots(figsize=(12, 11))

    scale = 0.6

    # Vertex positions (cube roots of unity scaled)
    theta_R, theta_G, theta_B = 0, 2*np.pi/3, 4*np.pi/3
    w_R = scale * np.array([np.cos(theta_R), np.sin(theta_R)])
    w_G = scale * np.array([np.cos(theta_G), np.sin(theta_G)])
    w_B = scale * np.array([np.cos(theta_B), np.sin(theta_B)])
    vertices = [w_R, w_G, w_B]

    # Anti-fundamental
    w_Rbar, w_Gbar, w_Bbar = -w_R, -w_G, -w_B

    # ===========================================
    # BACKGROUND: Energy density field
    # ===========================================

    x_grid = np.linspace(-1.0, 1.0, 200)
    y_grid = np.linspace(-1.0, 1.0, 200)
    X, Y = np.meshgrid(x_grid, y_grid)

    rho_energy = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy[i, j] = compute_incoherent_energy(X[i, j], Y[i, j], vertices, sigma=0.32)

    # Custom colormap: dark purple (low) to yellow (high), with some transparency feel
    # Use a modified magma that's slightly lighter
    im = ax.contourf(X, Y, rho_energy, levels=50, cmap='inferno', alpha=0.6, zorder=0)

    # Add subtle contour lines
    ax.contour(X, Y, rho_energy, levels=10, colors='white', alpha=0.15, linewidths=0.5, zorder=1)

    # Colorbar
    cbar = plt.colorbar(im, ax=ax, fraction=0.046, pad=0.02, shrink=0.8)
    cbar.set_label('Energy Density  $\\rho = |\\chi_R|^2 + |\\chi_G|^2 + |\\chi_B|^2$',
                   fontsize=12, labelpad=10)

    # ===========================================
    # WEIGHT DIAGRAM TRIANGLES
    # ===========================================

    # Fundamental triangle
    fund_tri = Polygon([w_R, w_G, w_B], fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)

    # Anti-fundamental triangle
    anti_tri = Polygon([w_Rbar, w_Gbar, w_Bbar], fill=False,
                       edgecolor='lightcoral', linewidth=3, linestyle='--', zorder=10)
    ax.add_patch(anti_tri)

    # ===========================================
    # PHASE TRAJECTORIES
    # ===========================================

    K = 1.0
    t_span = np.linspace(0, 50, 500)
    np.random.seed(123)
    n_traj = 20

    for i in range(n_traj):
        phi0_R = 0
        phi0_G = np.random.uniform(0, 2*np.pi)
        phi0_B = np.random.uniform(0, 2*np.pi)
        psi0 = np.array([phi0_G - phi0_R, phi0_B - phi0_G])

        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))

        trajectory_x, trajectory_y = [], []
        for psi in solution:
            psi1, psi2 = psi
            phi_R, phi_G, phi_B = 0, psi1, psi1 + psi2

            z_R = np.exp(1j * phi_R)
            z_G = np.exp(1j * phi_G)
            z_B = np.exp(1j * phi_B)
            color_sum = (z_R + z_G + z_B) / 3

            trajectory_x.append(scale * np.real(color_sum) * 3)
            trajectory_y.append(scale * np.imag(color_sum) * 3)

        trajectory_x = np.array(trajectory_x)
        trajectory_y = np.array(trajectory_y)

        # Determine attractor color
        final_psi = solution[-1] % (2*np.pi)
        dist1 = np.linalg.norm(final_psi - np.array([2*np.pi/3, 2*np.pi/3]))
        dist2 = np.linalg.norm(final_psi - np.array([4*np.pi/3, 4*np.pi/3]))
        traj_color = '#00BFFF' if dist1 < dist2 else '#FF6B6B'  # Bright colors for visibility

        # Plot trajectory with increasing alpha (time evolution)
        for j in range(len(trajectory_x) - 1):
            alpha_val = 0.3 + 0.6 * (j / len(trajectory_x))
            ax.plot(trajectory_x[j:j+2], trajectory_y[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.5, zorder=15)

        # Arrow at end
        if len(trajectory_x) > 10:
            ax.annotate('', xy=(trajectory_x[-1], trajectory_y[-1]),
                       xytext=(trajectory_x[-10], trajectory_y[-10]),
                       arrowprops=dict(arrowstyle='->', color=traj_color, lw=2, alpha=0.9),
                       zorder=16)

    # ===========================================
    # ATTRACTOR (Origin)
    # ===========================================

    # Pulsing circles to indicate "time flows here"
    for r, alpha in [(0.06, 0.5), (0.10, 0.35), (0.14, 0.2)]:
        circle = Circle((0, 0), r, fill=False, edgecolor='white',
                        linewidth=2.5, alpha=alpha, zorder=18)
        ax.add_patch(circle)

    # Central star
    ax.scatter(0, 0, c='white', s=400, marker='*', zorder=20,
               edgecolor='black', linewidth=1.5)

    # ===========================================
    # VERTEX MARKERS
    # ===========================================

    # Fundamental vertices
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']  # Bright R, G, B
    labels_fund = ['R', 'G', 'B']
    for w, c, l in zip(vertices, colors_fund, labels_fund):
        ax.scatter(*w, c=c, s=350, zorder=25, edgecolor='white', linewidth=2.5)
        direction = w / np.linalg.norm(w)
        ax.annotate(l, w + 0.11 * direction, fontsize=16, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='black')])

    # Anti-fundamental vertices
    colors_anti = ['#FF9999', '#99FF99', '#9999FF']
    labels_anti = ['R̄', 'Ḡ', 'B̄']
    for w, c, l in zip([w_Rbar, w_Gbar, w_Bbar], colors_anti, labels_anti):
        ax.scatter(*w, c=c, s=250, zorder=25, edgecolor='white', linewidth=2, marker='s')
        direction = w / np.linalg.norm(w)
        ax.annotate(l, w + 0.09 * direction, fontsize=13, color='white',
                   ha='center', va='center',
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # ===========================================
    # ANNOTATIONS
    # ===========================================

    # Main title
    ax.set_title('Geometry & Time Emergence from Color Field Dynamics\n'
                 'Energy Density Background with Phase Trajectories',
                 fontsize=16, fontweight='bold', pad=15, color='black')

    # Key insight box (top left)
    insight_text = (
        'Energy ρ peaks at color vertices (R, G, B)\n'
        'Energy minimum at center — but ρ ≠ 0!\n'
        'This non-zero energy drives time λ'
    )
    ax.text(0.02, 0.98, insight_text, transform=ax.transAxes, fontsize=11,
            verticalalignment='top', horizontalalignment='left',
            bbox=dict(boxstyle='round,pad=0.4', facecolor='black', alpha=0.7,
                     edgecolor='white', linewidth=2),
            color='white', fontweight='bold', zorder=30)

    # Color neutrality equation (bottom)
    eq_text = (
        'At attractor: $\\chi_R + \\chi_G + \\chi_B = 0$ (coherent sum vanishes)\n'
        'But: $|\\chi_R|^2 + |\\chi_G|^2 + |\\chi_B|^2 \\neq 0$ (energy persists → time emerges)'
    )
    ax.text(0.5, 0.02, eq_text, transform=ax.transAxes, fontsize=12,
            verticalalignment='bottom', horizontalalignment='center',
            bbox=dict(boxstyle='round,pad=0.4', facecolor='white', alpha=0.9,
                     edgecolor='orange', linewidth=2),
            color='black', zorder=30)

    # Legend
    from matplotlib.lines import Line2D
    from matplotlib.patches import Patch
    legend_elements = [
        Line2D([0], [0], color='cyan', linewidth=3, label='Fundamental (3)'),
        Line2D([0], [0], color='lightcoral', linewidth=3, linestyle='--', label='Anti-fundamental (3̄)'),
        Line2D([0], [0], color='#00BFFF', linewidth=2, label='Trajectory → FP₁ (120°)'),
        Line2D([0], [0], color='#FF6B6B', linewidth=2, label='Trajectory → FP₂ (240°)'),
        Line2D([0], [0], marker='*', color='w', markerfacecolor='white',
               markersize=15, markeredgecolor='black', linestyle='None',
               label='Attractor (ρ_min ≠ 0)'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=10,
              facecolor='black', edgecolor='white', labelcolor='white',
              framealpha=0.8)

    # Axis styling
    ax.set_xlim(-0.95, 0.95)
    ax.set_ylim(-0.95, 0.95)
    ax.set_xlabel('Weight Space / Phase Space Coordinate', fontsize=12)
    ax.set_ylabel('Weight Space / Phase Space Coordinate', fontsize=12)
    ax.set_aspect('equal')

    # Grid with subtle styling
    ax.grid(True, alpha=0.2, color='white', linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='white', linewidth=0.8, alpha=0.4)
    ax.axvline(x=0, color='white', linewidth=0.8, alpha=0.4)

    # Dark background for axis
    ax.set_facecolor('#1a1a2e')

    plt.tight_layout()

    return fig


def main():
    """Generate the unified diagram with energy overlay."""

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    print("Generating unified geometry diagram with energy density overlay...")

    fig = create_unified_diagram_with_energy()
    path = output_dir / "unified_geometry_energy_overlay.png"
    fig.savefig(path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {path}")
    plt.close(fig)

    print("\nThe diagram shows:")
    print("  • Background: Energy density ρ = Σ|χ_c|² (inferno colormap)")
    print("  • Bright spots at R, G, B vertices where energy peaks")
    print("  • Dark region at center but energy is NON-ZERO there")
    print("  • Trajectories converge to center (energy minimum)")
    print("  • White star marks the attractor where time emerges")


if __name__ == "__main__":
    main()
