#!/usr/bin/env python3
"""
Unified Geometry & Time Emergence Diagram
==========================================

A single comprehensive plot showing:
1. The SU(3) weight structure (geometry)
2. Phase dynamics converging to color neutrality
3. The key insight: coherent field vanishes at center, but ENERGY persists
4. This persistent energy is what drives internal time λ

The central message: TIME EMERGES from the geometric structure.

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Circle, FancyArrowPatch, Rectangle
from matplotlib.collections import LineCollection
from matplotlib.colors import LinearSegmentedColormap
from scipy.integrate import odeint
from mpl_toolkits.axes_grid1.inset_locator import inset_axes
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


def compute_coherent_field(x, y, vertices, sigma=0.4):
    """
    Compute |χ_total|² - the COHERENT sum of color fields.
    This vanishes at the center due to destructive interference.
    """
    chi_total = 0j
    phases = [0, 2*np.pi/3, 4*np.pi/3]  # Cube roots of unity

    for v, phase in zip(vertices, phases):
        # Each color field as Gaussian localized at vertex with phase
        r2 = (x - v[0])**2 + (y - v[1])**2
        amplitude = np.exp(-r2 / (2 * sigma**2))
        chi_total += amplitude * np.exp(1j * phase)

    return np.abs(chi_total)**2


def compute_incoherent_energy(x, y, vertices, sigma=0.4):
    """
    Compute ρ = Σ|χ_c|² - the INCOHERENT sum (energy density).
    This is NON-ZERO everywhere, including at center.
    """
    rho = 0

    for v in vertices:
        r2 = (x - v[0])**2 + (y - v[1])**2
        amplitude = np.exp(-r2 / (2 * sigma**2))
        rho += amplitude**2

    return rho


# ============================================================================
# MAIN UNIFIED PLOT
# ============================================================================

def create_unified_emergence_diagram():
    """
    Create the unified diagram showing geometry AND time emergence.
    """
    fig = plt.figure(figsize=(14, 12))

    # Main axis for the weight/phase diagram
    ax_main = fig.add_axes([0.08, 0.25, 0.6, 0.65])

    # Inset for coherent field (vanishes at center)
    ax_coherent = fig.add_axes([0.72, 0.55, 0.25, 0.32])

    # Inset for incoherent energy (non-zero at center)
    ax_energy = fig.add_axes([0.72, 0.12, 0.25, 0.32])

    # Bottom panel for the time emergence concept
    ax_time = fig.add_axes([0.08, 0.05, 0.6, 0.15])

    # ===========================================
    # MAIN PLOT: Weight diagram + trajectories
    # ===========================================

    scale = 0.6

    # Equilibrium positions (cube roots of unity)
    theta_R, theta_G, theta_B = 0, 2*np.pi/3, 4*np.pi/3
    w_R = scale * np.array([np.cos(theta_R), np.sin(theta_R)])
    w_G = scale * np.array([np.cos(theta_G), np.sin(theta_G)])
    w_B = scale * np.array([np.cos(theta_B), np.sin(theta_B)])

    vertices = [w_R, w_G, w_B]

    # Anti-fundamental
    w_Rbar, w_Gbar, w_Bbar = -w_R, -w_G, -w_B

    # Draw triangles
    fund_tri = Polygon([w_R, w_G, w_B], fill=True, facecolor='blue', alpha=0.08,
                       edgecolor='blue', linewidth=3, zorder=2)
    ax_main.add_patch(fund_tri)

    anti_tri = Polygon([w_Rbar, w_Gbar, w_Bbar], fill=True, facecolor='red', alpha=0.08,
                       edgecolor='red', linewidth=3, linestyle='--', zorder=2)
    ax_main.add_patch(anti_tri)

    # Unit circle
    theta_circle = np.linspace(0, 2*np.pi, 100)
    ax_main.plot(scale * np.cos(theta_circle), scale * np.sin(theta_circle),
                 'k-', alpha=0.2, linewidth=1, zorder=1)

    # Generate and plot trajectories
    K = 1.0
    t_span = np.linspace(0, 50, 500)
    np.random.seed(123)
    n_traj = 25

    all_trajectories = []

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
        all_trajectories.append((trajectory_x, trajectory_y, t_span))

        # Determine attractor
        final_psi = solution[-1] % (2*np.pi)
        dist1 = np.linalg.norm(final_psi - np.array([2*np.pi/3, 2*np.pi/3]))
        dist2 = np.linalg.norm(final_psi - np.array([4*np.pi/3, 4*np.pi/3]))
        color = 'blue' if dist1 < dist2 else 'red'

        # Plot with time-based coloring (alpha fades in)
        for j in range(len(trajectory_x) - 1):
            alpha_val = 0.2 + 0.5 * (j / len(trajectory_x))
            ax_main.plot(trajectory_x[j:j+2], trajectory_y[j:j+2],
                        color=color, alpha=alpha_val, linewidth=1.2, zorder=3)

        # Arrow at end
        if len(trajectory_x) > 10:
            ax_main.annotate('', xy=(trajectory_x[-1], trajectory_y[-1]),
                            xytext=(trajectory_x[-10], trajectory_y[-10]),
                            arrowprops=dict(arrowstyle='->', color=color, lw=1.5, alpha=0.7),
                            zorder=4)

    # Origin - THE ATTRACTOR (color neutral, but energy persists!)
    ax_main.scatter(0, 0, c='gold', s=500, marker='*', zorder=20,
                    edgecolor='black', linewidth=2)

    # Pulsing circles to show "time" at the attractor
    for r, alpha in [(0.08, 0.3), (0.12, 0.2), (0.16, 0.1)]:
        circle = Circle((0, 0), r, fill=False, edgecolor='gold',
                        linewidth=2, alpha=alpha, linestyle='-', zorder=19)
        ax_main.add_patch(circle)

    ax_main.annotate('Color Neutral\nATTRACTOR\n(ρ ≠ 0: Time flows!)',
                     (0.1, -0.15), fontsize=11, fontweight='bold',
                     ha='left', zorder=20,
                     bbox=dict(boxstyle='round,pad=0.3', facecolor='lightyellow',
                              edgecolor='orange', linewidth=2))

    # Color vertices
    colors_fund = ['#D32F2F', '#388E3C', '#1976D2']
    labels_fund = ['R (0°)', 'G (120°)', 'B (240°)']
    for w, c, l in zip([w_R, w_G, w_B], colors_fund, labels_fund):
        ax_main.scatter(*w, c=c, s=250, zorder=15, edgecolor='black', linewidth=2)
        direction = w / np.linalg.norm(w)
        ax_main.annotate(l, w + 0.12 * direction, fontsize=12, fontweight='bold',
                        color=c, ha='center', va='center')

    # Anti-fundamental vertices
    colors_anti = ['#EF9A9A', '#A5D6A7', '#90CAF9']
    labels_anti = ['R̄', 'Ḡ', 'B̄']
    for w, c, l in zip([w_Rbar, w_Gbar, w_Bbar], colors_anti, labels_anti):
        ax_main.scatter(*w, c=c, s=200, zorder=15, edgecolor='black', linewidth=2, marker='s')
        direction = w / np.linalg.norm(w)
        ax_main.annotate(l, w + 0.10 * direction, fontsize=11, color='gray', ha='center')

    ax_main.set_xlim(-1.0, 1.0)
    ax_main.set_ylim(-0.9, 1.0)
    ax_main.set_xlabel('Re$(\\chi_R + \\chi_G + \\chi_B)$ — Coherent Sum', fontsize=12)
    ax_main.set_ylabel('Im$(\\chi_R + \\chi_G + \\chi_B)$', fontsize=12)
    ax_main.set_title('Geometry Emergence: Phase Dynamics → SU(3) Structure',
                      fontsize=14, fontweight='bold', pad=10)
    ax_main.set_aspect('equal')
    ax_main.grid(True, alpha=0.3)
    ax_main.axhline(y=0, color='k', linewidth=0.8, alpha=0.5)
    ax_main.axvline(x=0, color='k', linewidth=0.8, alpha=0.5)

    # ===========================================
    # INSET 1: Coherent field |χ_total|²
    # ===========================================

    # Grid for field plots
    x_grid = np.linspace(-1, 1, 100)
    y_grid = np.linspace(-1, 1, 100)
    X, Y = np.meshgrid(x_grid, y_grid)

    # Coherent field
    chi_coherent = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            chi_coherent[i, j] = compute_coherent_field(X[i, j], Y[i, j], vertices, sigma=0.35)

    im1 = ax_coherent.contourf(X, Y, chi_coherent, levels=30, cmap='viridis')
    ax_coherent.scatter(0, 0, c='white', s=150, marker='*', edgecolor='black', linewidth=1.5, zorder=10)

    # Mark vertices
    for v, c in zip(vertices, colors_fund):
        ax_coherent.scatter(*v, c=c, s=80, edgecolor='white', linewidth=1, zorder=10)

    ax_coherent.set_title('$|\\chi_{total}|^2$ (Coherent)\n**VANISHES at center**',
                          fontsize=11, fontweight='bold')
    ax_coherent.set_xlim(-0.9, 0.9)
    ax_coherent.set_ylim(-0.9, 0.9)
    ax_coherent.set_aspect('equal')
    ax_coherent.set_xticks([])
    ax_coherent.set_yticks([])

    # Add colorbar
    cbar1 = plt.colorbar(im1, ax=ax_coherent, fraction=0.046, pad=0.04)
    cbar1.set_label('$|\\chi_R + \\chi_G + \\chi_B|^2$', fontsize=9)

    # ===========================================
    # INSET 2: Incoherent energy ρ
    # ===========================================

    rho_energy = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy[i, j] = compute_incoherent_energy(X[i, j], Y[i, j], vertices, sigma=0.35)

    im2 = ax_energy.contourf(X, Y, rho_energy, levels=30, cmap='magma')
    ax_energy.scatter(0, 0, c='white', s=150, marker='*', edgecolor='black', linewidth=1.5, zorder=10)

    for v, c in zip(vertices, colors_fund):
        ax_energy.scatter(*v, c=c, s=80, edgecolor='white', linewidth=1, zorder=10)

    ax_energy.set_title('$\\rho = \\Sigma|\\chi_c|^2$ (Energy)\n**NON-ZERO at center!**',
                        fontsize=11, fontweight='bold')
    ax_energy.set_xlim(-0.9, 0.9)
    ax_energy.set_ylim(-0.9, 0.9)
    ax_energy.set_aspect('equal')
    ax_energy.set_xticks([])
    ax_energy.set_yticks([])

    cbar2 = plt.colorbar(im2, ax=ax_energy, fraction=0.046, pad=0.04)
    cbar2.set_label('$|\\chi_R|^2 + |\\chi_G|^2 + |\\chi_B|^2$', fontsize=9)

    # Arrow connecting the insets with explanation
    fig.text(0.695, 0.47, '↓', fontsize=30, ha='center', va='center', color='orange', fontweight='bold')
    fig.text(0.85, 0.47, 'Coherent sum\nCANCELS\nbut energy\nPERSISTS',
             fontsize=10, ha='center', va='center',
             bbox=dict(boxstyle='round', facecolor='lightyellow', edgecolor='orange'))

    # ===========================================
    # BOTTOM PANEL: Time emergence concept
    # ===========================================

    ax_time.set_xlim(0, 10)
    ax_time.set_ylim(0, 1)
    ax_time.axis('off')

    # Draw the conceptual flow
    # Box 1: Geometry
    rect1 = Rectangle((0.3, 0.2), 2, 0.6, fill=True, facecolor='lightblue',
                       edgecolor='blue', linewidth=2)
    ax_time.add_patch(rect1)
    ax_time.text(1.3, 0.5, 'SU(3) Geometry\n(Weight Diagram)', fontsize=10,
                ha='center', va='center', fontweight='bold')

    # Arrow 1
    ax_time.annotate('', xy=(3.0, 0.5), xytext=(2.5, 0.5),
                    arrowprops=dict(arrowstyle='->', color='black', lw=2))

    # Box 2: Color Neutrality
    rect2 = Rectangle((3.2, 0.2), 2.2, 0.6, fill=True, facecolor='lightyellow',
                       edgecolor='orange', linewidth=2)
    ax_time.add_patch(rect2)
    ax_time.text(4.3, 0.5, 'Color Neutrality\n$\\chi_R + \\chi_G + \\chi_B = 0$',
                fontsize=10, ha='center', va='center', fontweight='bold')

    # Arrow 2
    ax_time.annotate('', xy=(6.1, 0.5), xytext=(5.6, 0.5),
                    arrowprops=dict(arrowstyle='->', color='black', lw=2))

    # Box 3: Energy persists
    rect3 = Rectangle((6.3, 0.2), 2.2, 0.6, fill=True, facecolor='#FFE0E0',
                       edgecolor='red', linewidth=2)
    ax_time.add_patch(rect3)
    ax_time.text(7.4, 0.5, 'Energy Persists\n$\\rho = \\Sigma|\\chi_c|^2 \\neq 0$',
                fontsize=10, ha='center', va='center', fontweight='bold')

    # Arrow 3
    ax_time.annotate('', xy=(9.2, 0.5), xytext=(8.7, 0.5),
                    arrowprops=dict(arrowstyle='->', color='black', lw=2))

    # Box 4: TIME
    rect4 = Rectangle((9.0, 0.1), 0.9, 0.8, fill=True, facecolor='gold',
                       edgecolor='black', linewidth=3)
    ax_time.add_patch(rect4)
    ax_time.text(9.45, 0.5, 'TIME\n$\\lambda$', fontsize=12,
                ha='center', va='center', fontweight='bold')

    # ===========================================
    # MAIN TITLE AND ANNOTATIONS
    # ===========================================

    fig.suptitle('Emergence of Geometry and Time from Color Field Dynamics',
                fontsize=18, fontweight='bold', y=0.97)

    # Key insight annotation
    fig.text(0.5, 0.215,
            'Key Insight: The coherent color sum vanishes at the attractor (color neutrality), '
            'but the incoherent energy sum persists.\n'
            'This non-zero energy density drives the internal time parameter λ — TIME EMERGES from the geometry.',
            ha='center', fontsize=11, style='italic',
            bbox=dict(boxstyle='round,pad=0.5', facecolor='white', edgecolor='gray', alpha=0.9))

    return fig


def main():
    """Generate the unified emergence diagram."""

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    print("Generating unified geometry + time emergence diagram...")

    fig = create_unified_emergence_diagram()
    path = output_dir / "unified_geometry_time_emergence.png"
    fig.savefig(path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {path}")
    plt.close(fig)

    print("\nDiagram shows:")
    print("  • Main panel: Phase trajectories converging to color-neutral origin")
    print("  • Top inset: Coherent field |χ_total|² VANISHES at center")
    print("  • Bottom inset: Energy density ρ is NON-ZERO at center")
    print("  • Flow diagram: Geometry → Color Neutrality → Energy → TIME")
    print("\nThis is the emergence of time from geometric structure!")


if __name__ == "__main__":
    main()
