#!/usr/bin/env python3
"""
Unified Weight-Phase Diagram
============================

A single plot showing the SU(3) weight diagram with phase dynamics
superimposed, demonstrating how the geometric structure emerges
from the dynamical evolution.

The key insight: the phase differences (ψ₁, ψ₂) can be mapped
directly onto the weight space, showing that trajectories
converge to the vertices of the weight diagram.

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Circle, FancyArrowPatch
from matplotlib.collections import LineCollection
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


def phases_to_weight_space(phi_R, phi_G, phi_B):
    """
    Map three phases to weight space coordinates.

    The phases define a point in the complex plane via the color sum:
    z = e^(iφ_R) + e^(iφ_G) + e^(iφ_B)

    At color neutrality, z = 0 (the origin/singlet).

    We use an alternative mapping that shows the structure better:
    Map to the centroid of the three unit vectors, scaled.
    """
    # Complex unit vectors for each color
    z_R = np.exp(1j * phi_R)
    z_G = np.exp(1j * phi_G)
    z_B = np.exp(1j * phi_B)

    # The color sum (should approach 0 for 120° separation)
    color_sum = z_R + z_G + z_B

    return np.real(color_sum), np.imag(color_sum)


def phase_diffs_to_weight_coords(psi1, psi2):
    """
    Map phase differences to weight-like coordinates.

    ψ₁ = φ_G - φ_R, ψ₂ = φ_B - φ_G

    We map these to coordinates that show the hexagonal structure:
    - (2π/3, 2π/3) → one stable FP (R→G→B)
    - (4π/3, 4π/3) → other stable FP (R→B→G)
    - (0, 0) → synchronized (unstable)

    Use a transformation that maps the torus to the weight plane.
    """
    # Transform to show hexagonal structure
    # Use the phase angles to create x, y coordinates
    x = (np.cos(psi1) + np.cos(psi1 + psi2)) / 2
    y = (np.sin(psi1) + np.sin(psi1 + psi2)) / 2

    return x, y


def get_color_positions_from_phases(phi_R, phi_G, phi_B, scale=0.5):
    """
    Get positions of R, G, B in weight space given their phases.
    Each color is represented as a unit vector scaled and offset.
    """
    # Unit vectors for each phase
    R_pos = scale * np.array([np.cos(phi_R), np.sin(phi_R)])
    G_pos = scale * np.array([np.cos(phi_G), np.sin(phi_G)])
    B_pos = scale * np.array([np.cos(phi_B), np.sin(phi_B)])

    return R_pos, G_pos, B_pos


# ============================================================================
# UNIFIED PLOT
# ============================================================================

def create_unified_diagram():
    """
    Create a single unified diagram showing weight structure and phase dynamics.
    """
    fig, ax = plt.subplots(figsize=(12, 12))

    # ===========================================
    # BACKGROUND: Weight diagram structure
    # ===========================================

    # The equilibrium positions (cube roots of unity scaled)
    scale = 0.6

    # Fundamental triangle vertices (120° apart)
    theta_R = 0
    theta_G = 2 * np.pi / 3
    theta_B = 4 * np.pi / 3

    w_R = scale * np.array([np.cos(theta_R), np.sin(theta_R)])
    w_G = scale * np.array([np.cos(theta_G), np.sin(theta_G)])
    w_B = scale * np.array([np.cos(theta_B), np.sin(theta_B)])

    # Anti-fundamental (opposite)
    w_Rbar = -w_R
    w_Gbar = -w_G
    w_Bbar = -w_B

    # Draw fundamental triangle (thick, prominent)
    fund_verts = np.array([w_R, w_G, w_B])
    fund_tri = Polygon(fund_verts, fill=True, facecolor='blue', alpha=0.08,
                       edgecolor='blue', linewidth=3, linestyle='-', zorder=2)
    ax.add_patch(fund_tri)

    # Draw anti-fundamental triangle
    anti_verts = np.array([w_Rbar, w_Gbar, w_Bbar])
    anti_tri = Polygon(anti_verts, fill=True, facecolor='red', alpha=0.08,
                       edgecolor='red', linewidth=3, linestyle='--', zorder=2)
    ax.add_patch(anti_tri)

    # Unit circle (phase space boundary)
    theta_circle = np.linspace(0, 2*np.pi, 100)
    ax.plot(scale * np.cos(theta_circle), scale * np.sin(theta_circle),
            'k-', alpha=0.2, linewidth=1, zorder=1)

    # ===========================================
    # PHASE DYNAMICS: Trajectories
    # ===========================================

    K = 1.0
    t_span = np.linspace(0, 50, 500)

    # Generate trajectories from various initial conditions
    np.random.seed(123)
    n_traj = 25

    for i in range(n_traj):
        # Random initial phases
        phi0_R = 0  # Fix R phase (gauge choice)
        phi0_G = np.random.uniform(0, 2*np.pi)
        phi0_B = np.random.uniform(0, 2*np.pi)

        psi0 = np.array([phi0_G - phi0_R, phi0_B - phi0_G])

        # Integrate
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))

        # Convert trajectory to weight space coordinates
        trajectory_x = []
        trajectory_y = []

        for psi in solution:
            psi1, psi2 = psi
            # Reconstruct phases (with R fixed at 0)
            phi_R = 0
            phi_G = psi1
            phi_B = psi1 + psi2

            # Get color positions and compute centroid-like coordinate
            # Use the "imbalance" from perfect 120° as the coordinate
            z_R = np.exp(1j * phi_R)
            z_G = np.exp(1j * phi_G)
            z_B = np.exp(1j * phi_B)

            # Color sum (deviation from neutrality)
            color_sum = (z_R + z_G + z_B) / 3

            trajectory_x.append(scale * np.real(color_sum) * 3)
            trajectory_y.append(scale * np.imag(color_sum) * 3)

        trajectory_x = np.array(trajectory_x)
        trajectory_y = np.array(trajectory_y)

        # Color by time (early = light, late = dark)
        points = np.array([trajectory_x, trajectory_y]).T.reshape(-1, 1, 2)
        segments = np.concatenate([points[:-1], points[1:]], axis=1)

        # Determine which attractor this trajectory goes to
        final_psi1 = solution[-1, 0] % (2*np.pi)
        final_psi2 = solution[-1, 1] % (2*np.pi)

        # Check if closer to FP1 (2π/3, 2π/3) or FP2 (4π/3, 4π/3)
        dist_FP1 = np.sqrt((final_psi1 - 2*np.pi/3)**2 + (final_psi2 - 2*np.pi/3)**2)
        dist_FP2 = np.sqrt((final_psi1 - 4*np.pi/3)**2 + (final_psi2 - 4*np.pi/3)**2)

        if dist_FP1 < dist_FP2:
            color = 'blue'
        else:
            color = 'red'

        ax.plot(trajectory_x, trajectory_y, color=color, alpha=0.4, linewidth=1, zorder=3)

        # Arrow at end showing direction
        if len(trajectory_x) > 10:
            ax.annotate('', xy=(trajectory_x[-1], trajectory_y[-1]),
                       xytext=(trajectory_x[-10], trajectory_y[-10]),
                       arrowprops=dict(arrowstyle='->', color=color, lw=1.5, alpha=0.6),
                       zorder=4)

    # ===========================================
    # FIXED POINTS AND VERTICES
    # ===========================================

    # Origin (singlet / color neutral state) - this is the ATTRACTOR
    ax.scatter(0, 0, c='gold', s=400, marker='*', zorder=20,
               edgecolor='black', linewidth=2)
    ax.annotate('Color Neutral\n(Attractor)', (0.08, -0.12), fontsize=11,
               fontweight='bold', ha='left', zorder=20)

    # Fundamental vertices (R, G, B)
    colors_fund = ['#D32F2F', '#388E3C', '#1976D2']
    labels_fund = ['R (0°)', 'G (120°)', 'B (240°)']
    for w, c, l in zip([w_R, w_G, w_B], colors_fund, labels_fund):
        ax.scatter(*w, c=c, s=250, zorder=15, edgecolor='black', linewidth=2)
        # Label outside
        direction = w / np.linalg.norm(w)
        label_pos = w + 0.12 * direction
        ax.annotate(l, label_pos, fontsize=12, fontweight='bold', color=c,
                   ha='center', va='center', zorder=15)

    # Anti-fundamental vertices
    colors_anti = ['#EF9A9A', '#A5D6A7', '#90CAF9']
    labels_anti = ['R̄', 'Ḡ', 'B̄']
    for w, c, l in zip([w_Rbar, w_Gbar, w_Bbar], colors_anti, labels_anti):
        ax.scatter(*w, c=c, s=200, zorder=15, edgecolor='black', linewidth=2, marker='s')
        direction = w / np.linalg.norm(w)
        label_pos = w + 0.10 * direction
        ax.annotate(l, label_pos, fontsize=11, color='gray', ha='center', va='center')

    # ===========================================
    # ANNOTATIONS
    # ===========================================

    # Title
    ax.set_title('Unified Weight-Phase Diagram\n'
                 'Phase Dynamics Converge to Color Neutrality',
                 fontsize=16, fontweight='bold', pad=20)

    # Key equation box
    eq_text = (
        'Color Neutrality Condition:\n'
        '$e^{i\\phi_R} + e^{i\\phi_G} + e^{i\\phi_B} = 0$\n\n'
        'Equivalent to:\n'
        '$1 + \\omega + \\omega^2 = 0$\n'
        'where $\\omega = e^{2\\pi i/3}$'
    )
    ax.text(0.98, 0.98, eq_text, transform=ax.transAxes, fontsize=11,
            verticalalignment='top', horizontalalignment='right',
            bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow',
                     edgecolor='orange', linewidth=2),
            zorder=25)

    # Dynamics explanation
    dynamics_text = (
        'Trajectories show phase\n'
        'evolution under Sakaguchi-\n'
        'Kuramoto dynamics.\n\n'
        'All paths converge to\n'
        'the color-neutral origin\n'
        '(120° phase separation).'
    )
    ax.text(0.02, 0.98, dynamics_text, transform=ax.transAxes, fontsize=10,
            verticalalignment='top', horizontalalignment='left',
            bbox=dict(boxstyle='round,pad=0.5', facecolor='lightcyan',
                     edgecolor='steelblue', linewidth=2),
            zorder=25)

    # Legend
    from matplotlib.patches import Patch
    from matplotlib.lines import Line2D
    legend_elements = [
        Patch(facecolor='blue', alpha=0.2, edgecolor='blue', linewidth=2,
              label='Fundamental (3)'),
        Patch(facecolor='red', alpha=0.2, edgecolor='red', linewidth=2,
              linestyle='--', label='Anti-fundamental (3̄)'),
        Line2D([0], [0], color='blue', alpha=0.5, linewidth=2,
               label='Trajectory → FP₁'),
        Line2D([0], [0], color='red', alpha=0.5, linewidth=2,
               label='Trajectory → FP₂'),
        Line2D([0], [0], marker='*', color='w', markerfacecolor='gold',
               markersize=15, markeredgecolor='black', label='Color neutral (attractor)'),
    ]
    ax.legend(handles=legend_elements, loc='lower right', fontsize=10)

    # Axis styling
    ax.set_xlim(-1.0, 1.0)
    ax.set_ylim(-1.0, 1.0)
    ax.set_xlabel('Re$(e^{i\\phi_R} + e^{i\\phi_G} + e^{i\\phi_B})/3$', fontsize=12)
    ax.set_ylabel('Im$(e^{i\\phi_R} + e^{i\\phi_G} + e^{i\\phi_B})/3$', fontsize=12)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3, linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='k', linewidth=0.8, alpha=0.5)
    ax.axvline(x=0, color='k', linewidth=0.8, alpha=0.5)

    plt.tight_layout()

    return fig


def create_unified_diagram_v2():
    """
    Alternative unified diagram: show the phase portrait WITH weight structure overlay.
    This version keeps the torus coordinates but overlays the weight triangles.
    """
    fig, ax = plt.subplots(figsize=(12, 12))

    K = 1.0

    # ===========================================
    # VECTOR FIELD on the torus
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

    ax.quiver(np.degrees(PSI1), np.degrees(PSI2), DPSI1_norm, DPSI2_norm,
              magnitude, cmap='viridis', alpha=0.5, scale=25, zorder=1)

    # ===========================================
    # TRAJECTORIES
    # ===========================================

    np.random.seed(42)
    t_span = np.linspace(0, 40, 400)

    for _ in range(20):
        psi0 = np.random.uniform(0, 2*np.pi, 2)
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))

        # Determine attractor
        final = solution[-1] % (2*np.pi)
        dist1 = np.linalg.norm(final - np.array([2*np.pi/3, 2*np.pi/3]))
        dist2 = np.linalg.norm(final - np.array([4*np.pi/3, 4*np.pi/3]))
        color = 'blue' if dist1 < dist2 else 'red'

        ax.plot(np.degrees(solution[:, 0] % (2*np.pi)),
               np.degrees(solution[:, 1] % (2*np.pi)),
               color=color, alpha=0.5, linewidth=1.2, zorder=5)

    # ===========================================
    # WEIGHT DIAGRAM OVERLAY (transformed to torus coords)
    # ===========================================

    # The key insight: the equilibrium phases map to specific (ψ₁, ψ₂) values
    # FP1: (120°, 120°) = fundamental chirality R→G→B
    # FP2: (240°, 240°) = anti-fundamental chirality R→B→G

    # Draw the "weight triangles" in phase-difference space
    # Fundamental: connects the three cyclic permutations
    fp1 = np.array([120, 120])  # R→G→B
    fp1_shift1 = np.array([120, 240])  # Shifted
    fp1_shift2 = np.array([240, 120])

    # These don't form a simple triangle in (ψ₁, ψ₂) space
    # Instead, mark the key points

    # Stable fixed points
    ax.plot(120, 120, 'o', color='#1976D2', markersize=25,
           markeredgecolor='black', markeredgewidth=3, zorder=20)
    ax.annotate('FP₁: R→G→B\n(Fundamental)', (135, 90), fontsize=12,
               fontweight='bold', color='#1976D2',
               bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.9),
               zorder=25)

    ax.plot(240, 240, 'o', color='#D32F2F', markersize=25,
           markeredgecolor='black', markeredgewidth=3, zorder=20)
    ax.annotate('FP₂: R→B→G\n(Anti-fundamental)', (255, 210), fontsize=12,
               fontweight='bold', color='#D32F2F',
               bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.9),
               zorder=25)

    # Unstable fixed point (synchronized)
    ax.plot(0, 0, 's', color='gray', markersize=15,
           markeredgecolor='black', markeredgewidth=2, zorder=20)
    ax.plot(360, 360, 's', color='gray', markersize=15,
           markeredgecolor='black', markeredgewidth=2, zorder=20)
    ax.annotate('Sync\n(Unstable)', (15, 25), fontsize=10, color='gray')

    # Saddle points
    saddles = [(120, 240), (240, 120), (0, 120), (120, 0),
               (0, 240), (240, 0), (240, 360), (360, 240),
               (120, 360), (360, 120)]
    for s in saddles:
        if 0 <= s[0] <= 360 and 0 <= s[1] <= 360:
            ax.plot(s[0], s[1], 'd', color='orange', markersize=10,
                   markeredgecolor='black', markeredgewidth=1.5, zorder=15, alpha=0.7)

    # ===========================================
    # WEIGHT STRUCTURE VISUALIZATION
    # ===========================================

    # Draw diagonal line showing the "weight plane" embedding
    # The line ψ₁ = ψ₂ corresponds to symmetric configurations
    ax.plot([0, 360], [0, 360], 'k--', alpha=0.3, linewidth=2, zorder=2)
    ax.annotate('ψ₁ = ψ₂\n(symmetric)', (280, 320), fontsize=9,
               rotation=45, alpha=0.5, ha='center')

    # Highlight the "fundamental region"
    fund_region = Polygon([(0, 0), (180, 0), (180, 180), (0, 180)],
                          fill=True, facecolor='blue', alpha=0.05,
                          edgecolor='none', zorder=0)
    ax.add_patch(fund_region)

    anti_region = Polygon([(180, 180), (360, 180), (360, 360), (180, 360)],
                          fill=True, facecolor='red', alpha=0.05,
                          edgecolor='none', zorder=0)
    ax.add_patch(anti_region)

    # ===========================================
    # ANNOTATIONS
    # ===========================================

    ax.set_xlabel('ψ₁ = φ_G − φ_R (degrees)', fontsize=14)
    ax.set_ylabel('ψ₂ = φ_B − φ_G (degrees)', fontsize=14)
    ax.set_title('Unified Phase Portrait with SU(3) Structure\n'
                 'Weight Diagram Embedded in Dynamical Phase Space',
                 fontsize=16, fontweight='bold')

    ax.set_xlim(0, 360)
    ax.set_ylim(0, 360)
    ax.set_xticks([0, 60, 120, 180, 240, 300, 360])
    ax.set_yticks([0, 60, 120, 180, 240, 300, 360])
    ax.grid(True, alpha=0.3)
    ax.set_aspect('equal')

    # Key insight box
    insight_text = (
        'Key Insight:\n'
        '• FP₁ (120°,120°) = Fundamental rep.\n'
        '• FP₂ (240°,240°) = Anti-fundamental rep.\n'
        '• Both satisfy color neutrality\n'
        '• Geometry emerges from dynamics!'
    )
    ax.text(0.02, 0.02, insight_text, transform=ax.transAxes, fontsize=11,
            verticalalignment='bottom', horizontalalignment='left',
            bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow',
                     edgecolor='orange', linewidth=2),
            zorder=25)

    # Legend
    from matplotlib.lines import Line2D
    from matplotlib.patches import Patch
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#1976D2',
               markersize=15, markeredgecolor='black', label='Stable FP (Fund.)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#D32F2F',
               markersize=15, markeredgecolor='black', label='Stable FP (Anti-fund.)'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='gray',
               markersize=10, markeredgecolor='black', label='Unstable FP'),
        Line2D([0], [0], marker='d', color='w', markerfacecolor='orange',
               markersize=10, markeredgecolor='black', label='Saddle point'),
        Line2D([0], [0], color='blue', alpha=0.6, linewidth=2, label='Traj. → FP₁'),
        Line2D([0], [0], color='red', alpha=0.6, linewidth=2, label='Traj. → FP₂'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=10)

    plt.tight_layout()

    return fig


def main():
    """Generate unified diagrams."""

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    print("Generating unified weight-phase diagrams...")

    # Version 1: Color sum space
    fig1 = create_unified_diagram()
    path1 = output_dir / "unified_weight_phase_color_sum.png"
    fig1.savefig(path1, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {path1}")
    plt.close(fig1)

    # Version 2: Torus with weight overlay
    fig2 = create_unified_diagram_v2()
    path2 = output_dir / "unified_weight_phase_torus.png"
    fig2.savefig(path2, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {path2}")
    plt.close(fig2)

    print("\nUnified diagrams generated!")
    print("\nTwo complementary views:")
    print("  1. Color sum space: trajectories converge to origin (color neutrality)")
    print("  2. Torus space: weight structure embedded in phase portrait")


if __name__ == "__main__":
    main()
