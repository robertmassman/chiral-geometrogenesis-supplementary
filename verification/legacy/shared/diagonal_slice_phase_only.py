#!/usr/bin/env python3
"""
Diagonal Slice with Phase Trajectories Only
============================================

Maps the phase dynamics from theorem 2.2.1 onto the diagonal slice view.
No energy background - just the phase trajectories converging to the dark band.

The mapping:
- Phase space: (ψ₁, ψ₂) where ψ₁ = φ_G - φ_R, ψ₂ = φ_B - φ_G
- Attractor at (2π/3, 2π/3) → color neutrality
- We map this to the (x, z) diagonal slice coordinates

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patheffects as path_effects
from scipy.integrate import odeint
from pathlib import Path

# ============================================================================
# CONSTANTS
# ============================================================================

ALPHA = 2 * np.pi / 3  # 120° phase frustration
R_STELLA = 1.0

# Stella octangula vertices (for reference markers)
STELLA_VERTICES = {
    'R': np.array([1, 1, 1]) / np.sqrt(3) * R_STELLA,
    'G': np.array([1, -1, -1]) / np.sqrt(3) * R_STELLA,
    'B': np.array([-1, 1, -1]) / np.sqrt(3) * R_STELLA,
    'W': np.array([-1, -1, 1]) / np.sqrt(3) * R_STELLA
}

# ============================================================================
# PHASE DYNAMICS (from theorem 2.2.1)
# ============================================================================

def phase_difference_dynamics(psi: np.ndarray, t: float, K: float) -> np.ndarray:
    """
    Phase-difference dynamics from Sakaguchi-Kuramoto model.
    ψ₁ = φ_G - φ_R, ψ₂ = φ_B - φ_G
    """
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


def phase_to_slice_coords(psi1, psi2, scale=1.2):
    """
    Map phase differences (ψ₁, ψ₂) to diagonal slice coordinates (x, z).

    The color sum: χ = e^(iφ_R) + e^(iφ_G) + e^(iφ_B)
    With φ_R = 0, φ_G = ψ₁, φ_B = ψ₁ + ψ₂

    At equilibrium (ψ₁ = ψ₂ = 2π/3): χ = 1 + ω + ω² = 0 (color neutral)

    We map the complex color sum to (x, z) coordinates on the slice.
    """
    phi_R = 0
    phi_G = psi1
    phi_B = psi1 + psi2

    # Complex color sum
    z_R = np.exp(1j * phi_R)
    z_G = np.exp(1j * phi_G)
    z_B = np.exp(1j * phi_B)
    color_sum = (z_R + z_G + z_B) / 3

    # Map to (x, z) - real part to x, imaginary part to z
    x = scale * np.real(color_sum)
    z = scale * np.imag(color_sum)

    return x, z


def main():
    """Generate the diagonal slice with phase trajectories."""

    fig, ax = plt.subplots(figsize=(10, 10))

    extent = 1.5

    # ===========================================
    # Draw the "dark band" as a reference line
    # ===========================================
    # The dark band is where the phase trajectories converge
    # In the original diagonal slice, it runs from upper-left to lower-right
    # For this mapping, the attractor is at the ORIGIN (color sum = 0)

    # Draw coordinate axes
    ax.axhline(y=0, color='gray', linewidth=1, alpha=0.5, linestyle='--')
    ax.axvline(x=0, color='gray', linewidth=1, alpha=0.5, linestyle='--')

    # ===========================================
    # PHASE TRAJECTORIES
    # ===========================================

    K = 1.0
    # Longer integration time to ensure trajectories reach final attractor
    # (not just slow down at saddle points)
    t_span = np.linspace(0, 150, 1500)
    np.random.seed(42)
    n_traj = 30

    # Color trajectories by which attractor they approach
    # FP1: (2π/3, 2π/3) and FP2: (4π/3, 4π/3)

    for i in range(n_traj):
        # Random initial phase differences
        psi0 = np.array([
            np.random.uniform(0, 2*np.pi),
            np.random.uniform(0, 2*np.pi)
        ])

        # Integrate the dynamics
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))

        # Map to slice coordinates
        traj_x = []
        traj_z = []
        for psi in solution:
            x, z = phase_to_slice_coords(psi[0], psi[1])
            traj_x.append(x)
            traj_z.append(z)

        traj_x = np.array(traj_x)
        traj_z = np.array(traj_z)

        # Determine which attractor (for coloring)
        final_psi = solution[-1] % (2*np.pi)
        dist1 = np.linalg.norm(final_psi - np.array([2*np.pi/3, 2*np.pi/3]))
        dist2 = np.linalg.norm(final_psi - np.array([4*np.pi/3, 4*np.pi/3]))

        if dist1 < dist2:
            traj_color = '#00BFFF'  # Blue for FP1
        else:
            traj_color = '#FF6B6B'  # Red for FP2

        # Plot trajectory with increasing alpha
        for j in range(len(traj_x) - 1):
            alpha_val = 0.2 + 0.7 * (j / len(traj_x))
            ax.plot(traj_x[j:j+2], traj_z[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.5)

        # Arrow at end
        if len(traj_x) > 10:
            ax.annotate('', xy=(traj_x[-1], traj_z[-1]),
                       xytext=(traj_x[-10], traj_z[-10]),
                       arrowprops=dict(arrowstyle='->', color=traj_color, lw=2, alpha=0.9))

    # ===========================================
    # MARK THE ATTRACTOR (origin = color neutrality)
    # ===========================================

    ax.scatter(0, 0, c='white', s=300, marker='*', zorder=20,
               edgecolor='black', linewidth=2)
    ax.annotate('Color Neutral\n(χ_R + χ_G + χ_B = 0)',
                (0.05, -0.1), fontsize=11, fontweight='bold',
                ha='left', va='top', color='black',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.9,
                         edgecolor='gold', linewidth=2))

    # ===========================================
    # VERTEX REFERENCE MARKERS (projected)
    # ===========================================

    # Show where the stella vertices would project in this space
    # R, G, B at their initial phases (before dynamics)
    for name, color in [('R', '#FF4444'), ('G', '#44FF44'), ('B', '#4444FF')]:
        v = STELLA_VERTICES[name]
        ax.plot(v[0], v[2], 'o', markersize=15, color=color,
               markeredgecolor='white', markeredgewidth=2, zorder=15)
        ax.annotate(name, (v[0] + 0.08, v[2] + 0.08), fontsize=14, color=color,
                   fontweight='bold',
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='white')])

    # W vertex
    v = STELLA_VERTICES['W']
    ax.plot(v[0], v[2], '*', markersize=18, color='gold',
           markeredgecolor='black', markeredgewidth=1, zorder=15)
    ax.annotate('W', (v[0] + 0.08, v[2] + 0.08), fontsize=14, color='gold',
               fontweight='bold',
               path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # ===========================================
    # LEGEND AND LABELS
    # ===========================================

    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='#00BFFF', linewidth=2, label='→ FP₁ (ψ = 120°)'),
        Line2D([0], [0], color='#FF6B6B', linewidth=2, label='→ FP₂ (ψ = 240°)'),
        Line2D([0], [0], marker='*', color='w', markerfacecolor='white',
               markersize=15, markeredgecolor='black', linestyle='None',
               label='Attractor (χ = 0)'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=11,
              facecolor='white', edgecolor='gray', framealpha=0.9)

    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)
    ax.set_xlabel('Re(χ_total) / Color Sum Real Part', fontsize=12)
    ax.set_ylabel('Im(χ_total) / Color Sum Imaginary Part', fontsize=12)
    ax.set_title('Phase Dynamics Mapped to Diagonal Slice Coordinates\n'
                 'Trajectories converge to color neutrality (χ = 0)',
                 fontsize=14, fontweight='bold', pad=15)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3, linestyle='-', linewidth=0.5)
    ax.set_facecolor('#f8f8f8')

    plt.tight_layout()

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)
    path = output_dir / "diagonal_slice_phase_only.png"
    fig.savefig(path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {path}")
    plt.close()

    print("\nThis plot shows:")
    print("  • Phase trajectories from theorem 2.2.1")
    print("  • Mapped to color sum space (Re(χ), Im(χ))")
    print("  • All trajectories converge to origin (color neutrality)")
    print("  • Blue = FP₁ attractor, Red = FP₂ attractor")


if __name__ == "__main__":
    main()
