#!/usr/bin/env python3
"""
Diagonal Slice with Phase Trajectories - Dark Band Mapping
==========================================================

Maps the phase dynamics from theorem 2.2.1 so that trajectories
flow toward the dark band (singlet axis) in the diagonal slice view.

The key insight:
- In the diagonal slice, the dark band runs along x + z = 0
- This is where χ_total ≈ 0 (color neutrality)
- Phase dynamics drive the system toward color neutrality
- So we map phase → position such that equilibrium → dark band

Mapping strategy:
- Color sum χ = e^(iφ_R) + e^(iφ_G) + e^(iφ_B)
- At equilibrium: χ = 0
- Away from equilibrium: |χ| > 0
- We use |χ| as radial distance from the dark band
- And arg(χ) to distribute around the band

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


def phase_to_color_sum(psi1, psi2):
    """
    Compute the complex color sum from phase differences.

    φ_R = 0, φ_G = ψ₁, φ_B = ψ₁ + ψ₂
    χ = e^(iφ_R) + e^(iφ_G) + e^(iφ_B)
    """
    phi_R = 0
    phi_G = psi1
    phi_B = psi1 + psi2

    z_R = np.exp(1j * phi_R)
    z_G = np.exp(1j * phi_G)
    z_B = np.exp(1j * phi_B)

    return z_R + z_G + z_B


def color_sum_to_slice_coords(chi, scale=1.0):
    """
    Map color sum to diagonal slice (x, z) coordinates.

    Strategy: The dark band is along x + z = 0.
    - |χ| = 0 → on the dark band
    - |χ| > 0 → away from the dark band

    We use:
    - perpendicular distance from band = |χ| * scale / 3
    - position along band determined by arg(χ)

    The band direction is (1, -1)/√2
    The perpendicular direction is (1, 1)/√2
    """
    mag = np.abs(chi) / 3  # Normalize (max |χ| = 3)
    phase = np.angle(chi)

    # Distance from dark band (perpendicular)
    perp_dist = mag * scale

    # Position along the band (parallel)
    # Use phase to spread trajectories along the band
    parallel_pos = np.sin(phase) * scale * 0.8

    # Dark band direction: (1, -1)/√2
    # Perpendicular: (1, 1)/√2
    band_dir = np.array([1, -1]) / np.sqrt(2)
    perp_dir = np.array([1, 1]) / np.sqrt(2)

    # Position = parallel along band + perpendicular away from band
    pos = parallel_pos * band_dir + perp_dist * perp_dir

    return pos[0], pos[1]


def phase_to_slice_direct(psi1, psi2, scale=1.2):
    """
    Direct mapping from phase differences to slice coordinates.
    """
    chi = phase_to_color_sum(psi1, psi2)
    return color_sum_to_slice_coords(chi, scale)


def main():
    """Generate the diagonal slice with phase trajectories flowing to dark band."""

    fig, ax = plt.subplots(figsize=(10, 10))

    extent = 1.5

    # ===========================================
    # Draw the dark band
    # ===========================================
    # The dark band runs along x + z = 0 (from upper-left to lower-right)
    band_x = np.array([-extent, extent])
    band_z = np.array([extent, -extent])
    ax.plot(band_x, band_z, color='black', linewidth=8, alpha=0.3,
            label='Singlet axis (χ = 0)', zorder=1)
    ax.plot(band_x, band_z, color='purple', linewidth=3, alpha=0.8,
            linestyle='--', zorder=2)

    # Draw coordinate axes
    ax.axhline(y=0, color='gray', linewidth=0.5, alpha=0.5, linestyle=':')
    ax.axvline(x=0, color='gray', linewidth=0.5, alpha=0.5, linestyle=':')

    # ===========================================
    # PHASE TRAJECTORIES
    # ===========================================

    K = 1.0
    # Longer integration time to ensure trajectories reach final attractor
    # (not just slow down at saddle points)
    t_span = np.linspace(0, 120, 1200)
    np.random.seed(42)
    n_traj = 35

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
            x, z = phase_to_slice_direct(psi[0], psi[1])
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

        # Plot trajectory with increasing alpha (fading in)
        for j in range(len(traj_x) - 1):
            alpha_val = 0.15 + 0.6 * (j / len(traj_x))
            ax.plot(traj_x[j:j+2], traj_z[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.5, zorder=5)

        # Arrow at end pointing toward the band
        if len(traj_x) > 15:
            ax.annotate('', xy=(traj_x[-1], traj_z[-1]),
                       xytext=(traj_x[-15], traj_z[-15]),
                       arrowprops=dict(arrowstyle='->', color=traj_color, lw=2, alpha=0.9),
                       zorder=10)

    # ===========================================
    # VERTEX REFERENCE MARKERS
    # ===========================================

    for name, color in [('R', '#FF4444'), ('G', '#44FF44'), ('B', '#4444FF')]:
        v = STELLA_VERTICES[name]
        ax.plot(v[0], v[2], 'o', markersize=18, color=color,
               markeredgecolor='white', markeredgewidth=2.5, zorder=15)
        ax.annotate(name, (v[0] + 0.1, v[2] + 0.1), fontsize=16, color=color,
                   fontweight='bold',
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='white')])

    # W vertex
    v = STELLA_VERTICES['W']
    ax.plot(v[0], v[2], '*', markersize=22, color='gold',
           markeredgecolor='black', markeredgewidth=1.5, zorder=15)
    ax.annotate('W', (v[0] + 0.1, v[2] + 0.1), fontsize=16, color='goldenrod',
               fontweight='bold',
               path_effects=[path_effects.withStroke(linewidth=3, foreground='white')])

    # Mark center
    ax.plot(0, 0, 'c+', markersize=20, markeredgewidth=3, zorder=12)

    # ===========================================
    # LEGEND AND LABELS
    # ===========================================

    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='#00BFFF', linewidth=2.5, label='→ FP₁ (ψ = 120°)'),
        Line2D([0], [0], color='#FF6B6B', linewidth=2.5, label='→ FP₂ (ψ = 240°)'),
        Line2D([0], [0], color='purple', linewidth=2.5, linestyle='--',
               label='Singlet axis'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=12,
              facecolor='white', edgecolor='gray', framealpha=0.95)

    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)
    ax.set_xlabel('x / R_stella', fontsize=13)
    ax.set_ylabel('z / R_stella', fontsize=13)
    ax.set_title('Phase Dynamics → Diagonal Slice View\n'
                 'Trajectories converge to singlet axis (color neutrality)',
                 fontsize=14, fontweight='bold', pad=15)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.25, linestyle='-', linewidth=0.5)
    ax.set_facecolor('#fafafa')

    plt.tight_layout()

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)
    path = output_dir / "diagonal_slice_phase_mapped.png"
    fig.savefig(path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {path}")
    plt.close()

    print("\nThis plot shows:")
    print("  • Phase trajectories from theorem 2.2.1")
    print("  • Mapped so they converge to the dark band (singlet axis)")
    print("  • Dark band = x + z = 0 line = color neutrality")
    print("  • Same viewing angle as diagonal_slice_basic.png")
    print("  • Blue trajectories → FP₁, Red trajectories → FP₂")


if __name__ == "__main__":
    main()
