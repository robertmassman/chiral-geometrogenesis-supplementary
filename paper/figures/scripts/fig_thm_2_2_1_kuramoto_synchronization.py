#!/usr/bin/env python3
"""
Figure: Kuramoto Phase-Locked Oscillation (Theorem 2.2.1)

Visualizes the Sakaguchi-Kuramoto synchronization of three color field phases
to the 120° phase-locked configuration. Shows how arbitrary initial conditions
converge to the symmetric R→G→B arrangement that underlies color confinement.

Key physics:
- Three color fields (R, G, B) are coupled oscillators with frustration α = 2π/3
- The system naturally locks to 120° phase separation
- This configuration gives color neutrality: e^(iφ_R) + e^(iφ_G) + e^(iφ_B) = 0
- The phase-lock is a stable attractor (eigenvalues λ = -3K/2)

Proof Document: docs/proofs/Phase2/Theorem-2.2.1-Phase-Locked-Oscillation.md
Paper Section: Section 2.2 (Phase Dynamics)

Output: fig_thm_2_2_1_kuramoto_synchronization.pdf, fig_thm_2_2_1_kuramoto_synchronization.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, Wedge
from matplotlib.collections import LineCollection
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

# Color palette for RGB color fields
COLOR_R = '#E74C3C'  # Red
COLOR_G = '#27AE60'  # Green
COLOR_B = '#3498DB'  # Blue
COLOR_BG = '#1a1a2e'  # Dark background for contrast


def sakaguchi_kuramoto(phases, t, omega, K, alpha):
    """
    Sakaguchi-Kuramoto dynamics for N=3 oscillators.

    dφ_i/dt = ω + (K/2) Σ_{j≠i} sin(φ_j - φ_i - α)

    With α = 2π/3, the stable fixed point is 120° separation.
    """
    phi_R, phi_G, phi_B = phases

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

    return [dphi_R, dphi_G, dphi_B]


def draw_phasor(ax, angle, color, label, radius=0.85, head_width=0.08):
    """Draw a phasor arrow on the unit circle."""
    x = radius * np.cos(angle)
    y = radius * np.sin(angle)

    # Arrow from origin
    ax.annotate('', xy=(x, y), xytext=(0, 0),
                arrowprops=dict(arrowstyle='->', color=color, lw=3,
                              mutation_scale=20))

    # Label outside the dotted circle
    label_r = 1.22
    ax.text(label_r * np.cos(angle), label_r * np.sin(angle), label,
            ha='center', va='center', fontsize=12, fontweight='bold',
            color=color)


def draw_unit_circle(ax):
    """Draw the unit circle with angle markers."""
    circle = Circle((0, 0), 1.0, fill=False, color='gray', lw=1.5, ls='--', alpha=0.5)
    ax.add_patch(circle)

    # Tick marks at 0°, 120°, 240° (labels removed to avoid overlap with χ labels)
    for angle in [0, 2*np.pi/3, 4*np.pi/3]:
        ax.plot([0.95*np.cos(angle), 1.05*np.cos(angle)],
                [0.95*np.sin(angle), 1.05*np.sin(angle)],
                'gray', lw=1.5, alpha=0.6)


def create_figure():
    """
    Create the Kuramoto synchronization figure.

    Panel (a): Phasor diagram showing final 120° locked state with color neutrality
    Panel (b): Time evolution of phase differences converging to 2π/3
    """
    fig, axes = plt.subplots(1, 2, figsize=(10, 4.5))

    # Parameters from Theorem 2.2.1
    omega = 1.0   # Natural frequency
    K = 1.0       # Coupling strength
    alpha = 2 * np.pi / 3  # Frustration parameter (120°)

    # =========================================================
    # Panel (a): Phasor Diagram - The 120° Phase Lock
    # =========================================================
    ax1 = axes[0]
    ax1.set_facecolor('#f8f9fa')

    # Draw unit circle
    draw_unit_circle(ax1)

    # The equilibrium phases (from co-rotating frame)
    phi_R_eq = 0
    phi_G_eq = 2 * np.pi / 3
    phi_B_eq = 4 * np.pi / 3

    # Draw the three phasors at equilibrium
    draw_phasor(ax1, phi_R_eq, COLOR_R, r'$\chi_R$')
    draw_phasor(ax1, phi_G_eq, COLOR_G, r'$\chi_G$')
    draw_phasor(ax1, phi_B_eq, COLOR_B, r'$\chi_B$')

    # Show the 120° angles between them
    # Arc from R to G
    arc_angles = np.linspace(0, 2*np.pi/3, 30)
    arc_r = 0.35
    ax1.plot(arc_r * np.cos(arc_angles), arc_r * np.sin(arc_angles),
             color='gray', lw=1.5, alpha=0.6)
    ax1.text(0.42 * np.cos(np.pi/3), 0.42 * np.sin(np.pi/3), r'$\frac{2\pi}{3}$',
             ha='center', va='center', fontsize=10, color='gray')

    # Show color neutrality: sum of phasors = 0
    # Draw small vectors at center showing cancellation
    center_r = 0.15
    for phi, color in [(phi_R_eq, COLOR_R), (phi_G_eq, COLOR_G), (phi_B_eq, COLOR_B)]:
        ax1.arrow(0, 0, center_r*np.cos(phi), center_r*np.sin(phi),
                  head_width=0.03, head_length=0.02, fc=color, ec=color, alpha=0.4)

    # Central marker showing sum = 0
    ax1.plot(0, 0, 'ko', markersize=8, zorder=10)

    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.axis('off')
    ax1.set_title(r'(a) Phase-Locked Configuration: $\Delta\phi = 2\pi/3$' + '\n' +
                  r'$\sum_c e^{i\phi_c} = 0$ (color neutrality)',
                  fontsize=11, fontweight='bold', pad=10)

    # Add subtitle about stability
    ax1.text(0, -1.3, 'Stable attractor of Sakaguchi-Kuramoto dynamics',
             ha='center', va='top', fontsize=9, color='#555')

    # =========================================================
    # Panel (b): Convergence Dynamics
    # =========================================================
    ax2 = axes[1]

    # Time array
    t_span = np.linspace(0, 12, 500)

    # Multiple initial conditions to show convergence
    initial_conditions = [
        (0.0, 0.5, 1.0),        # Clustered
        (0.0, 1.5, 2.5),        # Spread out
        (0.0, 0.8, 3.5),        # Asymmetric
        (0.0, 2.0, 2.5),        # Different spread
    ]

    colors_traj = ['#e74c3c', '#3498db', '#9b59b6', '#e67e22']

    for idx, (phi_R0, phi_G0, phi_B0) in enumerate(initial_conditions):
        # Integrate the Sakaguchi-Kuramoto system
        solution = odeint(sakaguchi_kuramoto, [phi_R0, phi_G0, phi_B0],
                         t_span, args=(omega, K, alpha))

        # Compute phase differences (relative to R, mod 2π)
        psi1 = (solution[:, 1] - solution[:, 0]) % (2 * np.pi)  # G - R
        psi2 = (solution[:, 2] - solution[:, 1]) % (2 * np.pi)  # B - G

        # Handle wraparound for smooth plotting
        for i in range(1, len(psi1)):
            if psi1[i] - psi1[i-1] > np.pi:
                psi1[i:] -= 2 * np.pi
            elif psi1[i] - psi1[i-1] < -np.pi:
                psi1[i:] += 2 * np.pi
        for i in range(1, len(psi2)):
            if psi2[i] - psi2[i-1] > np.pi:
                psi2[i:] -= 2 * np.pi
            elif psi2[i] - psi2[i-1] < -np.pi:
                psi2[i:] += 2 * np.pi

        # Plot ψ₁ = φ_G - φ_R
        ax2.plot(t_span, np.degrees(psi1), color=colors_traj[idx], lw=1.8,
                 alpha=0.8, label=f'IC {idx+1}' if idx == 0 else '')
        # Plot ψ₂ = φ_B - φ_G (dashed)
        ax2.plot(t_span, np.degrees(psi2), color=colors_traj[idx], lw=1.8,
                 alpha=0.5, ls='--')

    # Equilibrium line at 120°
    ax2.axhline(120, color='#27ae60', lw=2.5, ls=':', label=r'Equilibrium (120°)', zorder=10)

    ax2.set_xlabel(r'Internal time $\lambda$', fontsize=11)
    ax2.set_ylabel(r'Phase difference (degrees)', fontsize=11)
    ax2.set_title(r'(b) Convergence to 120° Separation',
                  fontsize=11, fontweight='bold', pad=10)
    ax2.set_xlim(0, 12)
    ax2.set_ylim(0, 240)
    ax2.set_yticks([0, 60, 120, 180, 240])
    ax2.grid(True, alpha=0.3)

    # Custom legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='gray', lw=1.8, label=r'$\psi_1 = \phi_G - \phi_R$'),
        Line2D([0], [0], color='gray', lw=1.8, ls='--', label=r'$\psi_2 = \phi_B - \phi_G$'),
        Line2D([0], [0], color='#27ae60', lw=2.5, ls=':', label=r'Equilibrium (decay rate $\frac{3K}{2}$)'),
    ]
    ax2.legend(handles=legend_elements, loc='upper right', fontsize=8)

    plt.tight_layout()
    return fig


def main():
    """Generate and save the figure."""
    print("Generating Theorem 2.2.1 Kuramoto Synchronization figure...")

    fig = create_figure()

    # Save in both formats
    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_thm_2_2_1_kuramoto_synchronization.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"  ✓ Saved: {output_path}")

    plt.close('all')
    print("Done!")


if __name__ == '__main__':
    main()
