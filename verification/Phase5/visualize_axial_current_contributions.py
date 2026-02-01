#!/usr/bin/env python3
"""
Visualization: Current Flow from Phase Winding
===============================================

Shows how the chiral field phase θ winding in space creates
an axial current: J_5^μ(χ) = v_χ² ∂^μθ

- Phase (hue): winds around the vortex center
- Current magnitude (brightness): 1/r falloff, brighter near core

Reference: Theorem 5.3.1 (Torsion from Chiral Current)
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import hsv_to_rgb

plt.rcParams.update({
    'font.size': 12,
    'font.family': 'serif',
    'mathtext.fontset': 'cm',
})

def main():
    fig, ax = plt.subplots(figsize=(9, 8))

    # Create grid
    n = 600
    x = np.linspace(-2, 2, n)
    y = np.linspace(-2, 2, n)
    X, Y = np.meshgrid(x, y)
    R = np.sqrt(X**2 + Y**2)
    R[R == 0] = 1e-10  # Avoid division by zero

    # Phase field: vortex with winding number 1
    theta = np.arctan2(Y, X)  # Range: [-π, π]

    # Map phase to hue [0, 1]
    hue = (theta + np.pi) / (2 * np.pi)

    # Current magnitude |J| ∝ 1/r (capped for visualization)
    # Normalize to [0, 1] range for brightness
    r_min, r_max = 0.2, 2.0
    current_mag = 1.0 / np.clip(R, r_min, r_max)
    current_mag = (current_mag - 1/r_max) / (1/r_min - 1/r_max)  # Normalize to [0, 1]

    # Create HSV image: Hue = phase, Saturation decreases with current, Value = current magnitude
    # White (high current) = low saturation, high value
    # Black (low current) = any saturation, low value
    H = hue
    S = 1.0 - current_mag  # Low saturation near core (white), high saturation far (colored->black)
    V = current_mag  # White near core (V=1), black far (V=0)

    # Stack and convert to RGB
    HSV = np.stack([H, S, V], axis=-1)
    RGB = hsv_to_rgb(HSV)

    # Plot the combined image
    ax.imshow(RGB, extent=[-2, 2, -2, 2], origin='lower', aspect='equal')

    # Draw current streamlines with color that contrasts with background
    r_vals = [0.35, 0.6, 0.9, 1.25, 1.65, 1.95]
    for r in r_vals:
        phi = np.linspace(0, 2*np.pi, 200)
        cx = r * np.cos(phi)
        cy = r * np.sin(phi)
        # Color: dark near core (white bg), light far (dark bg)
        gray_val = 1.0 - (1.0 / np.clip(r, r_min, r_max) - 1/r_max) / (1/r_min - 1/r_max)
        line_color = (gray_val, gray_val, gray_val)
        lw = 1.2
        ax.plot(cx, cy, color=line_color, lw=lw, alpha=0.7)

        # Arrowheads
        for angle in [np.pi/4, 3*np.pi/4, 5*np.pi/4, 7*np.pi/4]:
            ax_pos = r * np.cos(angle)
            ay_pos = r * np.sin(angle)
            dx = -np.sin(angle) * 0.1
            dy = np.cos(angle) * 0.1
            ax.annotate('', xy=(ax_pos + dx, ay_pos + dy),
                       xytext=(ax_pos, ay_pos),
                       arrowprops=dict(arrowstyle='->', color=line_color,
                                      lw=lw, alpha=0.8, mutation_scale=9))

    # Vortex core (dark to contrast with white center)
    core = plt.Circle((0, 0), 0.08, color='#333333', zorder=5)
    ax.add_patch(core)

    # Styling
    ax.set_xlim(-2, 2)
    ax.set_ylim(-2, 2)
    ax.set_xlabel(r'$x$', fontsize=14)
    ax.set_ylabel(r'$y$', fontsize=14)

    # Title
    ax.set_title(r'$J_5^\mu = v_\chi^2\,\partial^\mu\theta$: Phase Winding Creates Current',
                 fontsize=14, pad=12)

    # Custom colorbars
    # Phase colorbar (hue)
    cax1 = fig.add_axes([0.92, 0.35, 0.02, 0.3])
    phase_gradient = np.linspace(0, 1, 256).reshape(256, 1)
    phase_rgb = hsv_to_rgb(np.stack([phase_gradient,
                                      np.ones_like(phase_gradient) * 0.85,
                                      np.ones_like(phase_gradient) * 0.85], axis=-1))
    cax1.imshow(phase_rgb, aspect='auto', origin='lower', extent=[0, 1, -np.pi, np.pi])
    cax1.set_xticks([])
    cax1.set_yticks([-np.pi, 0, np.pi])
    cax1.set_yticklabels([r'$-\pi$', r'$0$', r'$\pi$'])
    cax1.set_ylabel(r'Phase $\theta$', fontsize=11)
    cax1.yaxis.set_label_position('right')
    cax1.yaxis.tick_right()

    # Current magnitude colorbar (white to black)
    cax2 = fig.add_axes([0.92, 0.12, 0.02, 0.18])
    bright_gradient = np.linspace(0, 1, 256).reshape(256, 1)
    bright_rgb = np.stack([bright_gradient] * 3, axis=-1)  # 0=black, 1=white
    cax2.imshow(bright_rgb, aspect='auto', origin='lower', extent=[0, 1, 0, 1])
    cax2.set_xticks([])
    cax2.set_yticks([0, 1])
    cax2.set_yticklabels([r'$0$', r'$1/r$'])
    cax2.set_ylabel(r'$|J_5|$', fontsize=11)
    cax2.yaxis.set_label_position('right')
    cax2.yaxis.tick_right()

    plt.savefig('plots/axial_current_contributions.png', dpi=300,
                bbox_inches='tight', facecolor='white')
    plt.savefig('plots/axial_current_contributions.pdf',
                bbox_inches='tight', facecolor='white')

    print("Saved: plots/axial_current_contributions.png")
    print("Saved: plots/axial_current_contributions.pdf")
    plt.close()

if __name__ == '__main__':
    main()
