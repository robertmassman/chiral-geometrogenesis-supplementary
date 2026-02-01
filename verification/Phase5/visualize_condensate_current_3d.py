#!/usr/bin/env python3
"""
3D Visualization: Condensate Current and Particle Creation
===========================================================

Shows the chiral condensate phase θ as a 3D "spiral staircase" surface.

- The surface height represents the phase θ
- The vortex (spiral) topology creates a particle at the center
- The gradient (slope) represents the axial current J_5^μ = v_χ² ∂^μθ

Key insight: The same field configuration that creates current flow
(phase gradient) also allows particle creation (topological winding).

Reference: Theorem 5.3.1 (Torsion from Chiral Current)
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.colors import LinearSegmentedColormap
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Line3DCollection

plt.rcParams.update({
    'font.size': 11,
    'font.family': 'serif',
    'mathtext.fontset': 'cm',
})

def main():
    fig = plt.figure(figsize=(11, 9))
    ax = fig.add_subplot(111, projection='3d')

    # Create polar grid (avoid r=0 singularity)
    r = np.linspace(0.2, 2.0, 80)
    phi = np.linspace(0, 2 * np.pi, 150)
    R, PHI = np.meshgrid(r, phi)

    # Convert to Cartesian
    X = R * np.cos(PHI)
    Y = R * np.sin(PHI)

    # Phase field: θ = φ (azimuthal angle) - creates helical surface
    # This is a vortex with winding number 1
    THETA = PHI
    Z = THETA

    # Create colormap
    colors = [
        '#1a0533', '#4a148c', '#1565c0', '#00897b',
        '#7cb342', '#fdd835', '#fb8c00', '#e53935',
        '#ad1457', '#6a1b9a', '#1a0533'
    ]
    phase_cmap = LinearSegmentedColormap.from_list('phase', colors, N=256)

    # Normalize Z for coloring
    Z_norm = (Z - Z.min()) / (Z.max() - Z.min())

    # Plot the helical surface with some transparency
    surf = ax.plot_surface(X, Y, Z, facecolors=phase_cmap(Z_norm),
                           alpha=0.7, antialiased=True, shade=False)

    # =========================================================================
    # CURRENT FLOW ARROWS - Large and visible
    # =========================================================================
    # Current J ∝ ∇θ = (1/r) φ̂ (azimuthal direction)
    # On the helicoid, current flows along the spiral (tangent to circles, upward in z)

    arrow_positions = []
    arrow_directions = []

    r_vals = [0.5, 0.9, 1.4, 1.9]
    n_per_ring = 5

    for r_val in r_vals:
        for i in range(n_per_ring):
            phi_val = i * 2 * np.pi / n_per_ring + 0.3  # offset to avoid overlap

            # Position on surface
            x_pos = r_val * np.cos(phi_val)
            y_pos = r_val * np.sin(phi_val)
            z_pos = phi_val

            # Current direction: tangent to the spiral (azimuthal + upward)
            # ∇θ in azimuthal direction, but on surface this means moving along spiral
            scale = 0.4
            dx = -np.sin(phi_val) * scale
            dy = np.cos(phi_val) * scale
            dz = scale  # moving up the spiral

            arrow_positions.append([x_pos, y_pos, z_pos])
            arrow_directions.append([dx, dy, dz])

    # Draw arrows with high visibility
    for pos, dir in zip(arrow_positions, arrow_directions):
        ax.quiver(pos[0], pos[1], pos[2],
                  dir[0], dir[1], dir[2],
                  color='yellow', alpha=1.0,
                  arrow_length_ratio=0.4,
                  linewidth=3, zorder=100)

    # =========================================================================
    # PARTICLE LOCATION - The vortex core (topological defect)
    # =========================================================================
    # The particle exists at r=0, where the phase is undefined (singular)
    # This is shown as a thick red line along the z-axis

    z_core = np.linspace(-0.3, 2*np.pi + 0.3, 50)
    x_core = np.zeros_like(z_core)
    y_core = np.zeros_like(z_core)
    ax.plot(x_core, y_core, z_core, 'r-', linewidth=6,
            label='Particle (vortex core)', zorder=50)

    # Add spheres along the core to make it more visible
    for z_val in [0.5, np.pi, 2*np.pi - 0.5]:
        ax.scatter([0], [0], [z_val], color='red', s=200, zorder=100,
                   edgecolor='darkred', linewidth=2)

    # =========================================================================
    # Styling
    # =========================================================================
    ax.set_xlabel(r'$x$', fontsize=14, labelpad=8)
    ax.set_ylabel(r'$y$', fontsize=14, labelpad=8)
    ax.set_zlabel(r'Phase $\theta$', fontsize=14, labelpad=8)

    ax.set_zticks([0, np.pi, 2*np.pi])
    ax.set_zticklabels([r'$0$', r'$\pi$', r'$2\pi$'])

    ax.set_xlim(-2.2, 2.2)
    ax.set_ylim(-2.2, 2.2)
    ax.set_zlim(-0.3, 2*np.pi + 0.3)

    # Title
    ax.set_title(r'Chiral Condensate $\chi = v_\chi e^{i\theta}$: '
                 'Phase Winding, Current, and Particle',
                 fontsize=13, pad=15)

    # View angle
    ax.view_init(elev=20, azim=-50)

    # Legend / annotations
    ax.text2D(0.02, 0.98,
              'Spiral surface: Phase field θ(x,y)\n'
              'Yellow arrows: Current J₅ ∝ ∇θ\n'
              'Red core: Particle (topological defect)',
              transform=ax.transAxes, fontsize=11,
              verticalalignment='top',
              bbox=dict(boxstyle='round,pad=0.4', facecolor='white',
                       edgecolor='gray', alpha=0.95))

    # Add explanation at bottom
    ax.text2D(0.5, 0.02,
              'The phase cannot be smoothly defined at r=0 → topological defect → particle',
              transform=ax.transAxes, fontsize=10, ha='center',
              style='italic', color='#444444')

    plt.savefig('plots/condensate_current_3d.png', dpi=300,
                bbox_inches='tight', facecolor='white')
    plt.savefig('plots/condensate_current_3d.pdf',
                bbox_inches='tight', facecolor='white')

    print("Saved: plots/condensate_current_3d.png")
    print("Saved: plots/condensate_current_3d.pdf")
    plt.close()

if __name__ == '__main__':
    main()
