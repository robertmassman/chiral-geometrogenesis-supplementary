#!/usr/bin/env python3
"""
3D Combined Visualization for Theorem 0.2.1: Total Field from Superposition

Two-panel figure showing:
1. Combined 3D slice view - all three orthogonal planes in 3D space
2. 3D isosurface - surfaces of constant |χ_total|

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from skimage import measure
import os

# Set up plotting style
plt.style.use('seaborn-v0_8-whitegrid')

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05
A0 = 1.0

PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

EXP_PHASES = {
    'R': np.exp(1j * PHASES['R']),
    'G': np.exp(1j * PHASES['G']),
    'B': np.exp(1j * PHASES['B']),
}

# Stella octangula vertices - Tetrahedron T+
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

# Tetrahedron T-
VERTICES_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}

PLOTS_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'plots')


# =============================================================================
# CORE FUNCTIONS
# =============================================================================

def pressure_function_grid(X, Y, Z, x_c, epsilon=EPSILON):
    """Vectorized pressure function for grids."""
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field_grid(X, Y, Z, a0=A0, epsilon=EPSILON):
    """Vectorized total chiral field for grids."""
    total = np.zeros_like(X, dtype=complex)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def energy_density_grid(X, Y, Z, a0=A0, epsilon=EPSILON):
    """Vectorized energy density for grids."""
    total = np.zeros_like(X)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        total += P_c**2
    return a0**2 * total


def draw_stella_octangula(ax, alpha=0.15, scale=1.0):
    """Draw the stella octangula wireframe."""
    # T+ tetrahedron edges
    t_plus = [VERTICES_PLUS[k] * scale for k in ['R', 'G', 'B', 'W']]
    edges_plus = [
        (t_plus[0], t_plus[1]), (t_plus[0], t_plus[2]), (t_plus[0], t_plus[3]),
        (t_plus[1], t_plus[2]), (t_plus[1], t_plus[3]), (t_plus[2], t_plus[3]),
    ]

    # T- tetrahedron edges
    t_minus = [VERTICES_MINUS[k] * scale for k in ['R_bar', 'G_bar', 'B_bar', 'W_bar']]
    edges_minus = [
        (t_minus[0], t_minus[1]), (t_minus[0], t_minus[2]), (t_minus[0], t_minus[3]),
        (t_minus[1], t_minus[2]), (t_minus[1], t_minus[3]), (t_minus[2], t_minus[3]),
    ]

    for e in edges_plus:
        ax.plot3D(*zip(*e), 'b-', alpha=0.4, linewidth=1)
    for e in edges_minus:
        ax.plot3D(*zip(*e), 'r-', alpha=0.4, linewidth=1)

    # Mark color vertices
    colors_map = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'gray'}
    for name, v in VERTICES_PLUS.items():
        ax.scatter(*v * scale, c=colors_map[name], s=60, edgecolors='black', linewidths=0.5)


def plot_combined_3d_visualization():
    """
    Create a two-panel figure:
    1. Combined 3D slice view
    2. 3D isosurface
    """
    fig = plt.figure(figsize=(16, 7))

    # ==========================================================================
    # Panel 1: Combined 3D Slice View
    # ==========================================================================
    ax1 = fig.add_subplot(121, projection='3d')

    # Grid setup for slices
    n_points = 80
    extent = 0.7
    coords = np.linspace(-extent, extent, n_points)

    # Create meshgrids for each plane
    # z = 0 plane
    Xz, Yz = np.meshgrid(coords, coords)
    Zz = np.zeros_like(Xz)
    chi_z = total_chiral_field_grid(Xz, Yz, Zz)
    mag_z = np.abs(chi_z)

    # y = 0 plane
    Xy, Zy = np.meshgrid(coords, coords)
    Yy = np.zeros_like(Xy)
    chi_y = total_chiral_field_grid(Xy, Yy, Zy)
    mag_y = np.abs(chi_y)

    # x = 0 plane
    Yx, Zx = np.meshgrid(coords, coords)
    Xx = np.zeros_like(Yx)
    chi_x = total_chiral_field_grid(Xx, Yx, Zx)
    mag_x = np.abs(chi_x)

    # Normalize for consistent colormap
    vmax = max(mag_z.max(), mag_y.max(), mag_x.max())
    vmin = 0

    # Plot z = 0 plane (horizontal)
    ax1.plot_surface(Xz, Yz, Zz, facecolors=plt.cm.viridis((mag_z - vmin) / (vmax - vmin)),
                     alpha=0.7, shade=False, antialiased=True, rstride=2, cstride=2)

    # Plot y = 0 plane (vertical, front-back)
    ax1.plot_surface(Xy, Yy, Zy, facecolors=plt.cm.viridis((mag_y - vmin) / (vmax - vmin)),
                     alpha=0.7, shade=False, antialiased=True, rstride=2, cstride=2)

    # Plot x = 0 plane (vertical, left-right)
    ax1.plot_surface(Xx, Yx, Zx, facecolors=plt.cm.viridis((mag_x - vmin) / (vmax - vmin)),
                     alpha=0.7, shade=False, antialiased=True, rstride=2, cstride=2)

    # Draw stella octangula
    draw_stella_octangula(ax1, scale=1.0)

    # Mark origin
    ax1.scatter([0], [0], [0], c='white', s=100, marker='o', edgecolors='black', linewidths=2, zorder=10)

    # Add plane labels
    ax1.text(extent * 0.8, extent * 0.8, 0.05, 'z=0', fontsize=10, color='black')
    ax1.text(extent * 0.8, 0.05, extent * 0.8, 'y=0', fontsize=10, color='black')
    ax1.text(0.05, extent * 0.8, extent * 0.8, 'x=0', fontsize=10, color='black')

    ax1.set_xlabel('x')
    ax1.set_ylabel('y')
    ax1.set_zlabel('z')
    ax1.set_title('(a) Combined Orthogonal Slices\n|χ_total| on x=0, y=0, z=0 planes', fontsize=12)
    ax1.set_xlim(-extent, extent)
    ax1.set_ylim(-extent, extent)
    ax1.set_zlim(-extent, extent)

    # Set viewing angle
    ax1.view_init(elev=20, azim=45)

    # ==========================================================================
    # Panel 2: 3D Isosurface
    # ==========================================================================
    ax2 = fig.add_subplot(122, projection='3d')

    # Create 3D grid for isosurface
    n_iso = 60
    x_iso = np.linspace(-extent, extent, n_iso)
    y_iso = np.linspace(-extent, extent, n_iso)
    z_iso = np.linspace(-extent, extent, n_iso)
    X3d, Y3d, Z3d = np.meshgrid(x_iso, y_iso, z_iso, indexing='ij')

    # Compute |χ_total| on 3D grid
    chi_3d = total_chiral_field_grid(X3d, Y3d, Z3d)
    mag_3d = np.abs(chi_3d)

    # Define isosurface levels (multiple shells)
    iso_levels = [0.3 * vmax, 0.5 * vmax, 0.7 * vmax]
    colors = ['#2166ac', '#92c5de', '#f4a582']  # Blue to red
    alphas = [0.3, 0.4, 0.5]

    for level, color, alpha in zip(iso_levels, colors, alphas):
        try:
            # Use marching cubes to find isosurface
            verts, faces, _, _ = measure.marching_cubes(mag_3d, level=level)

            # Scale vertices to actual coordinates
            verts_scaled = np.zeros_like(verts)
            verts_scaled[:, 0] = x_iso[0] + verts[:, 0] * (x_iso[-1] - x_iso[0]) / (n_iso - 1)
            verts_scaled[:, 1] = y_iso[0] + verts[:, 1] * (y_iso[-1] - y_iso[0]) / (n_iso - 1)
            verts_scaled[:, 2] = z_iso[0] + verts[:, 2] * (z_iso[-1] - z_iso[0]) / (n_iso - 1)

            # Create mesh
            mesh = Poly3DCollection(verts_scaled[faces], alpha=alpha, linewidths=0.1)
            mesh.set_facecolor(color)
            mesh.set_edgecolor('gray')
            ax2.add_collection3d(mesh)
        except ValueError:
            # No surface at this level
            pass

    # Draw stella octangula
    draw_stella_octangula(ax2, scale=1.0)

    # Mark origin
    ax2.scatter([0], [0], [0], c='white', s=100, marker='o', edgecolors='black', linewidths=2, zorder=10)

    ax2.set_xlabel('x')
    ax2.set_ylabel('y')
    ax2.set_zlabel('z')
    ax2.set_title('(b) Isosurfaces of |χ_total|\nShells at 30%, 50%, 70% of max', fontsize=12)
    ax2.set_xlim(-extent, extent)
    ax2.set_ylim(-extent, extent)
    ax2.set_zlim(-extent, extent)

    # Set viewing angle
    ax2.view_init(elev=20, azim=45)

    # Add colorbar for reference
    sm = plt.cm.ScalarMappable(cmap='viridis', norm=plt.Normalize(vmin=vmin, vmax=vmax))
    sm.set_array([])
    cbar_ax = fig.add_axes([0.02, 0.15, 0.015, 0.7])
    cbar = fig.colorbar(sm, cax=cbar_ax)
    cbar.set_label('|χ_total|', fontsize=11)

    # Main title
    fig.suptitle('Theorem 0.2.1: Total Chiral Field 3D Structure\n'
                 'Field vanishes at origin (white dot) where three planes intersect',
                 fontsize=14, fontweight='bold', y=0.98)

    plt.tight_layout(rect=[0.04, 0, 1, 0.93])

    return fig


def plot_isosurface_only():
    """
    Create a single-panel figure showing only the 3D isosurface.
    """
    fig = plt.figure(figsize=(8, 7))
    ax = fig.add_subplot(111, projection='3d')

    extent = 0.7

    # Compute vmax from 2D slices (same as two-panel version)
    # This ensures the isosurface levels match
    n_points = 80
    coords = np.linspace(-extent, extent, n_points)
    Xz, Yz = np.meshgrid(coords, coords)
    Zz = np.zeros_like(Xz)
    chi_z = total_chiral_field_grid(Xz, Yz, Zz)
    mag_z = np.abs(chi_z)

    Xy, Zy = np.meshgrid(coords, coords)
    Yy = np.zeros_like(Xy)
    chi_y = total_chiral_field_grid(Xy, Yy, Zy)
    mag_y = np.abs(chi_y)

    Yx, Zx = np.meshgrid(coords, coords)
    Xx = np.zeros_like(Yx)
    chi_x = total_chiral_field_grid(Xx, Yx, Zx)
    mag_x = np.abs(chi_x)

    vmax = max(mag_z.max(), mag_y.max(), mag_x.max())

    # Create 3D grid for isosurface
    n_iso = 60
    x_iso = np.linspace(-extent, extent, n_iso)
    y_iso = np.linspace(-extent, extent, n_iso)
    z_iso = np.linspace(-extent, extent, n_iso)
    X3d, Y3d, Z3d = np.meshgrid(x_iso, y_iso, z_iso, indexing='ij')

    # Compute |χ_total| on 3D grid
    chi_3d = total_chiral_field_grid(X3d, Y3d, Z3d)
    mag_3d = np.abs(chi_3d)

    # Define isosurface levels (multiple shells) - using vmax from slices
    iso_levels = [0.3 * vmax, 0.5 * vmax, 0.7 * vmax]
    colors = ['#2166ac', '#92c5de', '#f4a582']  # Blue to red
    alphas = [0.3, 0.4, 0.5]
    level_names = ['30% level', '50% level', '70% level']

    for level, color, alpha in zip(iso_levels, colors, alphas):
        try:
            # Use marching cubes to find isosurface
            verts, faces, _, _ = measure.marching_cubes(mag_3d, level=level)

            # Scale vertices to actual coordinates
            verts_scaled = np.zeros_like(verts)
            verts_scaled[:, 0] = x_iso[0] + verts[:, 0] * (x_iso[-1] - x_iso[0]) / (n_iso - 1)
            verts_scaled[:, 1] = y_iso[0] + verts[:, 1] * (y_iso[-1] - y_iso[0]) / (n_iso - 1)
            verts_scaled[:, 2] = z_iso[0] + verts[:, 2] * (z_iso[-1] - z_iso[0]) / (n_iso - 1)

            # Create mesh
            mesh = Poly3DCollection(verts_scaled[faces], alpha=alpha, linewidths=0.1)
            mesh.set_facecolor(color)
            mesh.set_edgecolor('gray')
            ax.add_collection3d(mesh)
        except ValueError:
            # No surface at this level
            pass

    # Draw stella octangula
    draw_stella_octangula(ax, scale=1.0)

    # Mark origin
    ax.scatter([0], [0], [0], c='white', s=100, marker='o', edgecolors='black', linewidths=2, zorder=10)

    # Create legend using proxy artists
    from matplotlib.patches import Patch
    from matplotlib.lines import Line2D

    legend_elements = [
        # Isosurface levels
        Patch(facecolor='#2166ac', alpha=0.3, label='30% level'),
        Patch(facecolor='#92c5de', alpha=0.4, label='50% level'),
        Patch(facecolor='#f4a582', alpha=0.5, label='70% level'),
        # Vertices
        Line2D([0], [0], marker='o', color='w', markerfacecolor='red',
               markersize=8, markeredgecolor='black', label='R vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='green',
               markersize=8, markeredgecolor='black', label='G vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='blue',
               markersize=8, markeredgecolor='black', label='B vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='gray',
               markersize=8, markeredgecolor='black', label='W vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='white',
               markersize=8, markeredgecolor='black', label='Origin (χ=0)'),
    ]

    ax.legend(handles=legend_elements, loc='upper left', fontsize=9,
              framealpha=0.9, edgecolor='gray')

    ax.set_xlabel('x')
    ax.set_ylabel('y')
    ax.set_zlabel('z')
    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)
    ax.set_zlim(-extent, extent)

    # Set viewing angle - W vertex at (-1,-1,1)/sqrt(3) points toward camera
    # azim=225 looks from -x,-y direction; elev=25 looks slightly down
    ax.view_init(elev=25, azim=225)

    # Title
    ax.set_title('Isosurfaces of |χ_total|\nShells at 30%, 50%, 70% of max', fontsize=12)

    plt.tight_layout()

    return fig


def plot_isosurface_two_views():
    """
    Create a two-panel figure showing isosurfaces from two orientations:
    (a) W vertex toward camera (current view)
    (b) W vertex pointing straight up
    """
    from matplotlib.patches import Patch
    from matplotlib.lines import Line2D

    fig = plt.figure(figsize=(14, 6))

    extent = 0.7

    # Compute vmax from 2D slices
    n_points = 80
    coords = np.linspace(-extent, extent, n_points)
    Xz, Yz = np.meshgrid(coords, coords)
    Zz = np.zeros_like(Xz)
    mag_z = np.abs(total_chiral_field_grid(Xz, Yz, Zz))

    Xy, Zy = np.meshgrid(coords, coords)
    Yy = np.zeros_like(Xy)
    mag_y = np.abs(total_chiral_field_grid(Xy, Yy, Zy))

    Yx, Zx = np.meshgrid(coords, coords)
    Xx = np.zeros_like(Yx)
    mag_x = np.abs(total_chiral_field_grid(Xx, Yx, Zx))

    vmax = max(mag_z.max(), mag_y.max(), mag_x.max())

    # Create 3D grid for isosurface
    n_iso = 60
    x_iso = np.linspace(-extent, extent, n_iso)
    y_iso = np.linspace(-extent, extent, n_iso)
    z_iso = np.linspace(-extent, extent, n_iso)
    X3d, Y3d, Z3d = np.meshgrid(x_iso, y_iso, z_iso, indexing='ij')
    mag_3d = np.abs(total_chiral_field_grid(X3d, Y3d, Z3d))

    # Isosurface levels (including 10% outermost shell)
    iso_levels = [0.1 * vmax, 0.3 * vmax, 0.5 * vmax, 0.7 * vmax]
    colors = ['#053061', '#2166ac', '#92c5de', '#f4a582']  # Dark blue for 10%
    alphas = [0.2, 0.3, 0.4, 0.5]

    # Two views: (elev, azim, title)
    views = [
        (25, 225, '(a) W vertex toward viewer'),
        (-20, -136, '(b) View from below'),
    ]

    for idx, (elev, azim, title) in enumerate(views):
        ax = fig.add_subplot(1, 2, idx + 1, projection='3d')

        # Add isosurfaces
        for level, color, alpha in zip(iso_levels, colors, alphas):
            try:
                verts, faces, _, _ = measure.marching_cubes(mag_3d, level=level)
                verts_scaled = np.zeros_like(verts)
                verts_scaled[:, 0] = x_iso[0] + verts[:, 0] * (x_iso[-1] - x_iso[0]) / (n_iso - 1)
                verts_scaled[:, 1] = y_iso[0] + verts[:, 1] * (y_iso[-1] - y_iso[0]) / (n_iso - 1)
                verts_scaled[:, 2] = z_iso[0] + verts[:, 2] * (z_iso[-1] - z_iso[0]) / (n_iso - 1)

                mesh = Poly3DCollection(verts_scaled[faces], alpha=alpha, linewidths=0)
                mesh.set_facecolor(color)
                mesh.set_edgecolor('none')
                ax.add_collection3d(mesh)
            except ValueError:
                pass

        # Draw stella octangula
        draw_stella_octangula(ax, scale=1.0)

        # Mark origin
        ax.scatter([0], [0], [0], c='white', s=100, marker='o', edgecolors='black', linewidths=2, zorder=10)

        ax.set_xlabel('x')
        ax.set_ylabel('y')
        ax.set_zlabel('z')
        ax.set_xlim(-extent, extent)
        ax.set_ylim(-extent, extent)
        ax.set_zlim(-extent, extent)
        ax.view_init(elev=elev, azim=azim)
        ax.set_title(title, fontsize=12)

    # Add single legend for the figure
    legend_elements = [
        Patch(facecolor='#053061', alpha=0.2, label='10% level'),
        Patch(facecolor='#2166ac', alpha=0.3, label='30% level'),
        Patch(facecolor='#92c5de', alpha=0.4, label='50% level'),
        Patch(facecolor='#f4a582', alpha=0.5, label='70% level'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='red',
               markersize=8, markeredgecolor='black', label='R vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='green',
               markersize=8, markeredgecolor='black', label='G vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='blue',
               markersize=8, markeredgecolor='black', label='B vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='gray',
               markersize=8, markeredgecolor='black', label='W vertex'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='white',
               markersize=8, markeredgecolor='black', label='Origin (χ=0)'),
    ]

    fig.legend(handles=legend_elements, loc='center left', bbox_to_anchor=(0.01, 0.5),
               fontsize=9, framealpha=0.9, edgecolor='gray')

    fig.suptitle('Isosurfaces of |χ_total| - Two Orientations', fontsize=14, fontweight='bold')
    plt.tight_layout(rect=[0.1, 0, 1, 0.95])

    return fig


def main():
    """Main entry point."""
    print("=" * 70)
    print("Theorem 0.2.1: 3D Combined Visualization")
    print("=" * 70)

    # Ensure output directory exists
    os.makedirs(PLOTS_DIR, exist_ok=True)

    print("\nGenerating 3D combined visualization...")
    fig = plot_combined_3d_visualization()

    filepath = os.path.join(PLOTS_DIR, 'theorem_0_2_1_3d_combined.png')
    fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close(fig)
    print(f"Saved to {filepath}")

    print("\nGenerating isosurface-only figure...")
    fig2 = plot_isosurface_only()

    filepath2 = os.path.join(PLOTS_DIR, 'theorem_0_2_1_isosurface.png')
    fig2.savefig(filepath2, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close(fig2)
    print(f"Saved to {filepath2}")

    print("\nGenerating two-view isosurface figure...")
    fig3 = plot_isosurface_two_views()

    filepath3 = os.path.join(PLOTS_DIR, 'theorem_0_2_1_isosurface_two_views.png')
    fig3.savefig(filepath3, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close(fig3)
    print(f"Saved to {filepath3}")

    print("\nDone!")


if __name__ == "__main__":
    main()
