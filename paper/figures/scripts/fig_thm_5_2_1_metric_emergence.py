#!/usr/bin/env python3
"""
Figure: Metric Emergence Schematic (Theorem 5.2.1)

Shows how the spacetime metric emerges from the chiral field configuration:
- Panel (a): Energy density distribution from pressure functions creating gravitational potential
- Panel (b): Emergent metric components g_00 and g_rr deviating from flat space

Key physics:
- g_μν = η_μν + κ⟨T_μν⟩ + O(κ²) - metric perturbation from stress-energy
- Flat spacetime at center (Theorem 0.2.3) with quadratic deviations
- Time dilation from position-dependent oscillation frequency ω(x)
- Convergence via Banach fixed-point iteration

Proof Document: docs/proofs/Phase5/Theorem-5.2.1-Emergent-Metric.md
Paper Section: Section 12 (Emergent Spacetime and Gravity)

Output: fig_thm_5_2_1_metric_emergence.pdf, fig_thm_5_2_1_metric_emergence.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, FancyArrowPatch, Circle, Wedge
from matplotlib.collections import PatchCollection
import matplotlib.patheffects as path_effects
from mpl_toolkits.axes_grid1 import make_axes_locatable
import os


# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# Colors
COLOR_ENERGY = '#E74C3C'      # Red for energy density
COLOR_METRIC_00 = '#2980B9'   # Blue for g_00
COLOR_METRIC_RR = '#27AE60'   # Green for g_rr
COLOR_FLAT = '#7F8C8D'        # Gray for flat metric
COLOR_LIGHT_CONE = '#F39C12'  # Orange for light cones
COLOR_TIME = '#9B59B6'        # Purple for time direction
COLOR_SPACE = '#3498DB'       # Blue for space direction


def get_stella_vertices_3d():
    """
    Return the 3D vertex positions from Definition 0.1.3 §2.1.

    Tetrahedron T_+ vertices (normalized to unit distance from origin):
    x_R = (1, 1, 1)/√3
    x_G = (1, -1, -1)/√3
    x_B = (-1, 1, -1)/√3
    x_W = (-1, -1, 1)/√3
    """
    s = 1.0 / np.sqrt(3)
    return {
        'R': np.array([s, s, s]),
        'G': np.array([s, -s, -s]),
        'B': np.array([-s, s, -s]),
        'W': np.array([-s, -s, s])
    }


def project_to_plane_perp_to_W():
    """
    Project R, G, B vertices onto the plane perpendicular to the W-axis.
    This matches the visualization in theorem_3_0_3_geometry_overview.png panel B.

    Returns 2D coordinates (e1, e2) in the plane perpendicular to W.
    """
    vertices = get_stella_vertices_3d()

    # W direction (normalized)
    w_dir = vertices['W'] / np.linalg.norm(vertices['W'])

    # Construct orthonormal basis in the plane perpendicular to W
    # e1: perpendicular to W, choose to lie in plane containing W and z-axis
    # Use Gram-Schmidt starting from a vector not parallel to W
    temp = np.array([1, 0, 0])
    if np.abs(np.dot(temp, w_dir)) > 0.9:
        temp = np.array([0, 1, 0])
    e1 = temp - np.dot(temp, w_dir) * w_dir
    e1 = e1 / np.linalg.norm(e1)

    # e2: perpendicular to both W and e1
    e2 = np.cross(w_dir, e1)
    e2 = e2 / np.linalg.norm(e2)

    # Project each color vertex onto the (e1, e2) plane
    projected = {}
    for color in ['R', 'G', 'B']:
        v = vertices[color]
        projected[color] = (np.dot(v, e1), np.dot(v, e2))

    return projected, e1, e2


def pressure_function_3d(x, y, center_2d, z_offset, epsilon=0.5):
    """
    Pressure function P_c(x) from Definition 0.1.3 for 3D vertex.

    P_c(x) = 1/(|x - x_c|² + ε²)

    For 2D visualization, we compute the distance in 3D space where
    the observation point is at (x, y, 0) in the e1-e2-W coordinate system.
    The vertex is at (center_2d[0], center_2d[1], z_offset).
    """
    # Distance squared in 3D
    r_sq = (x - center_2d[0])**2 + (y - center_2d[1])**2 + z_offset**2
    return 1.0 / (r_sq + epsilon**2)


def energy_density(x, y, a0=1.0, epsilon=0.5):
    """
    Energy density from Theorem 0.2.1 §3.2:
    ρ(x) = a₀² Σ_c P_c(x)²

    Using proper 3D vertex positions projected onto plane ⊥ to W-axis.
    The observation plane is at z=0 in the (e1, e2, W) coordinate system.
    """
    vertices_3d = get_stella_vertices_3d()
    projected, e1, e2 = project_to_plane_perp_to_W()

    # W direction for computing z-offsets
    w_dir = vertices_3d['W'] / np.linalg.norm(vertices_3d['W'])

    rho = np.zeros_like(x)
    for color in ['R', 'G', 'B']:
        # 2D position in the observation plane
        center_2d = projected[color]

        # z-offset: component of vertex along W direction
        z_offset = np.dot(vertices_3d[color], w_dir)

        # Pressure function with 3D distance
        P = pressure_function_3d(x, y, center_2d, z_offset, epsilon)
        rho += a0**2 * P**2

    return rho, projected


def newtonian_potential(r, rho_0, R_eff, G=1.0):
    """
    Newtonian potential from Poisson equation.
    For uniform density sphere: Φ = -2πGρ₀r²/3 (inside)

    From Theorem 5.2.1 §5.3:
    Φ_N(r) ≈ -2πGρ₀r²/3 near center
    """
    return -2 * np.pi * G * rho_0 * r**2 / 3


def metric_g00(r, Phi_N, c=1.0):
    """
    g_00 component from Theorem 5.2.1 §5.1:
    g_00 = -(1 + 2Φ_N/c²)
    """
    return -(1 + 2 * Phi_N / c**2)


def metric_grr(r, Phi_N, c=1.0):
    """
    g_rr component from Theorem 5.2.1 §5.1:
    g_rr = 1 - 2Φ_N/c²
    """
    return 1 - 2 * Phi_N / c**2



def create_figure():
    """Create the two-panel metric emergence figure."""
    fig, axes = plt.subplots(1, 2, figsize=(9, 4), dpi=300)

    # =========================================================================
    # Panel (a): Energy Density Distribution (styled like theorem_3_0_3 panel B)
    # Using proper 3D vertex positions projected onto plane ⊥ to W-axis
    # =========================================================================
    ax1 = axes[0]

    # Create grid - tighter view to show peaks clearly
    x = np.linspace(-1.5, 1.5, 300)
    y = np.linspace(-1.5, 1.5, 300)
    X, Y = np.meshgrid(x, y)

    # Compute energy density with proper 3D geometry
    # epsilon = 0.35 for sharper peaks in visualization
    # (physical value is ~0.5 per Definition 0.1.3 §10.1)
    rho, projected_vertices = energy_density(X, Y, a0=1.0, epsilon=0.35)

    # Normalize for visualization
    rho_norm = rho / rho.max()

    # Plot energy density using imshow for cleaner look (like reference)
    im = ax1.imshow(rho_norm, extent=[-1.5, 1.5, -1.5, 1.5], origin='lower',
                    cmap='plasma', vmin=0, vmax=1, aspect='equal')

    # Mark the center (observation region) with a star
    ax1.scatter(0, 0, s=150, marker='*', c='white', edgecolors='black',
                linewidths=1, zorder=6)

    # Colorbar
    divider = make_axes_locatable(ax1)
    cax = divider.append_axes("right", size="5%", pad=0.08)
    cbar = plt.colorbar(im, cax=cax)
    cbar.set_label(r'$\rho / \rho_{max}$', fontsize=9)
    cbar.ax.tick_params(labelsize=8)

    # Add R, G, B labels at vertex positions (text only, no points)
    for color in ['R', 'G', 'B']:
        x_pos, y_pos = projected_vertices[color]
        ax1.text(x_pos, y_pos, color, fontsize=9, fontweight='bold',
                 color='black', ha='center', va='center')

    ax1.set_xlabel(r'$e_1$ direction', fontsize=10)
    ax1.set_ylabel(r'$e_2$ direction', fontsize=10)
    ax1.set_title(r'(a) Energy Density in Plane $\perp$ to W', fontsize=11, fontweight='bold')
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.tick_params(labelsize=9)

    # =========================================================================
    # Panel (b): Emergent Metric Components
    # =========================================================================
    ax2 = axes[1]

    # Radial coordinate
    r = np.linspace(0.01, 3.0, 200)

    # Physical parameters (dimensionless units)
    rho_0 = 1.0  # Central energy density
    c = 1.0
    G_eff = 0.1  # Effective gravitational coupling (weak field)

    # Newtonian potential
    Phi_N = newtonian_potential(r, rho_0, R_eff=1.0, G=G_eff)

    # Metric components
    g00 = metric_g00(r, Phi_N, c)
    grr = metric_grr(r, Phi_N, c)

    # Flat space values
    g00_flat = -np.ones_like(r)
    grr_flat = np.ones_like(r)

    # Plot
    ax2.plot(r, -g00, color=COLOR_METRIC_00, lw=2.5, label=r'$-g_{00}$ (time dilation)')
    ax2.plot(r, grr, color=COLOR_METRIC_RR, lw=2.5, label=r'$g_{rr}$ (spatial stretch)')
    ax2.axhline(1.0, color=COLOR_FLAT, lw=1.5, ls='--', label=r'Flat: $\eta_{\mu\nu}$', alpha=0.7)

    # Shade the deviation region (with legend entries)
    ax2.fill_between(r, -g00, 1.0, alpha=0.15, color=COLOR_METRIC_00,
                     label=r'$\Delta g_{00}$ deviation')
    ax2.fill_between(r, grr, 1.0, alpha=0.15, color=COLOR_METRIC_RR,
                     label=r'$\Delta g_{rr}$ deviation')

    # Mark the center region
    ax2.axvspan(0, 0.5, alpha=0.1, color='yellow', label='Center (nearly flat)')

    ax2.set_xlabel(r'$r / R_\chi$', fontsize=10)
    ax2.set_ylabel('Metric Component', fontsize=10)
    ax2.set_title(r'(b) Emergent Metric Components ($h_{\mu\nu} \propto r^2$)',
                  fontsize=11, fontweight='bold')
    ax2.set_xlim(0, 3.0)
    ax2.set_ylim(0.80, 1.20)
    ax2.legend(loc='upper right', fontsize=8)
    ax2.tick_params(labelsize=9)
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    # Save to parent figures directory
    pdf_path = os.path.join(OUTPUT_DIR, 'fig_thm_5_2_1_metric_emergence.pdf')
    png_path = os.path.join(OUTPUT_DIR, 'fig_thm_5_2_1_metric_emergence.png')

    fig.savefig(pdf_path, bbox_inches='tight', pad_inches=0.05, facecolor='white')
    fig.savefig(png_path, bbox_inches='tight', pad_inches=0.05, facecolor='white')

    print(f"Generated: {pdf_path}")
    print(f"Generated: {png_path}")

    plt.close('all')


if __name__ == '__main__':
    main()
