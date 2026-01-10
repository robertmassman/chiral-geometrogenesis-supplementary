#!/usr/bin/env python3
"""
Unified Geometry Diagram with Singlet Axis Visualization
=========================================================

Two-panel figure showing:
1. Weight plane view (perpendicular to singlet axis) - singlet axis as ⊙ point
2. Diagonal slice view (along singlet axis) - singlet axis as visible line

The physical interpretation:
- The singlet axis is the [1,1,1] direction connecting the two tetrahedra apexes
- This is the "chiral axis" where the pressure-depression mechanism operates
- Time (λ) emerges along this axis from the persistent energy

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patheffects as path_effects
from matplotlib.patches import Polygon, Circle, FancyArrowPatch
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


def compute_energy_diagonal_slice(s, t, vertices_3d, sigma=0.5):
    """
    Compute energy density along the diagonal slice (x=y plane).

    Parameters:
        s: coordinate along the singlet axis [1,1,1]
        t: coordinate perpendicular to singlet axis (in the x=y plane)
        vertices_3d: list of 3D vertex positions
        sigma: Gaussian width
    """
    # The singlet axis direction
    singlet_dir = np.array([1, 1, 1]) / np.sqrt(3)

    # A perpendicular direction in the x=y plane: [1, 1, -2]/sqrt(6)
    perp_dir = np.array([1, 1, -2]) / np.sqrt(6)

    # Another perpendicular (for full 3D): [-1, 1, 0]/sqrt(2)
    # But we're in x=y plane, so we use a simpler parameterization

    # Position in 3D
    # For x=y plane: point = (s/sqrt(3))*[1,1,1] + (t/sqrt(2))*[1,1,-2]/sqrt(3)
    # Simplified: we parameterize by distance along singlet (s) and radial distance (t)

    # Actually, let's use a cleaner parameterization for the x=y diagonal:
    # x = y, so position is (x, x, z) where we vary x and z

    rho = 0
    for v in vertices_3d:
        # Distance from point to vertex
        # Point in 3D: we're showing a 2D slice, let's use (s, s, t) parameterization
        # where s is the x=y coordinate and t is z
        point = np.array([s, s, t])
        r2 = np.sum((point - v)**2)
        amplitude = np.exp(-r2 / (2 * sigma**2))
        rho += amplitude**2

    return rho


# ============================================================================
# PANEL 1: WEIGHT PLANE VIEW (singlet axis perpendicular - shows as point)
# ============================================================================

def create_weight_plane_panel(ax):
    """
    Create the weight plane view with singlet axis marked as ⊙.
    """
    scale = 0.6

    # Vertex positions (cube roots of unity scaled)
    theta_R, theta_G, theta_B = 0, 2*np.pi/3, 4*np.pi/3
    w_R = scale * np.array([np.cos(theta_R), np.sin(theta_R)])
    w_G = scale * np.array([np.cos(theta_G), np.sin(theta_G)])
    w_B = scale * np.array([np.cos(theta_B), np.sin(theta_B)])
    vertices = [w_R, w_G, w_B]

    # Anti-fundamental
    w_Rbar, w_Gbar, w_Bbar = -w_R, -w_G, -w_B

    # Background: Energy density field
    x_grid = np.linspace(-1.0, 1.0, 200)
    y_grid = np.linspace(-1.0, 1.0, 200)
    X, Y = np.meshgrid(x_grid, y_grid)

    rho_energy = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy[i, j] = compute_incoherent_energy(X[i, j], Y[i, j], vertices, sigma=0.32)

    im = ax.contourf(X, Y, rho_energy, levels=50, cmap='inferno', alpha=0.6, zorder=0)
    ax.contour(X, Y, rho_energy, levels=10, colors='white', alpha=0.15, linewidths=0.5, zorder=1)

    # Weight diagram triangles
    fund_tri = Polygon([w_R, w_G, w_B], fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)

    anti_tri = Polygon([w_Rbar, w_Gbar, w_Bbar], fill=False,
                       edgecolor='lightcoral', linewidth=3, linestyle='--', zorder=10)
    ax.add_patch(anti_tri)

    # Phase trajectories
    K = 1.0
    t_span = np.linspace(0, 50, 500)
    np.random.seed(123)
    n_traj = 15

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

        final_psi = solution[-1] % (2*np.pi)
        dist1 = np.linalg.norm(final_psi - np.array([2*np.pi/3, 2*np.pi/3]))
        dist2 = np.linalg.norm(final_psi - np.array([4*np.pi/3, 4*np.pi/3]))
        traj_color = '#00BFFF' if dist1 < dist2 else '#FF6B6B'

        for j in range(len(trajectory_x) - 1):
            alpha_val = 0.3 + 0.6 * (j / len(trajectory_x))
            ax.plot(trajectory_x[j:j+2], trajectory_y[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.5, zorder=15)

        if len(trajectory_x) > 10:
            ax.annotate('', xy=(trajectory_x[-1], trajectory_y[-1]),
                       xytext=(trajectory_x[-10], trajectory_y[-10]),
                       arrowprops=dict(arrowstyle='->', color=traj_color, lw=2, alpha=0.9),
                       zorder=16)

    # ===========================================
    # SINGLET AXIS SYMBOL (⊙) - replaces pulsing circles
    # ===========================================

    # Outer circle for ⊙ symbol
    singlet_circle = Circle((0, 0), 0.08, fill=False, edgecolor='white',
                            linewidth=3, zorder=20)
    ax.add_patch(singlet_circle)

    # Central dot for ⊙ symbol
    ax.scatter(0, 0, c='white', s=80, marker='o', zorder=21,
               edgecolor='none')

    # Label the singlet axis
    ax.annotate('Singlet Axis\n(⊙ into page)\nTime λ emerges here',
                (0.12, -0.05), fontsize=10, fontweight='bold',
                ha='left', va='top', color='white', zorder=25,
                bbox=dict(boxstyle='round,pad=0.3', facecolor='black', alpha=0.8,
                         edgecolor='gold', linewidth=2))

    # Vertex markers
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for w, c, l in zip(vertices, colors_fund, labels_fund):
        ax.scatter(*w, c=c, s=300, zorder=25, edgecolor='white', linewidth=2.5)
        direction = w / np.linalg.norm(w)
        ax.annotate(l, w + 0.10 * direction, fontsize=14, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='black')])

    colors_anti = ['#FF9999', '#99FF99', '#9999FF']
    labels_anti = ['R̄', 'Ḡ', 'B̄']
    for w, c, l in zip([w_Rbar, w_Gbar, w_Bbar], colors_anti, labels_anti):
        ax.scatter(*w, c=c, s=200, zorder=25, edgecolor='white', linewidth=2, marker='s')
        direction = w / np.linalg.norm(w)
        ax.annotate(l, w + 0.08 * direction, fontsize=11, color='white',
                   ha='center', va='center',
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Title and styling
    ax.set_title('Weight Plane View\n(Perpendicular to Singlet Axis)',
                 fontsize=14, fontweight='bold', pad=10, color='black')

    ax.set_xlim(-0.9, 0.9)
    ax.set_ylim(-0.9, 0.9)
    ax.set_xlabel('$T_3$ direction', fontsize=11)
    ax.set_ylabel('$Y$ direction', fontsize=11)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.2, color='white', linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='white', linewidth=0.8, alpha=0.4)
    ax.axvline(x=0, color='white', linewidth=0.8, alpha=0.4)
    ax.set_facecolor('#1a1a2e')

    return im


# ============================================================================
# PANEL 2: DIAGONAL SLICE VIEW (singlet axis visible as line)
# ============================================================================

def create_diagonal_slice_panel(ax):
    """
    Create the diagonal slice view showing the singlet axis as a visible line.
    This is similar to the 3rd panel of theorem_5_1_1_energy_distribution.
    """
    # Stella octangula vertices in 3D
    # Tetrahedron T+ (fundamental)
    T_plus = np.array([
        [1, 1, 1],      # W (apex - singlet)
        [1, -1, -1],    # R
        [-1, 1, -1],    # G
        [-1, -1, 1]     # B
    ]) / np.sqrt(3)  # Normalize to unit sphere

    # Tetrahedron T- (anti-fundamental)
    T_minus = np.array([
        [-1, -1, -1],   # W-bar (apex - singlet)
        [-1, 1, 1],     # R-bar
        [1, -1, 1],     # G-bar
        [1, 1, -1]      # B-bar
    ]) / np.sqrt(3)

    all_vertices = list(T_plus) + list(T_minus)

    # For the diagonal slice (x=y plane), we parameterize by:
    # - horizontal axis: x = y coordinate
    # - vertical axis: z coordinate

    n_grid = 150
    xy_range = np.linspace(-1.2, 1.2, n_grid)
    z_range = np.linspace(-1.2, 1.2, n_grid)
    XY, Z = np.meshgrid(xy_range, z_range)

    # Compute energy density
    sigma = 0.4
    rho = np.zeros_like(XY)

    for i in range(n_grid):
        for j in range(n_grid):
            xy_val = XY[i, j]
            z_val = Z[i, j]
            # Point in 3D: (xy, xy, z) - this is on the x=y plane
            point = np.array([xy_val, xy_val, z_val])

            energy = 0
            for v in all_vertices:
                r2 = np.sum((point - v)**2)
                amplitude = np.exp(-r2 / (2 * sigma**2))
                energy += amplitude**2
            rho[i, j] = energy

    # Plot energy density
    im = ax.contourf(XY, Z, np.log10(rho + 1e-10), levels=50, cmap='hot', zorder=0)
    ax.contour(XY, Z, np.log10(rho + 1e-10), levels=10, colors='white', alpha=0.15, linewidths=0.5, zorder=1)

    # ===========================================
    # SINGLET AXIS (visible as diagonal line)
    # ===========================================

    # The singlet axis connects W at (1,1,1)/√3 to W-bar at (-1,-1,-1)/√3
    # In the x=y plane, this projects to the line from (1/√3, 1/√3) to (-1/√3, -1/√3)
    # In our (xy, z) coordinates: from (1/√3, 1/√3) to (-1/√3, -1/√3)

    singlet_start = np.array([1, 1]) / np.sqrt(3)
    singlet_end = np.array([-1, -1]) / np.sqrt(3)

    # Draw singlet axis as a prominent line
    ax.plot([singlet_start[0], singlet_end[0]], [singlet_start[1], singlet_end[1]],
            color='gold', linewidth=4, linestyle='-', zorder=15, alpha=0.9)

    # Add arrows to show direction (time flow)
    mid_point = (singlet_start + singlet_end) / 2
    ax.annotate('', xy=mid_point + 0.15 * (singlet_end - singlet_start),
               xytext=mid_point - 0.15 * (singlet_end - singlet_start),
               arrowprops=dict(arrowstyle='<->', color='gold', lw=3),
               zorder=16)

    # Label the singlet axis
    ax.annotate('Singlet Axis\n(Chiral Axis)\nλ flows here',
                (0.15, 0.0), fontsize=11, fontweight='bold',
                ha='left', va='center', color='white', zorder=25,
                bbox=dict(boxstyle='round,pad=0.3', facecolor='black', alpha=0.8,
                         edgecolor='gold', linewidth=2),
                path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Mark the apex vertices (W and W-bar)
    ax.scatter(singlet_start[0], singlet_start[1], c='gold', s=200, marker='*',
               zorder=20, edgecolor='black', linewidth=1.5)
    ax.annotate('W', singlet_start + np.array([0.08, 0.08]), fontsize=12,
               fontweight='bold', color='gold',
               path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    ax.scatter(singlet_end[0], singlet_end[1], c='gold', s=200, marker='*',
               zorder=20, edgecolor='black', linewidth=1.5)
    ax.annotate('W̄', singlet_end + np.array([-0.12, -0.08]), fontsize=12,
               fontweight='bold', color='gold',
               path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Mark color vertices (projected onto x=y plane)
    # R at (1,-1,-1)/√3 projects to xy=(1-1)/2/√3=0, but we need proper projection
    # Let's mark approximate positions where vertices appear in this slice

    # The color vertices in T+ are at:
    # R: (1,-1,-1)/√3 - in x=y plane this is at xy=0, z=-1/√3
    # G: (-1,1,-1)/√3 - in x=y plane this is at xy=0, z=-1/√3
    # B: (-1,-1,1)/√3 - in x=y plane this is at xy=-1/√3, z=1/√3

    # Actually, R and G are NOT on the x=y plane. Let's mark where they're closest.
    # For this visualization, we'll mark the positions of maximum energy

    # Mark center (origin)
    ax.scatter(0, 0, c='cyan', s=150, marker='+', zorder=20, linewidth=3)

    # Title and styling
    ax.set_title('Diagonal Slice View (x=y plane)\nSinglet Axis Visible as Line',
                 fontsize=14, fontweight='bold', pad=10, color='black')

    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1.1)
    ax.set_xlabel('x = y coordinate (diagonal)', fontsize=11)
    ax.set_ylabel('z coordinate', fontsize=11)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.2, color='white', linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='white', linewidth=0.8, alpha=0.3)
    ax.axvline(x=0, color='white', linewidth=0.8, alpha=0.3)
    ax.set_facecolor('#1a1a2e')

    return im


# ============================================================================
# MAIN FIGURE
# ============================================================================

def create_dual_view_figure():
    """
    Create two-panel figure showing both views of the singlet axis.
    """
    fig, axes = plt.subplots(1, 2, figsize=(18, 8))

    # Panel 1: Weight plane view
    im1 = create_weight_plane_panel(axes[0])

    # Panel 2: Diagonal slice view
    im2 = create_diagonal_slice_panel(axes[1])

    # Add colorbars
    cbar1 = plt.colorbar(im1, ax=axes[0], fraction=0.046, pad=0.02, shrink=0.8)
    cbar1.set_label('Energy $\\rho$', fontsize=10)

    cbar2 = plt.colorbar(im2, ax=axes[1], fraction=0.046, pad=0.02, shrink=0.8)
    cbar2.set_label('log₁₀(Energy)', fontsize=10)

    # Main title
    fig.suptitle('Singlet Axis: The Chiral Direction Where Time Emerges',
                fontsize=18, fontweight='bold', y=0.98)

    # Subtitle explaining the connection
    fig.text(0.5, 0.02,
            'Left: Weight plane view — singlet axis pierces plane at ⊙ (perpendicular to page)\n'
            'Right: Diagonal slice — singlet axis visible as gold line connecting W and W̄ apexes',
            ha='center', fontsize=12, style='italic',
            bbox=dict(boxstyle='round,pad=0.4', facecolor='lightyellow', edgecolor='gold', alpha=0.9))

    plt.tight_layout(rect=[0, 0.06, 1, 0.95])

    return fig


def main():
    """Generate the dual-view singlet axis figure."""

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    print("Generating dual-view singlet axis diagram...")

    fig = create_dual_view_figure()
    path = output_dir / "unified_geometry_singlet_axis.png"
    fig.savefig(path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {path}")
    plt.close(fig)

    print("\nThe diagram shows:")
    print("  • Left panel: Weight plane view with ⊙ symbol marking singlet axis")
    print("  • Right panel: Diagonal slice with singlet axis as gold line")
    print("  • The singlet axis is the chiral direction where time λ emerges")
    print("  • W and W̄ are the apex vertices of the two tetrahedra")


if __name__ == "__main__":
    main()
