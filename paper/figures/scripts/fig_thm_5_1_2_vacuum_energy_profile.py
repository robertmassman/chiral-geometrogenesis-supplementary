#!/usr/bin/env python3
"""
Figure: Vacuum Energy Profile (Theorem 5.1.2)

Shows the position-dependent vacuum energy density ρ_vac(x) arising from
three-color field phase cancellation on the stella octangula.

Key physics:
- Three color fields χ_R, χ_G, χ_B with phases 0, 2π/3, 4π/3
- At center: equal pressures → phases cancel → v_χ(0) = 0 → ρ_vac(0) = 0
- Near center: ρ_vac ~ r⁴ (quartic suppression from phase cancellation)
- At color vertices: ρ_vac peaks due to single-field dominance

Proof Document: docs/proofs/Phase5/Theorem-5.1.2-Vacuum-Energy-Density.md
Paper Section: Section 5.1 (Vacuum Energy and Cosmological Constant)

Output: fig_thm_5_1_2_vacuum_energy_profile.pdf, fig_thm_5_1_2_vacuum_energy_profile.png
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.axes_grid1 import make_axes_locatable
from pathlib import Path

# Output directory (parent figures folder)
SCRIPT_DIR = Path(__file__).parent
OUTPUT_DIR = SCRIPT_DIR.parent
OUTPUT_DIR.mkdir(exist_ok=True)

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


# =============================================================================
# PHYSICS FUNCTIONS
# =============================================================================

def pressure_function(x, x_c, epsilon=0.01):
    """
    Pressure function P_c(x) = 1/(|x - x_c|² + ε²).

    This models the field amplitude from each color vertex.
    """
    if x.ndim == 1:
        r_sq = np.sum((x - x_c)**2)
    else:
        r_sq = np.sum((x - x_c)**2, axis=-1)
    return 1.0 / (r_sq + epsilon**2)


def compute_vev_squared(x, color_vertices, epsilon=0.01):
    """
    Compute v_χ²(x) from pressure functions using phase cancellation formula.

    v_χ² = (a₀²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]

    This vanishes when P_R = P_G = P_B (at the center where all vertices
    are equidistant).
    """
    if x.ndim == 1:
        P = np.array([pressure_function(x, x_c, epsilon) for x_c in color_vertices])
    else:
        P = np.array([pressure_function(x, x_c, epsilon) for x_c in color_vertices])
        P = P.T  # Shape: (N_points, 3)

    # VEV squared from pressure differences
    if P.ndim == 1:
        v_sq = 0.5 * ((P[0] - P[1])**2 + (P[1] - P[2])**2 + (P[2] - P[0])**2)
    else:
        v_sq = 0.5 * ((P[:, 0] - P[:, 1])**2 + (P[:, 1] - P[:, 2])**2 + (P[:, 2] - P[:, 0])**2)

    return v_sq


# =============================================================================
# FIGURE GENERATION
# =============================================================================

def create_figure():
    """
    Create 3-panel vacuum energy profile figure.

    Panel A: XY slice showing ρ_vac in the plane of the three color vertices
    Panel B: XZ slice showing ρ_vac perpendicular to the color plane
    Panel C: Radial profile showing ρ_vac ~ r⁴ scaling near center
    """
    fig = plt.figure(figsize=(16, 5))

    # Color vertex positions (equilateral triangle in xy-plane, normalized to unit distance)
    color_vertices = np.array([
        [1, 0, 0],
        [-0.5, np.sqrt(3)/2, 0],
        [-0.5, -np.sqrt(3)/2, 0]
    ])
    color_vertices = color_vertices / np.linalg.norm(color_vertices[0])
    epsilon = 0.01

    N = 200  # Grid resolution (higher for smoother gradients)

    # =========================================================================
    # Pre-compute both slices to determine shared color range
    # =========================================================================

    # XY slice (z=0 plane)
    x = np.linspace(-1.5, 1.5, N)
    y = np.linspace(-1.5, 1.5, N)
    X_xy, Y_xy = np.meshgrid(x, y)
    points_xy = np.stack([X_xy.ravel(), Y_xy.ravel(), np.zeros_like(X_xy.ravel())], axis=-1)
    v_sq_xy = compute_vev_squared(points_xy, color_vertices, epsilon)
    V_SQ_xy = v_sq_xy.reshape(N, N)
    RHO_xy = V_SQ_xy**2
    log_rho_xy = np.log10(RHO_xy + 1e-20)

    # XZ slice (y=0 plane)
    z = np.linspace(-1.5, 1.5, N)
    X_xz, Z_xz = np.meshgrid(x, z)
    points_xz = np.stack([X_xz.ravel(), np.zeros_like(X_xz.ravel()), Z_xz.ravel()], axis=-1)
    v_sq_xz = compute_vev_squared(points_xz, color_vertices, epsilon)
    V_SQ_xz = v_sq_xz.reshape(N, N)
    RHO_xz = V_SQ_xz**2
    log_rho_xz = np.log10(RHO_xz + 1e-20)

    # Shared color range for both panels
    vmin = min(log_rho_xy.min(), log_rho_xz.min())
    vmax = max(log_rho_xy.max(), log_rho_xz.max())

    # =========================================================================
    # Panel A: XY slice (z=0 plane)
    # =========================================================================
    ax1 = fig.add_subplot(131)

    # Plot with log scale using imshow for smooth gradients (no banding)
    im1 = ax1.imshow(log_rho_xy, extent=[-1.5, 1.5, -1.5, 1.5], origin='lower',
                     cmap='viridis', vmin=vmin, vmax=vmax, aspect='equal')

    # Colorbar with proper sizing
    divider1 = make_axes_locatable(ax1)
    cax1 = divider1.append_axes("right", size="5%", pad=0.08)
    cbar1 = plt.colorbar(im1, cax=cax1)
    cbar1.set_label(r'$\log_{10}(\rho_{\rm vac})$')

    # Mark color vertices
    colors = ['red', 'green', 'blue']
    labels = ['R', 'G', 'B']
    for i, (v, c, l) in enumerate(zip(color_vertices, colors, labels)):
        ax1.plot(v[0], v[1], 'o', color=c, markersize=12, markeredgecolor='white',
                 markeredgewidth=2, label=r'$\chi_{}$'.format(l))

    # Mark center
    ax1.plot(0, 0, '*', color='gold', markersize=20, markeredgecolor='black',
             markeredgewidth=1.5, label=r'Center ($\rho$=0)')

    ax1.set_xlabel('x')
    ax1.set_ylabel('y')
    ax1.set_title(r'(A) XY Slice: $\rho_{\rm vac}(x,y,0)$' + '\nLog Scale', fontweight='bold')
    ax1.legend(loc='upper right', fontsize=8, markerscale=0.7)

    # =========================================================================
    # Panel B: XZ slice (y=0 plane)
    # =========================================================================
    ax2 = fig.add_subplot(132)

    # Plot with consistent color range
    im2 = ax2.imshow(log_rho_xz, extent=[-1.5, 1.5, -1.5, 1.5], origin='lower',
                     cmap='viridis', vmin=vmin, vmax=vmax, aspect='equal')

    # Colorbar with proper sizing
    divider2 = make_axes_locatable(ax2)
    cax2 = divider2.append_axes("right", size="5%", pad=0.08)
    cbar2 = plt.colorbar(im2, cax=cax2)
    cbar2.set_label(r'$\log_{10}(\rho_{\rm vac})$')

    # Mark where color vertices intersect this plane (only χ_R at x=1, y=0)
    ax2.plot(color_vertices[0, 0], 0, 'o', color='red', markersize=12,
             markeredgecolor='white', markeredgewidth=2, label=r'$\chi_R$ (y=0)')

    # Mark center
    ax2.plot(0, 0, '*', color='gold', markersize=20, markeredgecolor='black',
             markeredgewidth=1.5, label=r'Center ($\rho$=0)')

    ax2.set_xlabel('x')
    ax2.set_ylabel('z')
    ax2.set_title(r'(B) XZ Slice: $\rho_{\rm vac}(x,0,z)$' + '\nLog Scale', fontweight='bold')
    ax2.legend(loc='upper right', fontsize=8, markerscale=0.7)

    # =========================================================================
    # Panel C: Radial profile
    # =========================================================================
    ax3 = fig.add_subplot(133)

    radii = np.linspace(0, 4.0, 400)
    rho_radial = []

    for r in radii:
        point = np.array([r, 0, 0])
        v_sq = compute_vev_squared(point, color_vertices, epsilon)
        rho_radial.append(max(0, v_sq)**2)

    ax3.semilogy(radii, rho_radial, 'b-', linewidth=2, label=r'$\rho_{\rm vac}(r)$')
    ax3.axvline(x=1.0, color='red', linestyle='--', alpha=0.7, label='Color vertex (r=1)')
    ax3.axhline(y=1e-10, color='gray', linestyle=':', alpha=0.5)

    ax3.set_xlabel('Radius r')
    ax3.set_ylabel(r'$\rho_{\rm vac}$ [arb. units]')
    ax3.set_title(r'(C) Radial Profile' + '\n' + r'$\rho_{\rm vac}(r) \sim r^4$ near center',
                  fontweight='bold')
    ax3.legend(fontsize=8)
    ax3.grid(True, alpha=0.3)
    ax3.set_xlim(0, 4.0)
    ax3.set_ylim(1e-15, 1e20)

    plt.tight_layout()
    return fig


def main():
    """Generate and save the vacuum energy profile figure."""
    print("=" * 60)
    print("Theorem 5.1.2: Vacuum Energy Profile Figure")
    print("=" * 60)

    fig = create_figure()

    # Save outputs
    png_path = OUTPUT_DIR / 'fig_thm_5_1_2_vacuum_energy_profile.png'
    pdf_path = OUTPUT_DIR / 'fig_thm_5_1_2_vacuum_energy_profile.pdf'

    fig.savefig(png_path, dpi=300, bbox_inches='tight', facecolor='white')
    print(f"Saved: {png_path}")

    fig.savefig(pdf_path, bbox_inches='tight', facecolor='white')
    print(f"Saved: {pdf_path}")

    plt.close('all')
    print("\nDone!")


if __name__ == '__main__':
    main()
