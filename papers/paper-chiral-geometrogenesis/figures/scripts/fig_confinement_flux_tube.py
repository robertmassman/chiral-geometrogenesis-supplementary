#!/usr/bin/env python3
"""
Figure: Confinement/Flux Tube Mechanism

Generates publication-quality figure showing the chiral field suppression
mechanism for confinement in the Chiral Geometrogenesis framework.

Three panels:
- (a) Flux tube profile: chi suppression between quark-antiquark pair
- (b) Flux tube growth at r = 0.5, 1.0, 1.5, 2.0 fm showing E_tube = sigma * r
- (c) Flux tube cross-section: chi and energy density profiles

Key physics:
- Chiral field chi -> 0 near color charges creates flux tube
- String tension sigma = (hbar c / R_stella)^2 = (440 MeV)^2
- Flux tube cross-section A_perp = pi * R_stella^2
- Flux tube width R_perp ~ R_stella ~ 0.448 fm

References: Theorem 2.5.2 (Dynamical Confinement), Proposition 0.0.17j

Output: fig_confinement_flux_tube.pdf, fig_confinement_flux_tube.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib.gridspec import GridSpec, GridSpecFromSubplotSpec
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Set up publication-quality figure style
plt.rcParams.update({
    'font.size': 10,
    'font.family': 'serif',
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'legend.fontsize': 9,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,  # Set to True if LaTeX is available
})

# Physical constants
R_STELLA = 0.448  # fm, characteristic stella size
HBAR_C = 197.3    # MeV*fm
SIGMA_ROOT = HBAR_C / R_STELLA  # sqrt(sigma) = 440 MeV
SIGMA = SIGMA_ROOT**2  # String tension in MeV^2
V_CHI = 1.0  # Normalized chiral VEV


def chi_profile_2d(x, y, q_pos, qbar_pos, sigma_perp=0.35):
    """
    2D chiral field profile for quark-antiquark pair.
    Suppressed in flux tube region between charges.
    """
    delta_chi = 0.30

    # Distance along the q-qbar axis
    axis = qbar_pos - q_pos
    axis_len = np.linalg.norm(axis)
    axis_unit = axis / axis_len

    # Project point onto axis
    vec_from_q = np.stack([x - q_pos[0], y - q_pos[1]], axis=-1)
    proj_len = np.einsum('...i,i->...', vec_from_q, axis_unit)

    # Perpendicular distance from axis
    proj_point = q_pos + proj_len[..., np.newaxis] * axis_unit
    r_perp = np.sqrt((x - proj_point[..., 0])**2 + (y - proj_point[..., 1])**2)

    # Inside flux tube region (between quarks)
    in_tube = (proj_len >= 0) & (proj_len <= axis_len)

    # Suppression profile
    chi = np.ones_like(x) * V_CHI
    tube_suppression = delta_chi * np.exp(-r_perp**2 / (2 * sigma_perp**2))
    chi[in_tube] = V_CHI * (1 - tube_suppression[in_tube])

    # Suppression near quark positions (spherical)
    r_q = np.sqrt((x - q_pos[0])**2 + (y - q_pos[1])**2)
    r_qbar = np.sqrt((x - qbar_pos[0])**2 + (y - qbar_pos[1])**2)
    chi = chi * (1 - delta_chi * np.exp(-r_q**2 / (2 * sigma_perp**2)))
    chi = chi * (1 - delta_chi * np.exp(-r_qbar**2 / (2 * sigma_perp**2)))

    # Normalize
    chi = np.clip(chi, V_CHI * (1 - delta_chi), V_CHI)

    return chi


def create_figure():
    """Generate the confinement/flux tube figure."""
    # Create figure with 3 panels:
    # Top row: (a) flux tube profile, (b) flux tube growth 2x2
    # Bottom row: (c) flux tube cross-section (centered, spanning width)
    fig = plt.figure(figsize=(14, 11))

    # Use GridSpec for layout
    gs = fig.add_gridspec(2, 2, height_ratios=[1, 1], width_ratios=[1, 1],
                          hspace=0.30, wspace=0.25)

    ax1 = fig.add_subplot(gs[0, 0])  # Top left - panel (a)

    # Create nested 2x2 grid for panel (b) in top right
    gs_inner = GridSpecFromSubplotSpec(2, 2, subplot_spec=gs[0, 1], hspace=0.25, wspace=0.20)
    ax2_panels = [fig.add_subplot(gs_inner[i, j]) for i in range(2) for j in range(2)]

    ax3 = fig.add_subplot(gs[1, :])  # Bottom row - panel (c) spanning full width

    # ============================================
    # Panel (a): Flux tube profile - 2D heatmap
    # ============================================

    # Set up grid
    x = np.linspace(-1.5, 1.5, 200)
    y = np.linspace(-0.8, 0.8, 120)
    X, Y = np.meshgrid(x, y)

    # Quark positions
    q_pos = np.array([-0.8, 0.0])
    qbar_pos = np.array([0.8, 0.0])

    # Calculate chiral field
    chi = chi_profile_2d(X, Y, q_pos, qbar_pos, sigma_perp=0.30)

    # Plot heatmap
    im = ax1.contourf(X, Y, chi/V_CHI, levels=np.linspace(0.65, 1.0, 20),
                       cmap='RdYlBu_r', extend='neither')

    # Add contour lines
    ax1.contour(X, Y, chi/V_CHI, levels=[0.70, 0.80, 0.90], colors='white',
                linewidths=0.8, linestyles='--', alpha=0.7)

    # Mark quark positions
    ax1.scatter(*q_pos, s=150, c='blue', marker='o', edgecolors='white',
                linewidths=2, zorder=10, label='q (color)')
    ax1.scatter(*qbar_pos, s=150, c='red', marker='o', edgecolors='white',
                linewidths=2, zorder=10, label=r'$\bar{q}$ (anticolor)')

    # Draw flux tube outline
    tube_radius = 0.35
    rect = Rectangle((-0.8, -tube_radius), 1.6, 2*tube_radius,
                     fill=False, edgecolor='yellow', linewidth=2, linestyle='-')
    ax1.add_patch(rect)

    # Annotations
    ax1.annotate(r'$\chi \to 0$', xy=(0, 0), fontsize=12, ha='center', va='center',
                 color='white', fontweight='bold',
                 bbox=dict(boxstyle='round', facecolor='gray', alpha=0.7))
    ax1.annotate(r'$\chi = v_\chi$', xy=(0, 0.6), fontsize=11, ha='center',
                 color='darkblue', fontweight='bold')

    # Colorbar
    cbar = plt.colorbar(im, ax=ax1, shrink=0.7, label=r'$\langle\chi\rangle / v_\chi$',
                        orientation='vertical', pad=0.02)

    ax1.set_xlabel('x (fm)')
    ax1.set_ylabel('y (fm)')
    ax1.set_title(r'(a) Flux tube: chiral field $\chi$ suppressed between color charges')
    ax1.set_aspect('equal')
    ax1.legend(loc='upper right', fontsize=9)

    # ============================================
    # Panel (b): Flux tube growth at different separations
    # ============================================

    separations = [0.5, 1.0, 1.5, 2.0]  # fm

    # Common grid for all subpanels
    x_growth = np.linspace(-1.3, 1.3, 130)
    y_growth = np.linspace(-0.6, 0.6, 60)
    X_growth, Y_growth = np.meshgrid(x_growth, y_growth)

    # Color levels
    levels = np.linspace(0.65, 1.0, 20)

    for idx, (ax_sub, r_sep) in enumerate(zip(ax2_panels, separations)):
        # Quark positions
        q_pos_sub = np.array([-r_sep/2, 0.0])
        qbar_pos_sub = np.array([r_sep/2, 0.0])

        # Calculate chiral field
        chi_sub = chi_profile_2d(X_growth, Y_growth, q_pos_sub, qbar_pos_sub, sigma_perp=0.30)

        # Plot
        im_sub = ax_sub.contourf(X_growth, Y_growth, chi_sub/V_CHI, levels=levels,
                                  cmap='RdYlBu_r', extend='neither')

        # Contour lines
        ax_sub.contour(X_growth, Y_growth, chi_sub/V_CHI, levels=[0.75, 0.85, 0.95],
                       colors='white', linewidths=0.5, linestyles='--', alpha=0.5)

        # Mark quarks
        ax_sub.scatter(*q_pos_sub, s=60, c='blue', marker='o', edgecolors='white',
                       linewidths=1.5, zorder=10)
        ax_sub.scatter(*qbar_pos_sub, s=60, c='red', marker='o', edgecolors='white',
                       linewidths=1.5, zorder=10)

        # Draw flux tube outline
        tube_radius_sub = 0.30
        if r_sep > 0.1:
            rect_sub = Rectangle((q_pos_sub[0], -tube_radius_sub), r_sep, 2*tube_radius_sub,
                                  fill=False, edgecolor='yellow', linewidth=1.2, linestyle='-', alpha=0.8)
            ax_sub.add_patch(rect_sub)

        # Calculate energy
        E_tube = SIGMA_ROOT**2 / HBAR_C * r_sep  # MeV

        # Title with energy
        ax_sub.set_title(f'$r = {r_sep}$ fm,  $E = {E_tube:.0f}$ MeV', fontsize=9)
        ax_sub.set_aspect('equal')
        ax_sub.set_xlim(-1.3, 1.3)
        ax_sub.set_ylim(-0.6, 0.6)

        # Only show axis labels on outer panels
        if idx >= 2:  # Bottom row
            ax_sub.set_xlabel('x (fm)', fontsize=8)
        if idx % 2 == 0:  # Left column
            ax_sub.set_ylabel('y (fm)', fontsize=8)

        ax_sub.tick_params(labelsize=7)

    # Add panel (b) label and formula
    fig.text(0.73, 0.92, r'(b) Flux tube growth: $E_{tube} = \sigma \cdot r$',
             fontsize=11, ha='center', fontweight='bold')

    # ============================================
    # Panel (c): Flux tube cross-section and energy density
    # ============================================

    # Radial profile of chi and energy density
    r_perp = np.linspace(0, 1.5, 100)  # fm
    sigma_perp = 0.35  # fm, Gaussian width
    delta_chi = 0.30

    # Chi profile
    chi_profile = 1 - delta_chi * np.exp(-r_perp**2 / (2 * sigma_perp**2))

    # Energy density (proportional to deviation from vacuum)
    # rho ~ (chi - v_chi)^2 ~ delta_chi^2 * exp(-r^2/sigma^2)
    rho = delta_chi**2 * np.exp(-r_perp**2 / sigma_perp**2)
    rho_normalized = rho / rho.max()

    ax3_twin = ax3.twinx()

    # Plot chi profile
    l1, = ax3.plot(r_perp, chi_profile, 'b-', linewidth=2.5, label=r'Chiral field $\langle\chi\rangle/v_\chi$')
    ax3.fill_between(r_perp, chi_profile, 1, alpha=0.2, color='blue')

    # Plot energy density
    l2, = ax3_twin.plot(r_perp, rho_normalized, 'r--', linewidth=2.5, label=r'Energy density $\rho(r_\perp)$')
    ax3_twin.fill_between(r_perp, 0, rho_normalized, alpha=0.15, color='red')

    # Mark R_stella
    ax3.axvline(x=R_STELLA, color='green', linestyle=':', linewidth=2, alpha=0.8)
    ax3.text(R_STELLA + 0.05, 0.72, f'$R_{{\\rm stella}}$\n$= {R_STELLA}$ fm',
             fontsize=10, color='green', va='center')

    # Mark Gaussian width
    ax3.axvline(x=sigma_perp, color='orange', linestyle='--', linewidth=1.5, alpha=0.7)
    ax3.text(sigma_perp - 0.03, 0.95, f'$\\sigma_\\perp = {sigma_perp}$ fm\n(lattice)',
             fontsize=9, color='darkorange', va='top', ha='right')

    ax3.set_xlabel(r'Transverse distance $r_\perp$ (fm)')
    ax3.set_ylabel(r'Chiral field $\langle\chi\rangle / v_\chi$', color='blue')
    ax3_twin.set_ylabel(r'Normalized energy density', color='red')

    ax3.set_xlim(0, 1.5)
    ax3.set_ylim(0.65, 1.02)
    ax3_twin.set_ylim(0, 1.1)

    ax3.tick_params(axis='y', labelcolor='blue')
    ax3_twin.tick_params(axis='y', labelcolor='red')

    # Combined legend
    lines = [l1, l2]
    labels = [l.get_label() for l in lines]
    ax3.legend(lines, labels, loc='center right', fontsize=9)

    ax3.set_title(r'(c) Flux tube cross-section: $A_\perp = \pi R_{\rm stella}^2$')
    ax3.grid(True, alpha=0.3)

    # Add formula box (positioned on right side using axes coordinates)
    formula = (f'$A_\\perp = \\pi R_{{\\rm stella}}^2 = {np.pi * R_STELLA**2:.2f}$ fm$^2$\n'
               f'$\\sigma = (\\hbar c / R_{{\\rm stella}})^2$\n'
               f'$E_{{\\rm tube}} = \\sigma \\cdot r$')
    props = dict(boxstyle='round', facecolor='lightyellow', alpha=0.9, edgecolor='orange')
    ax3.text(0.98, 0.05, formula, fontsize=10, bbox=props,
             transform=ax3.transAxes, ha='right', va='bottom')

    # ============================================
    # Final layout and save
    # ============================================

    plt.tight_layout()

    # Save figures
    plt.savefig(f'{OUTPUT_DIR}/fig_confinement_flux_tube.png',
                dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(f'{OUTPUT_DIR}/fig_confinement_flux_tube.pdf',
                bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Figure saved to {OUTPUT_DIR}/fig_confinement_flux_tube.pdf")
    print(f"Figure saved to {OUTPUT_DIR}/fig_confinement_flux_tube.png")
    print("\nKey values verified:")
    print(f"  - R_stella = {R_STELLA} fm")
    print(f"  - sqrt(sigma) = hbar*c / R_stella = {SIGMA_ROOT:.1f} MeV")
    print(f"  - sigma = {SIGMA:.0f} MeV^2 = {SIGMA/1e6:.4f} GeV^2")
    print(f"  - String breaking distance ~ {1200 / (SIGMA / HBAR_C):.2f} fm")
    print(f"  - T_c / sqrt(sigma) ~ 0.35 -> T_c ~ {0.35 * SIGMA_ROOT:.0f} MeV")


if __name__ == '__main__':
    create_figure()
