#!/usr/bin/env python3
"""
Figure: Flux Tube Growth with Separation (Option 4)

NOTE: This standalone figure is DEPRECATED. The flux tube growth visualization
is now included as panel (b) in fig_confinement_flux_tube.pdf.
This script is retained for reference but no longer generates output files.

Shows the chiral field profile for increasing q-qbar separations,
demonstrating the growing flux tube and linear energy cost.

Panels show r = 0.5, 1.0, 1.5, 2.0 fm with:
- Chi suppression visualization
- Energy accumulation in the tube

Key physics:
- Flux tube extends linearly with separation
- Energy E = sigma * r grows linearly
- This is the physical origin of confinement

References: Theorem 2.5.2, Iritani et al. (2015)

See: fig_confinement_flux_tube.py for the combined figure.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, FancyBboxPatch
from matplotlib.colors import LinearSegmentedColormap
import os

# Create output directory
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style
plt.rcParams.update({
    'font.size': 10,
    'font.family': 'serif',
    'axes.labelsize': 11,
    'axes.titlesize': 11,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'legend.fontsize': 9,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
})

# Physical constants
R_STELLA = 0.448  # fm
HBAR_C = 197.3    # MeV*fm
SIGMA_ROOT = HBAR_C / R_STELLA  # 440 MeV
V_CHI = 1.0


def chi_profile_2d(x, y, q_pos, qbar_pos, sigma_perp=0.30):
    """2D chiral field profile for quark-antiquark pair."""
    delta_chi = 0.30

    axis = qbar_pos - q_pos
    axis_len = np.linalg.norm(axis)
    if axis_len < 1e-6:
        # Quarks at same position
        r = np.sqrt((x - q_pos[0])**2 + (y - q_pos[1])**2)
        return V_CHI * (1 - delta_chi * np.exp(-r**2 / (2 * sigma_perp**2)))

    axis_unit = axis / axis_len

    vec_from_q = np.stack([x - q_pos[0], y - q_pos[1]], axis=-1)
    proj_len = np.einsum('...i,i->...', vec_from_q, axis_unit)

    proj_point = q_pos + proj_len[..., np.newaxis] * axis_unit
    r_perp = np.sqrt((x - proj_point[..., 0])**2 + (y - proj_point[..., 1])**2)

    in_tube = (proj_len >= 0) & (proj_len <= axis_len)

    chi = np.ones_like(x) * V_CHI
    tube_suppression = delta_chi * np.exp(-r_perp**2 / (2 * sigma_perp**2))
    chi[in_tube] = V_CHI * (1 - tube_suppression[in_tube])

    r_q = np.sqrt((x - q_pos[0])**2 + (y - q_pos[1])**2)
    r_qbar = np.sqrt((x - qbar_pos[0])**2 + (y - qbar_pos[1])**2)
    chi = chi * (1 - delta_chi * np.exp(-r_q**2 / (2 * sigma_perp**2)))
    chi = chi * (1 - delta_chi * np.exp(-r_qbar**2 / (2 * sigma_perp**2)))

    chi = np.clip(chi, V_CHI * (1 - delta_chi), V_CHI)
    return chi


def create_figure():
    """Generate the flux tube growth figure."""
    # Separations to show
    separations = [0.5, 1.0, 1.5, 2.0]  # fm

    fig, axes = plt.subplots(2, 2, figsize=(11, 8))
    axes = axes.flatten()

    # Common grid
    x = np.linspace(-1.5, 1.5, 150)
    y = np.linspace(-0.8, 0.8, 80)
    X, Y = np.meshgrid(x, y)

    # Color levels
    levels = np.linspace(0.65, 1.0, 20)

    for idx, (ax, r_sep) in enumerate(zip(axes, separations)):
        # Quark positions
        q_pos = np.array([-r_sep/2, 0.0])
        qbar_pos = np.array([r_sep/2, 0.0])

        # Calculate chiral field
        chi = chi_profile_2d(X, Y, q_pos, qbar_pos, sigma_perp=0.30)

        # Plot
        im = ax.contourf(X, Y, chi/V_CHI, levels=levels, cmap='RdYlBu_r', extend='neither')

        # Contour lines
        ax.contour(X, Y, chi/V_CHI, levels=[0.75, 0.85, 0.95], colors='white',
                   linewidths=0.6, linestyles='--', alpha=0.6)

        # Mark quarks
        ax.scatter(*q_pos, s=120, c='blue', marker='o', edgecolors='white', linewidths=2, zorder=10)
        ax.scatter(*qbar_pos, s=120, c='red', marker='o', edgecolors='white', linewidths=2, zorder=10)

        # Draw flux tube outline
        tube_radius = 0.35
        if r_sep > 0.1:
            rect = Rectangle((q_pos[0], -tube_radius), r_sep, 2*tube_radius,
                             fill=False, edgecolor='yellow', linewidth=1.5, linestyle='-', alpha=0.8)
            ax.add_patch(rect)

        # Calculate energy
        E_tube = SIGMA_ROOT**2 / HBAR_C * r_sep  # MeV

        # Labels
        ax.set_xlabel('x (fm)')
        ax.set_ylabel('y (fm)')
        panel_label = chr(ord('a') + idx)
        ax.set_title(f'({panel_label}) $r = {r_sep}$ fm,  $E_{{tube}} = {E_tube:.0f}$ MeV')
        ax.set_aspect('equal')
        ax.set_xlim(-1.5, 1.5)
        ax.set_ylim(-0.8, 0.8)

        # Add separation arrow
        arrow_y = -0.6
        ax.annotate('', xy=(qbar_pos[0], arrow_y), xytext=(q_pos[0], arrow_y),
                    arrowprops=dict(arrowstyle='<->', color='black', lw=1.5))
        ax.text(0, arrow_y - 0.12, f'$r = {r_sep}$ fm', ha='center', fontsize=9)

    # Add colorbar
    fig.subplots_adjust(right=0.88)
    cbar_ax = fig.add_axes([0.90, 0.15, 0.02, 0.7])
    cbar = fig.colorbar(im, cax=cbar_ax, label=r'$\langle\chi\rangle / v_\chi$')

    # Add overall title with physics summary
    fig.suptitle(r'Flux tube growth: $E_{tube} = \sigma \cdot r$ demonstrates linear confinement',
                 fontsize=13, y=0.98)

    plt.tight_layout(rect=[0, 0, 0.88, 0.95])

    # Save
    plt.savefig(f'{OUTPUT_DIR}/fig_flux_tube_growth.png', dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(f'{OUTPUT_DIR}/fig_flux_tube_growth.pdf', bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Figure saved to {OUTPUT_DIR}/fig_flux_tube_growth.pdf")
    print(f"Figure saved to {OUTPUT_DIR}/fig_flux_tube_growth.png")
    print("\nEnergy values:")
    for r in separations:
        E = SIGMA_ROOT**2 / HBAR_C * r
        print(f"  r = {r} fm: E_tube = {E:.0f} MeV")


if __name__ == '__main__':
    print("NOTE: This standalone figure is deprecated.")
    print("Flux tube growth is now included as panel (b) in fig_confinement_flux_tube.pdf")
    print("Run fig_confinement_flux_tube.py instead.")
    print()
    print("To generate the standalone figure anyway, uncomment the line below:")
    print("# create_figure()")
    # create_figure()  # Uncomment to generate standalone figure
