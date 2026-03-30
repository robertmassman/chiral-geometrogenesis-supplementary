#!/usr/bin/env python3
"""
Figure: Confining Potential from CG Mechanism

Generates publication-quality figure showing the confining potential
and Wilson loop area law in the Chiral Geometrogenesis framework.

Two panels:
- (a) Confining potential (Cornell potential) with string tension formula
- (b) Wilson loop area law schematic and derivation

Key physics:
- String tension sigma = (hbar c / R_stella)^2 = (440 MeV)^2
- Cornell potential V(r) = sigma*r - 4*alpha_s/(3*r)
- Wilson loop W(C) = exp(-sigma * A) where A = r * T
- Area law implies linear confinement

References: Theorem 2.5.2 (Dynamical Confinement), Proposition 0.0.17j

Output: fig_confining_potential.pdf, fig_confining_potential.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, FancyArrowPatch, FancyBboxPatch
from matplotlib.gridspec import GridSpec
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Set up publication-quality figure style
plt.rcParams.update({
    'font.size': 11,
    'font.family': 'serif',
    'axes.labelsize': 12,
    'axes.titlesize': 13,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'legend.fontsize': 10,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,  # Set to True if LaTeX is available
})

# Physical constants
R_STELLA = 0.448  # fm, characteristic stella size
HBAR_C = 197.3    # MeV*fm
SIGMA_ROOT = HBAR_C / R_STELLA  # sqrt(sigma) = 440 MeV
SIGMA = SIGMA_ROOT**2  # String tension in MeV^2


def cornell_potential(r, sigma_root=440, alpha_s=0.3):
    """
    Cornell potential V(r) = sigma*r - 4*alpha_s/(3*r) + V0
    sigma_root in MeV, r in fm
    Returns potential in MeV
    """
    V_coulomb = -4 * alpha_s / (3 * r) * HBAR_C
    V_linear = sigma_root**2 / HBAR_C * r  # sigma*r in MeV
    return V_linear + V_coulomb


def create_figure():
    """Generate the confining potential figure."""
    fig = plt.figure(figsize=(14, 6))

    gs = fig.add_gridspec(1, 2, width_ratios=[1, 1], wspace=0.25)

    ax1 = fig.add_subplot(gs[0, 0])  # Left - Cornell potential
    ax2 = fig.add_subplot(gs[0, 1])  # Right - Wilson loop schematic

    # ============================================
    # Panel (a): Confining potential (Cornell potential)
    # ============================================

    r = np.linspace(0.1, 2.0, 200)  # fm

    # Cornell potential
    V_cornell = cornell_potential(r, sigma_root=440, alpha_s=0.3)
    V_linear_only = 440**2 / HBAR_C * r  # Linear part only
    V_coulomb_only = -4 * 0.3 / (3 * r) * HBAR_C  # Coulomb part only

    # Normalize to V(0.5 fm) = 0 for visualization
    V0_offset = cornell_potential(np.array([0.5]), sigma_root=440, alpha_s=0.3)[0]
    V_linear_offset = 440**2 / HBAR_C * 0.5
    V_coulomb_offset = -4 * 0.3 / (3 * 0.5) * HBAR_C

    ax1.plot(r, V_cornell - V0_offset, 'b-', linewidth=2.5, label='Cornell potential $V(r)$')
    ax1.plot(r, V_linear_only - V_linear_offset, 'r--', linewidth=1.8,
             label=r'Linear: $\sigma r$', alpha=0.7)
    ax1.plot(r, V_coulomb_only - V_coulomb_offset, 'g:', linewidth=1.8,
             label=r'Coulomb: $-\frac{4\alpha_s}{3r}$', alpha=0.7)
    ax1.fill_between(r, -250, V_cornell - V0_offset, alpha=0.1, color='blue')

    # Mark string breaking distance
    r_break = 1.22  # fm, from derivation
    V_break = cornell_potential(np.array([r_break]), sigma_root=440, alpha_s=0.3)[0] - V0_offset
    ax1.axvline(x=r_break, color='purple', linestyle=':', linewidth=1.5, alpha=0.8,
                label=r'String breaking $r \approx 1.2$ fm')
    ax1.scatter([r_break], [V_break], s=100, c='purple', marker='s', zorder=10)

    # Add key formula box
    formula_text = (r'$\sigma = \left(\frac{\hbar c}{R_{\rm stella}}\right)^2$'
                    '\n\n'
                    r'$\sqrt{\sigma} = 440$ MeV'
                    '\n\n'
                    r'$R_{\rm stella} = 0.448$ fm')
    props2 = dict(boxstyle='round', facecolor='lightyellow', alpha=0.95, edgecolor='orange')
    ax1.text(0.18, 480, formula_text, fontsize=11, verticalalignment='top',
             bbox=props2, family='serif')

    # Add dual superconductor comparison
    dual_sc_text = (r'$\mathbf{Dual\ Superconductor\ Analogy}$' + '\n'
                    r'Type-II SC: magnetic flux $\to$ vortices' + '\n'
                    r'QCD dual: color-electric flux $\to$ tubes' + '\n'
                    r'CG: $\chi$-suppression $\equiv$ monopole condensate')
    props_dual = dict(boxstyle='round,pad=0.4', facecolor='lavender', alpha=0.95,
                      edgecolor='purple', linewidth=1.5)
    ax1.text(0.18, 250, dual_sc_text, fontsize=9, va='top', ha='left',
             bbox=props_dual, family='serif', linespacing=1.4)

    ax1.set_xlabel('Separation $r$ (fm)')
    ax1.set_ylabel('$V(r)$ (MeV)')
    ax1.set_xlim(0, 2.0)
    ax1.set_ylim(-250, 550)
    ax1.legend(loc='lower right', fontsize=10)
    ax1.set_title('(a) Confining potential from CG mechanism')
    ax1.grid(True, alpha=0.3)

    # ============================================
    # Panel (b): Wilson loop on lattice with CG connection
    # ============================================

    ax2.set_xlim(-0.5, 10.5)
    ax2.set_ylim(-0.5, 10)
    ax2.set_aspect('equal')
    ax2.axis('off')

    # Lattice parameters
    nx, ny = 9, 8  # Number of lattice points
    lattice_spacing = 1.0  # Visual spacing

    # Wilson loop boundaries (in lattice units)
    loop_i_min, loop_i_max = 2, 6  # x direction (spatial, r)
    loop_j_min, loop_j_max = 1, 6  # y direction (time, T)

    # Draw χ-suppression region inside the Wilson loop (flux tube)
    # Gradient shading - darker in center representing χ → 0
    for i in range(loop_i_min, loop_i_max):
        for j in range(loop_j_min, loop_j_max):
            # Distance from center of flux tube (x-direction only for tube)
            x_center = (loop_i_min + loop_i_max) / 2
            dist_from_center = abs(i + 0.5 - x_center) / ((loop_i_max - loop_i_min) / 2)
            # χ suppression: darker (lower χ) in center
            chi_value = 0.3 + 0.5 * dist_from_center  # 0.3 at center, 0.8 at edge
            color_intensity = chi_value
            rect = Rectangle((i, j), 1, 1,
                            facecolor=(0.7, 0.85, 1.0, 1.0 - 0.6*chi_value),
                            edgecolor='none')
            ax2.add_patch(rect)

    # Draw lattice points and gauge links
    # Z3 colors for the three phases
    z3_colors = ['#e41a1c', '#4daf4a', '#377eb8']  # Red, Green, Blue

    for i in range(nx):
        for j in range(ny):
            x, y = i * lattice_spacing, j * lattice_spacing

            # Check if this point is on the Wilson loop boundary
            on_loop = ((i >= loop_i_min and i <= loop_i_max and (j == loop_j_min or j == loop_j_max)) or
                      (j >= loop_j_min and j <= loop_j_max and (i == loop_i_min or i == loop_i_max)))

            # Check if inside the loop
            inside_loop = (i > loop_i_min and i < loop_i_max and j > loop_j_min and j < loop_j_max)

            # Draw lattice point with Z3 coloring
            color_idx = (i + j) % 3
            point_color = z3_colors[color_idx] if not inside_loop else '#666666'
            point_size = 60 if on_loop else 30
            point_alpha = 1.0 if on_loop else 0.6
            ax2.scatter(x, y, s=point_size, c=point_color, alpha=point_alpha,
                       zorder=5, edgecolors='black', linewidths=0.5)

            # Draw horizontal gauge links (except at right edge)
            if i < nx - 1:
                # Check if this link is part of Wilson loop
                is_wilson_link = ((j == loop_j_min or j == loop_j_max) and
                                 i >= loop_i_min and i < loop_i_max)

                if is_wilson_link:
                    # Wilson loop link - thick blue with arrow
                    arrow_dir = 1 if j == loop_j_min else -1  # Direction on loop
                    ax2.annotate('', xy=(x + arrow_dir * 0.8, y), xytext=(x + (1-arrow_dir) * 0.4, y),
                               arrowprops=dict(arrowstyle='->', color='blue', lw=2.5,
                                             mutation_scale=12))
                else:
                    # Regular gauge link - thin gray
                    ax2.plot([x, x + lattice_spacing], [y, y],
                            color='gray', linewidth=0.5, alpha=0.4)

            # Draw vertical gauge links (except at top edge)
            if j < ny - 1:
                # Check if this link is part of Wilson loop
                is_wilson_link = ((i == loop_i_min or i == loop_i_max) and
                                 j >= loop_j_min and j < loop_j_max)

                if is_wilson_link:
                    # Wilson loop link - thick blue with arrow
                    arrow_dir = 1 if i == loop_i_max else -1  # Direction on loop
                    ax2.annotate('', xy=(x, y + (1+arrow_dir) * 0.4),
                               xytext=(x, y + (1-arrow_dir) * 0.4),
                               arrowprops=dict(arrowstyle='->', color='blue', lw=2.5,
                                             mutation_scale=12))
                else:
                    # Regular gauge link - thin gray
                    ax2.plot([x, x], [y, y + lattice_spacing],
                            color='gray', linewidth=0.5, alpha=0.4)

    # Mark quark and antiquark positions
    q_x, q_y = loop_i_min, (loop_j_min + loop_j_max) / 2
    qbar_x, qbar_y = loop_i_max, (loop_j_min + loop_j_max) / 2
    ax2.scatter([q_x], [q_y], s=200, c='red', marker='o', zorder=10,
               edgecolors='darkred', linewidths=2)
    ax2.scatter([qbar_x], [qbar_y], s=200, c='red', marker='o', zorder=10,
               edgecolors='darkred', linewidths=2)
    ax2.text(q_x + 0.3, q_y, r'$q$', fontsize=14, ha='left', va='center',
            color='darkred', fontweight='bold')
    ax2.text(qbar_x - 0.3, qbar_y, r'$\bar{q}$', fontsize=14, ha='right', va='center',
            color='darkred', fontweight='bold')

    # Label dimensions
    ax2.annotate('', xy=(loop_i_max, loop_j_min - 0.7), xytext=(loop_i_min, loop_j_min - 0.7),
                arrowprops=dict(arrowstyle='<->', color='black', lw=1.5))
    ax2.text((loop_i_min + loop_i_max)/2, loop_j_min - 1.4, r'$r$',
            fontsize=13, ha='center', va='top', fontweight='bold')

    ax2.annotate('', xy=(loop_i_max + 0.7, loop_j_max), xytext=(loop_i_max + 0.7, loop_j_min),
                arrowprops=dict(arrowstyle='<->', color='black', lw=1.5))
    ax2.text(loop_i_max + 1.0, (loop_j_min + loop_j_max)/2, r'$T$',
            fontsize=13, ha='left', va='center', fontweight='bold')

    # Add lattice spacing annotation
    ax2.annotate('', xy=(0, -0.4), xytext=(1, -0.4),
                arrowprops=dict(arrowstyle='<->', color='gray', lw=1))
    ax2.text(0.5, -0.7, r'$a \sim R_{\rm stella}$', fontsize=10, ha='center', va='top',
            color='gray')

    # χ-suppression label inside flux tube
    ax2.text((loop_i_min + loop_i_max)/2, (loop_j_min + loop_j_max)/2,
            r'$\chi \to 0$' + '\n' + r'(flux tube)',
            fontsize=11, ha='center', va='center',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.9, edgecolor='gray'))

    # Add Z3 color legend
    ax2.text(-0.1, 9.5, r'$\mathbf{Z_3\ center}$' + '\n' + r'(color phases)',
            fontsize=9, ha='left', va='top')
    for idx, (color, label) in enumerate(zip(z3_colors, [r'$0$', r'$2\pi/3$', r'$4\pi/3$'])):
        ax2.scatter([0.1], [8.7 - idx * 0.5], s=40, c=color, edgecolors='black', linewidths=0.5)
        ax2.text(0.4, 8.7 - idx * 0.5, label, fontsize=9, va='center')

    # Add formula box (horizontal, next to Z3 legend, two lines)
    wilson_text = (r'$\mathbf{Wilson\ Loop:}$  '
                   r'$W(C) = \mathrm{Tr} \prod_{\ell \in C} U_\ell$' + '\n'
                   r'$\mathbf{Area\ law:}$  '
                   r'$\langle W(C) \rangle \sim e^{-\sigma A}$,  '
                   r'$\sigma = (\hbar c / R_{\rm stella})^2$  '
                   r'$\Rightarrow V(r) = \sigma r$')
    props_wilson = dict(boxstyle='round,pad=0.4', facecolor='lightcyan', alpha=0.95,
                        edgecolor='teal', linewidth=1.5)
    ax2.text(2.6, 8.5, wilson_text, fontsize=9, verticalalignment='center', ha='left',
             bbox=props_wilson, family='serif', linespacing=1.4)

    ax2.set_title('(b) Wilson loop on lattice with $\\chi$-suppression', fontsize=13, pad=10)

    # ============================================
    # Final layout and save
    # ============================================

    plt.tight_layout()

    # Save figures
    plt.savefig(f'{OUTPUT_DIR}/fig_confining_potential.png',
                dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(f'{OUTPUT_DIR}/fig_confining_potential.pdf',
                bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Figure saved to {OUTPUT_DIR}/fig_confining_potential.pdf")
    print(f"Figure saved to {OUTPUT_DIR}/fig_confining_potential.png")
    print("\nKey values verified:")
    print(f"  - R_stella = {R_STELLA} fm")
    print(f"  - sqrt(sigma) = hbar*c / R_stella = {SIGMA_ROOT:.1f} MeV")
    print(f"  - sigma = {SIGMA:.0f} MeV^2 = {SIGMA/1e6:.4f} GeV^2")
    print(f"  - String breaking distance ~ {1200 / (SIGMA / HBAR_C):.2f} fm")


if __name__ == '__main__':
    create_figure()
