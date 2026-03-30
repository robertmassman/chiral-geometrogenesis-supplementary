#!/usr/bin/env python3
"""
Figure: Wilson Loop Decay (Option 1)

Shows the exponential decay of Wilson loop expectation value with area,
comparing confining (area law) vs deconfining (perimeter law) behavior.

Key physics:
- Confining phase: <W(C)> ~ exp(-sigma * Area)
- Deconfined phase: <W(C)> ~ exp(-mu * Perimeter)
- The area law is the diagnostic criterion for confinement

References: Theorem 2.5.2, Wilson (1974)

Output: fig_wilson_loop_decay.pdf, fig_wilson_loop_decay.png
"""

import numpy as np
import matplotlib.pyplot as plt
import os

# Create output directory
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style
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
    'text.usetex': False,
})

# Physical constants
SIGMA = 0.194  # GeV^2, string tension
MU = 0.3  # GeV, perimeter coefficient for deconfined phase


def wilson_loop_area_law(R, T, sigma=SIGMA):
    """Wilson loop with area law: <W> = exp(-sigma * R * T)"""
    return np.exp(-sigma * R * T)


def wilson_loop_perimeter_law(R, T, mu=MU):
    """Wilson loop with perimeter law: <W> = exp(-mu * 2(R+T))"""
    return np.exp(-mu * 2 * (R + T))


def create_figure():
    """Generate the Wilson loop decay figure."""
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # ============================================
    # Panel (a): <W> vs Area for fixed aspect ratio
    # ============================================
    ax1 = axes[0]

    # For square loops (R = T), Area = R^2
    R_values = np.linspace(0.1, 2.5, 100)  # fm
    T_values = R_values  # Square loops
    Area = R_values * T_values  # fm^2

    # Convert to GeV units: 1 fm = 1/(0.197 GeV) => 1 fm^2 = 1/(0.197)^2 GeV^-2
    # sigma in GeV^2, Area in fm^2, need sigma*Area dimensionless
    # sigma = 0.194 GeV^2 = 0.194 / (hbar c)^2 fm^-2 = 0.194 / 0.0389 fm^-2 = 5.0 fm^-2
    sigma_fm = SIGMA / (0.197)**2  # Convert to fm^-2

    W_confined = np.exp(-sigma_fm * Area)
    W_deconfined = wilson_loop_perimeter_law(R_values, T_values, mu=0.5)

    ax1.semilogy(Area, W_confined, 'b-', linewidth=2.5, label=r'Confined: $e^{-\sigma \cdot RT}$ (area law)')
    ax1.semilogy(Area, W_deconfined, 'r--', linewidth=2.5, label=r'Deconfined: $e^{-\mu \cdot 2(R+T)}$ (perimeter)')

    # Shade regions
    ax1.fill_between(Area, W_confined, 1e-10, alpha=0.15, color='blue')

    # Add annotations
    ax1.annotate('Linear potential\n$V(r) = \\sigma r$',
                 xy=(5.2, 1e-9), fontsize=10, ha='center', color='darkblue',
                 bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.7))

    ax1.annotate('Coulomb-like\n$V(r) \\sim 1/r$',
                 xy=(5.2, 1e-4), fontsize=10, ha='center', color='darkred',
                 bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.7))

    ax1.set_xlabel(r'Loop Area $RT$ (fm$^2$)')
    ax1.set_ylabel(r'$\langle W(C) \rangle$')
    ax1.set_title(r'(a) Wilson loop decay: area vs perimeter law')
    ax1.set_xlim(0, 6)
    ax1.set_ylim(1e-12, 2)
    ax1.legend(loc='lower left', bbox_to_anchor=(0, 0))
    ax1.grid(True, alpha=0.3, which='both')

    # Add formula box - position in upper left area
    formula = (r'$\langle W(C) \rangle = \exp(-\sigma \cdot {\rm Area})$'
               '\n'
               r'$\sigma = 0.194$ GeV$^2$ = $(440$ MeV$)^2$')
    props = dict(boxstyle='round', facecolor='white', alpha=0.9, edgecolor='blue')
    ax1.text(0.15, 1e-9, formula, fontsize=10, va='bottom', bbox=props)

    # ============================================
    # Panel (b): <W> vs R for fixed T (time slice)
    # ============================================
    ax2 = axes[1]

    R = np.linspace(0, 2.0, 100)  # fm (spatial separation)
    T_fixed = [0.5, 1.0, 1.5, 2.0]  # fm (different time extents)
    colors = plt.cm.viridis(np.linspace(0.2, 0.8, len(T_fixed)))

    for T, color in zip(T_fixed, colors):
        Area = R * T
        W = np.exp(-sigma_fm * Area)
        ax2.semilogy(R, W, '-', linewidth=2, color=color,
                     label=f'$T = {T}$ fm')

    # Mark typical hadronic scale
    ax2.axvline(x=1.0, color='gray', linestyle=':', linewidth=1.5, alpha=0.7)
    ax2.text(1.05, 1e-6, r'$r \sim 1$ fm', fontsize=9, color='gray', rotation=90, va='center')

    ax2.set_xlabel(r'Spatial separation $R$ (fm)')
    ax2.set_ylabel(r'$\langle W(C) \rangle$')
    ax2.set_title(r'(b) Wilson loop vs separation (different $T$)')
    ax2.set_xlim(0, 2.0)
    ax2.set_ylim(1e-10, 2)
    ax2.legend(loc='lower left', title='Time extent', bbox_to_anchor=(0, 0))
    ax2.grid(True, alpha=0.3, which='both')

    # Add interpretation
    ax2.annotate('Faster decay at larger $T$\n$\\Rightarrow$ linear potential',
                 xy=(1.5, 3e-10), fontsize=10, ha='center',
                 bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    plt.tight_layout()

    # Save
    plt.savefig(f'{OUTPUT_DIR}/fig_wilson_loop_decay.png', dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(f'{OUTPUT_DIR}/fig_wilson_loop_decay.pdf', bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Figure saved to {OUTPUT_DIR}/fig_wilson_loop_decay.pdf")
    print(f"Figure saved to {OUTPUT_DIR}/fig_wilson_loop_decay.png")


if __name__ == '__main__':
    create_figure()
