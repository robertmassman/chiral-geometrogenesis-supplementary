#!/usr/bin/env python3
"""
Visualization plots for Proposition 5.2.4b: Spin-2 Graviton from Stress-Energy Conservation

Generates four plots:
1. Yukawa vs Newtonian Potential - Why graviton must be massless
2. Gravitational Wave Polarizations - The 2 physical DOF visualized
3. Degree of Freedom by Dimension - Formula d(d-3)/2 across dimensions
4. Spin Exclusion Diagram - Why only spin-2 couples to T_μν

References:
- Proposition 5.2.4b (Spin-2 From Stress-Energy Conservation)
- Weinberg (1964, 1965) — Soft graviton theorems
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle, Ellipse
from matplotlib.collections import PatchCollection
import matplotlib.gridspec as gridspec
from pathlib import Path

# Style configuration
plt.rcParams.update({
    'font.size': 10,
    'axes.titlesize': 12,
    'axes.labelsize': 10,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'legend.fontsize': 9,
    'figure.titlesize': 14,
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# Physical constants
HBAR = 1.054571817e-34  # J·s
C = 2.99792458e8        # m/s
G_NEWTON = 6.67430e-11  # m³/(kg·s²)

# Output directory
OUTPUT_DIR = Path(__file__).parent.parent / "plots"
OUTPUT_DIR.mkdir(exist_ok=True)


def plot_yukawa_vs_newton():
    """
    Plot 1: Yukawa vs Newtonian Potential

    Shows how a massive mediator gives exponentially-decaying Yukawa potential,
    while observations require the 1/r Newtonian potential (massless mediator).
    """
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Left panel: Potential comparison
    ax1 = axes[0]

    r = np.linspace(0.1, 10, 500)  # Normalized distance (units of Compton wavelength)

    # Newtonian potential: Φ = -1/r (normalized)
    phi_newton = -1 / r

    # Yukawa potentials with different masses
    mass_params = [0.5, 1.0, 2.0]  # m * λ_compton values
    colors = ['#e74c3c', '#f39c12', '#9b59b6']

    ax1.plot(r, phi_newton, 'b-', linewidth=2.5, label='Newton: $-1/r$ (massless)', zorder=10)

    for m, color in zip(mass_params, colors):
        phi_yukawa = -np.exp(-m * r) / r
        ax1.plot(r, phi_yukawa, '--', color=color, linewidth=2,
                label=f'Yukawa: $m\\lambda = {m}$')

    ax1.set_xlabel('$r / \\lambda$ (distance in Compton wavelengths)')
    ax1.set_ylabel('$\\Phi(r) / \\Phi_0$ (normalized potential)')
    ax1.set_title('Gravitational Potential: Massive vs Massless Mediator')
    ax1.set_xlim(0, 10)
    ax1.set_ylim(-2, 0.1)
    ax1.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
    ax1.legend(loc='lower right')
    ax1.grid(True, alpha=0.3)

    # Add annotation
    ax1.annotate('Massive mediator:\nexponential suppression\nat large $r$',
                xy=(6, -0.15), fontsize=9, ha='center',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    # Right panel: Log scale to show exponential decay
    ax2 = axes[1]

    r_log = np.linspace(0.5, 20, 500)
    phi_newton_log = 1 / r_log  # |Φ|

    ax2.semilogy(r_log, phi_newton_log, 'b-', linewidth=2.5,
                 label='Newton: $|\\Phi| \\propto 1/r$')

    for m, color in zip(mass_params, colors):
        phi_yukawa_log = np.exp(-m * r_log) / r_log
        ax2.semilogy(r_log, phi_yukawa_log, '--', color=color, linewidth=2,
                    label=f'Yukawa: $m\\lambda = {m}$')

    ax2.set_xlabel('$r / \\lambda$ (distance in Compton wavelengths)')
    ax2.set_ylabel('$|\\Phi(r)| / \\Phi_0$ (log scale)')
    ax2.set_title('Exponential Suppression of Yukawa Potential')
    ax2.set_xlim(0, 20)
    ax2.set_ylim(1e-10, 10)
    ax2.legend(loc='upper right')
    ax2.grid(True, alpha=0.3, which='both')

    # Add observational constraint annotation
    ax2.annotate('LIGO bound:\n$m_g < 1.76 \\times 10^{-23}$ eV\n$\\lambda > 10^{16}$ m',
                xy=(14, 1e-3), fontsize=9, ha='center',
                bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.7))

    plt.tight_layout()

    # Save
    output_path = OUTPUT_DIR / "proposition_5_2_4b_yukawa_vs_newton.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")
    plt.close()


def plot_gravitational_wave_polarizations():
    """
    Plot 2: Gravitational Wave Polarizations

    Shows how the + and × polarizations deform a ring of test particles,
    visualizing the 2 physical degrees of freedom of the massless spin-2 graviton.
    """
    fig, axes = plt.subplots(2, 5, figsize=(14, 6))

    # Time/phase values for animation frames
    phases = np.linspace(0, 2*np.pi, 5, endpoint=False)

    # Initial circle of test particles
    n_particles = 24
    theta = np.linspace(0, 2*np.pi, n_particles, endpoint=False)
    x0 = np.cos(theta)
    y0 = np.sin(theta)

    amplitude = 0.3  # Strain amplitude (exaggerated for visualization)

    # Top row: Plus polarization
    for i, phase in enumerate(phases):
        ax = axes[0, i]

        # h+ polarization: stretches x, compresses y (and vice versa)
        h_plus = amplitude * np.cos(phase)
        x_plus = x0 * (1 + h_plus)
        y_plus = y0 * (1 - h_plus)

        # Draw deformed ring
        ax.fill(x_plus, y_plus, alpha=0.3, color='blue')
        ax.plot(np.append(x_plus, x_plus[0]), np.append(y_plus, y_plus[0]),
               'b-', linewidth=1.5)
        ax.scatter(x_plus, y_plus, c='blue', s=30, zorder=5)

        # Reference circle
        circle_ref = plt.Circle((0, 0), 1, fill=False, linestyle='--',
                                color='gray', alpha=0.5)
        ax.add_patch(circle_ref)

        ax.set_xlim(-1.6, 1.6)
        ax.set_ylim(-1.6, 1.6)
        ax.set_aspect('equal')
        ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
        ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)

        if i == 0:
            ax.set_ylabel('$h_+$ polarization', fontsize=11, fontweight='bold')
        ax.set_title(f'$\\omega t = {i}\\pi/2.5$', fontsize=9)
        ax.set_xticks([])
        ax.set_yticks([])

    # Bottom row: Cross polarization
    for i, phase in enumerate(phases):
        ax = axes[1, i]

        # h× polarization: shears at 45°
        h_cross = amplitude * np.cos(phase)
        # Rotation by 45° then stretch/compress then rotate back
        x_cross = x0 + h_cross * y0
        y_cross = y0 + h_cross * x0

        # Draw deformed ring
        ax.fill(x_cross, y_cross, alpha=0.3, color='red')
        ax.plot(np.append(x_cross, x_cross[0]), np.append(y_cross, y_cross[0]),
               'r-', linewidth=1.5)
        ax.scatter(x_cross, y_cross, c='red', s=30, zorder=5)

        # Reference circle
        circle_ref = plt.Circle((0, 0), 1, fill=False, linestyle='--',
                                color='gray', alpha=0.5)
        ax.add_patch(circle_ref)

        ax.set_xlim(-1.6, 1.6)
        ax.set_ylim(-1.6, 1.6)
        ax.set_aspect('equal')
        ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
        ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)

        if i == 0:
            ax.set_ylabel('$h_\\times$ polarization', fontsize=11, fontweight='bold')
        ax.set_xticks([])
        ax.set_yticks([])

    # Add overall title and annotations
    fig.suptitle('Gravitational Wave Polarizations: The 2 Physical DOF of Spin-2',
                fontsize=13, fontweight='bold', y=0.98)

    # Add text annotation
    fig.text(0.5, 0.02,
            'Wave propagating perpendicular to page (z-direction). '
            'Dashed circle = unperturbed. These are the only 2 independent modes.',
            ha='center', fontsize=10, style='italic')

    plt.tight_layout(rect=[0, 0.05, 1, 0.95])

    # Save
    output_path = OUTPUT_DIR / "proposition_5_2_4b_gw_polarizations.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")
    plt.close()


def plot_dof_by_dimension():
    """
    Plot 3: Degrees of Freedom by Dimension

    Shows the formula DOF = d(d-3)/2 for massless spin-2 fields,
    highlighting that D=4 gives exactly 2 polarizations.
    """
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Left panel: Bar chart of DOF
    ax1 = axes[0]

    dimensions = np.arange(3, 12)

    def dof_massless_spin2(d):
        return d * (d - 3) // 2

    def dof_symmetric_tensor(d):
        return d * (d + 1) // 2

    dof_physical = [dof_massless_spin2(d) for d in dimensions]
    dof_total = [dof_symmetric_tensor(d) for d in dimensions]
    dof_gauge = [d for d in dimensions]  # gauge freedom = d
    dof_constraint = [d for d in dimensions]  # harmonic constraint = d

    x = np.arange(len(dimensions))
    width = 0.6

    # Stacked bar showing breakdown
    bars1 = ax1.bar(x, dof_physical, width, label='Physical DOF', color='#2ecc71', zorder=3)
    bars2 = ax1.bar(x, dof_gauge, width, bottom=dof_physical,
                   label='Gauge redundancy ($\\xi^\\mu$)', color='#e74c3c', alpha=0.7, zorder=3)
    bars3 = ax1.bar(x, dof_constraint, width,
                   bottom=[p + g for p, g in zip(dof_physical, dof_gauge)],
                   label='Constraints ($\\partial_\\mu \\bar{h}^{\\mu\\nu}=0$)',
                   color='#3498db', alpha=0.7, zorder=3)

    # Mark d=4
    d4_idx = list(dimensions).index(4)
    ax1.bar(x[d4_idx], dof_physical[d4_idx], width, color='#27ae60',
           edgecolor='black', linewidth=2, zorder=4)

    ax1.set_xlabel('Spacetime Dimension $d$')
    ax1.set_ylabel('Degrees of Freedom')
    ax1.set_title('DOF Counting for Massless Spin-2 Field')
    ax1.set_xticks(x)
    ax1.set_xticklabels(dimensions)
    ax1.legend(loc='upper left')
    ax1.grid(True, alpha=0.3, axis='y')

    # Annotate d=4
    ax1.annotate('$d=4$: 2 DOF\n(observed!)',
                xy=(d4_idx, dof_physical[d4_idx] + 0.5),
                xytext=(d4_idx + 1.5, dof_physical[d4_idx] + 5),
                fontsize=10, ha='center',
                arrowprops=dict(arrowstyle='->', color='black'),
                bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.7))

    # Right panel: Formula visualization
    ax2 = axes[1]

    d_continuous = np.linspace(3, 11, 100)
    dof_continuous = d_continuous * (d_continuous - 3) / 2

    ax2.plot(d_continuous, dof_continuous, 'b-', linewidth=2,
            label='$\\mathrm{DOF} = \\frac{d(d-3)}{2}$')
    ax2.scatter(dimensions, dof_physical, s=100, c='#2ecc71',
               edgecolors='black', linewidths=1.5, zorder=5, label='Integer dimensions')

    # Highlight special cases
    special_dims = {3: ('d=3: No dynamics\n(topological)', 'left'),
                   4: ('d=4: 2 DOF\n(our universe)', 'right'),
                   5: ('d=5: 5 DOF', 'right'),
                   10: ('d=10: 35 DOF\n(string theory)', 'left')}

    for d, (text, align) in special_dims.items():
        if d in dimensions:
            idx = list(dimensions).index(d)
            offset = 0.3 if align == 'right' else -0.3
            ax2.annotate(text, xy=(d, dof_physical[idx]),
                        xytext=(d + offset, dof_physical[idx] + 3),
                        fontsize=8, ha=align,
                        arrowprops=dict(arrowstyle='->', color='gray', alpha=0.7))

    ax2.set_xlabel('Spacetime Dimension $d$')
    ax2.set_ylabel('Physical Degrees of Freedom')
    ax2.set_title('Formula: $\\mathrm{DOF} = \\frac{d(d-3)}{2}$')
    ax2.set_xlim(2.5, 11.5)
    ax2.set_ylim(-2, 40)
    ax2.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
    ax2.legend(loc='upper left')
    ax2.grid(True, alpha=0.3)

    # Add formula breakdown
    textstr = ('$h_{\\mu\\nu}$: $\\frac{d(d+1)}{2}$ components\n'
              '$-$ gauge: $d$ (from $\\xi^\\mu$)\n'
              '$-$ constraints: $d$\n'
              '$=$ physical: $\\frac{d(d-3)}{2}$')
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8)
    ax2.text(0.98, 0.55, textstr, transform=ax2.transAxes, fontsize=9,
            verticalalignment='top', horizontalalignment='right', bbox=props)

    plt.tight_layout()

    # Save
    output_path = OUTPUT_DIR / "proposition_5_2_4b_dof_dimension.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")
    plt.close()


def plot_spin_exclusion():
    """
    Plot 4: Spin Exclusion Diagram

    Visual summary of why spins 0, 1, 3/2, and ≥3 cannot couple to T_μν
    for long-range gravity. Only spin-2 works.
    """
    fig, ax = plt.subplots(figsize=(14, 8))
    ax.set_xlim(0, 14)
    ax.set_ylim(0, 10)
    ax.axis('off')

    # Title
    ax.text(7, 9.5, 'Why Spin-2 is Unique for Gravity',
           fontsize=16, fontweight='bold', ha='center')
    ax.text(7, 8.9, 'Coupling to conserved symmetric $T_{\\mu\\nu}$',
           fontsize=12, ha='center', style='italic')

    # Define box positions and content
    spins = [
        {'spin': '0', 'name': 'Scalar', 'x': 1.5, 'color': '#e74c3c',
         'couples': 'Trace $T^\\mu_\\mu$',
         'issue': 'Violates equivalence\nprinciple',
         'detail': 'Different gravity for\ndust vs. radiation'},
        {'spin': '1', 'name': 'Vector', 'x': 4.5, 'color': '#e67e22',
         'couples': 'Current $J^\\mu$',
         'issue': 'Wrong source type',
         'detail': 'Gravity couples to\nenergy, not charge'},
        {'spin': '3/2', 'name': 'Fermion', 'x': 7.5, 'color': '#9b59b6',
         'couples': 'Spinor current',
         'issue': 'Statistics mismatch',
         'detail': 'Cannot couple to\nbosonic $T_{\\mu\\nu}$'},
        {'spin': '2', 'name': 'Tensor', 'x': 10.5, 'color': '#27ae60',
         'couples': 'Full $T_{\\mu\\nu}$',
         'issue': None,
         'detail': 'GRAVITON'},
        {'spin': '≥3', 'name': 'Higher', 'x': 13, 'color': '#95a5a6',
         'couples': 'Higher tensors',
         'issue': 'No long-range force',
         'detail': '$\\mathcal{A}(p) \\sim p^j \\to 0$\nas $p \\to 0$'},
    ]

    box_width = 2.4
    box_height = 5.5
    y_base = 2.0

    for spin_data in spins:
        x = spin_data['x']
        color = spin_data['color']
        is_valid = spin_data['issue'] is None

        # Main box
        if is_valid:
            rect = FancyBboxPatch((x - box_width/2, y_base), box_width, box_height,
                                 boxstyle="round,pad=0.05,rounding_size=0.2",
                                 facecolor=color, edgecolor='black',
                                 linewidth=3, alpha=0.3)
            ax.add_patch(rect)
            # Add checkmark
            ax.text(x, y_base + box_height + 0.3, '✓', fontsize=24,
                   ha='center', va='bottom', color='green', fontweight='bold')
        else:
            rect = FancyBboxPatch((x - box_width/2, y_base), box_width, box_height,
                                 boxstyle="round,pad=0.05,rounding_size=0.2",
                                 facecolor=color, edgecolor='gray',
                                 linewidth=2, alpha=0.2)
            ax.add_patch(rect)
            # Add X mark
            ax.text(x, y_base + box_height + 0.3, '✗', fontsize=24,
                   ha='center', va='bottom', color='red', fontweight='bold')

        # Spin label (large)
        ax.text(x, y_base + box_height - 0.6, f"Spin {spin_data['spin']}",
               fontsize=14, ha='center', va='top', fontweight='bold')

        # Name
        ax.text(x, y_base + box_height - 1.3, spin_data['name'],
               fontsize=11, ha='center', va='top', style='italic')

        # Couples to
        ax.text(x, y_base + box_height - 2.2, 'Couples to:',
               fontsize=9, ha='center', va='top', color='gray')
        ax.text(x, y_base + box_height - 2.7, spin_data['couples'],
               fontsize=10, ha='center', va='top')

        # Issue or success
        if is_valid:
            ax.text(x, y_base + 1.5, spin_data['detail'],
                   fontsize=12, ha='center', va='center',
                   fontweight='bold', color='darkgreen')
        else:
            ax.text(x, y_base + 2.0, spin_data['issue'],
                   fontsize=10, ha='center', va='center', color='darkred')
            ax.text(x, y_base + 0.8, spin_data['detail'],
                   fontsize=9, ha='center', va='center', color='gray')

    # Bottom annotation: Weinberg's theorem
    textbox = ('Weinberg (1964, 1965): For any Lorentz-invariant QFT where a massless particle\n'
              'couples to conserved energy-momentum, that particle must be spin-2.')
    props = dict(boxstyle='round', facecolor='lightyellow', alpha=0.9, edgecolor='orange')
    ax.text(7, 0.5, textbox, fontsize=10, ha='center', va='bottom', bbox=props)

    plt.tight_layout()

    # Save
    output_path = OUTPUT_DIR / "proposition_5_2_4b_spin_exclusion.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")
    plt.close()


def create_combined_figure():
    """
    Create a combined 2x2 figure with all four plots.
    """
    fig = plt.figure(figsize=(16, 14))
    gs = gridspec.GridSpec(2, 2, figure=fig, hspace=0.3, wspace=0.25)

    # =========================================================================
    # Plot 1: Yukawa vs Newton (top-left)
    # =========================================================================
    ax1 = fig.add_subplot(gs[0, 0])

    r = np.linspace(0.1, 15, 500)
    phi_newton = -1 / r

    mass_params = [0.3, 0.6, 1.0]
    colors = ['#e74c3c', '#f39c12', '#9b59b6']

    ax1.plot(r, phi_newton, 'b-', linewidth=2.5, label='Newton: $-1/r$ (massless)', zorder=10)
    for m, color in zip(mass_params, colors):
        phi_yukawa = -np.exp(-m * r) / r
        ax1.plot(r, phi_yukawa, '--', color=color, linewidth=2, label=f'Yukawa: $m\\lambda = {m}$')

    ax1.set_xlabel('$r / \\lambda$ (Compton wavelengths)')
    ax1.set_ylabel('$\\Phi(r) / \\Phi_0$')
    ax1.set_title('(a) Massless Mediator Requirement', fontweight='bold')
    ax1.set_xlim(0, 15)
    ax1.set_ylim(-1.5, 0.1)
    ax1.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
    ax1.legend(loc='lower right', fontsize=8)
    ax1.grid(True, alpha=0.3)
    ax1.annotate('1/r observed\n→ massless graviton', xy=(10, -0.15), fontsize=9, ha='center',
                bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.7))

    # =========================================================================
    # Plot 2: GW Polarizations (top-right)
    # =========================================================================
    ax2_main = fig.add_subplot(gs[0, 1])
    ax2_main.axis('off')
    ax2_main.set_title('(b) Gravitational Wave Polarizations (2 DOF)', fontweight='bold')

    # Create subplots within this region
    inner_gs = gridspec.GridSpecFromSubplotSpec(2, 3, subplot_spec=gs[0, 1],
                                                 hspace=0.1, wspace=0.1)

    phases = [0, np.pi/2, np.pi]
    n_particles = 20
    theta = np.linspace(0, 2*np.pi, n_particles, endpoint=False)
    x0 = np.cos(theta)
    y0 = np.sin(theta)
    amplitude = 0.35

    for i, phase in enumerate(phases):
        # Plus polarization (top row)
        ax_plus = fig.add_subplot(inner_gs[0, i])
        h_plus = amplitude * np.cos(phase)
        x_plus = x0 * (1 + h_plus)
        y_plus = y0 * (1 - h_plus)

        ax_plus.fill(x_plus, y_plus, alpha=0.3, color='blue')
        ax_plus.plot(np.append(x_plus, x_plus[0]), np.append(y_plus, y_plus[0]), 'b-', lw=1.5)
        circle_ref = plt.Circle((0, 0), 1, fill=False, ls='--', color='gray', alpha=0.5)
        ax_plus.add_patch(circle_ref)
        ax_plus.set_xlim(-1.6, 1.6)
        ax_plus.set_ylim(-1.6, 1.6)
        ax_plus.set_aspect('equal')
        ax_plus.set_xticks([])
        ax_plus.set_yticks([])
        if i == 0:
            ax_plus.set_ylabel('$h_+$', fontsize=10)

        # Cross polarization (bottom row)
        ax_cross = fig.add_subplot(inner_gs[1, i])
        h_cross = amplitude * np.cos(phase)
        x_cross = x0 + h_cross * y0
        y_cross = y0 + h_cross * x0

        ax_cross.fill(x_cross, y_cross, alpha=0.3, color='red')
        ax_cross.plot(np.append(x_cross, x_cross[0]), np.append(y_cross, y_cross[0]), 'r-', lw=1.5)
        circle_ref = plt.Circle((0, 0), 1, fill=False, ls='--', color='gray', alpha=0.5)
        ax_cross.add_patch(circle_ref)
        ax_cross.set_xlim(-1.6, 1.6)
        ax_cross.set_ylim(-1.6, 1.6)
        ax_cross.set_aspect('equal')
        ax_cross.set_xticks([])
        ax_cross.set_yticks([])
        if i == 0:
            ax_cross.set_ylabel('$h_\\times$', fontsize=10)

    # =========================================================================
    # Plot 3: DOF by Dimension (bottom-left)
    # =========================================================================
    ax3 = fig.add_subplot(gs[1, 0])

    dimensions = np.arange(3, 12)
    dof_physical = [d * (d - 3) // 2 for d in dimensions]

    colors_bar = ['#27ae60' if d == 4 else '#3498db' for d in dimensions]
    bars = ax3.bar(dimensions, dof_physical, color=colors_bar, edgecolor='black', linewidth=1)

    ax3.set_xlabel('Spacetime Dimension $d$')
    ax3.set_ylabel('Physical DOF')
    ax3.set_title('(c) DOF Formula: $d(d-3)/2$', fontweight='bold')
    ax3.set_xticks(dimensions)
    ax3.grid(True, alpha=0.3, axis='y')

    # Highlight d=4
    ax3.annotate('$d=4$: 2 DOF\n(our universe)', xy=(4, 2), xytext=(5.5, 8),
                fontsize=9, ha='center',
                arrowprops=dict(arrowstyle='->', color='black'),
                bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.8))

    # Add values on bars
    for i, (d, dof) in enumerate(zip(dimensions, dof_physical)):
        ax3.text(d, dof + 0.5, str(dof), ha='center', va='bottom', fontsize=9)

    # =========================================================================
    # Plot 4: Spin Exclusion (bottom-right)
    # =========================================================================
    ax4 = fig.add_subplot(gs[1, 1])
    ax4.set_xlim(0, 10)
    ax4.set_ylim(0, 10)
    ax4.axis('off')
    ax4.set_title('(d) Spin Exclusion (Weinberg\'s Theorem)', fontweight='bold')

    spins_simple = [
        {'spin': '0', 'x': 1, 'valid': False, 'reason': 'Trace only'},
        {'spin': '1', 'x': 3, 'valid': False, 'reason': 'Vector $J^\\mu$'},
        {'spin': '3/2', 'x': 5, 'valid': False, 'reason': 'Fermion'},
        {'spin': '2', 'x': 7, 'valid': True, 'reason': 'GRAVITON'},
        {'spin': '≥3', 'x': 9, 'valid': False, 'reason': 'No range'},
    ]

    for s in spins_simple:
        x = s['x']
        y = 5
        color = '#27ae60' if s['valid'] else '#e74c3c'
        alpha = 0.8 if s['valid'] else 0.3

        circle = plt.Circle((x, y), 0.8, facecolor=color, edgecolor='black',
                            linewidth=2, alpha=alpha)
        ax4.add_patch(circle)

        ax4.text(x, y, f"s={s['spin']}", ha='center', va='center',
                fontsize=11, fontweight='bold')

        mark = '✓' if s['valid'] else '✗'
        mark_color = 'green' if s['valid'] else 'red'
        ax4.text(x, y + 1.3, mark, ha='center', va='center',
                fontsize=16, color=mark_color, fontweight='bold')

        ax4.text(x, y - 1.5, s['reason'], ha='center', va='top', fontsize=8)

    # Arrow pointing to spin-2
    ax4.annotate('Couples to\n$T_{\\mu\\nu}$', xy=(7, 6.3), xytext=(7, 8.5),
                fontsize=9, ha='center',
                arrowprops=dict(arrowstyle='->', color='green', lw=2))

    # Weinberg reference
    ax4.text(5, 1.5, 'Only spin-2 can consistently couple to\nconserved symmetric $T_{\\mu\\nu}$',
            ha='center', fontsize=9, style='italic',
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    # Overall title
    fig.suptitle('Proposition 5.2.4b: Spin-2 Graviton from Stress-Energy Conservation',
                fontsize=14, fontweight='bold', y=0.98)

    # Save
    output_path = OUTPUT_DIR / "proposition_5_2_4b_combined.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")
    plt.close()


def main():
    """Generate all plots for Proposition 5.2.4b."""
    print("="*60)
    print("Generating plots for Proposition 5.2.4b")
    print("Spin-2 Graviton from Stress-Energy Conservation")
    print("="*60)
    print()

    # Generate individual plots
    print("Generating individual plots...")
    plot_yukawa_vs_newton()
    plot_gravitational_wave_polarizations()
    plot_dof_by_dimension()
    plot_spin_exclusion()

    # Generate combined figure
    print("\nGenerating combined figure...")
    create_combined_figure()

    print("\n" + "="*60)
    print("All plots generated successfully!")
    print(f"Output directory: {OUTPUT_DIR}")
    print("="*60)


if __name__ == "__main__":
    main()
