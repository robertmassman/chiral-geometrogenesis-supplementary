#!/usr/bin/env python3
"""
Figure: Born Rule Derivation via Ergodic Flow (Proposition 0.0.17a)

Visualizes how the Born rule P = |ψ|² emerges from ergodic geodesic flow
on the Cartan torus T² equipped with the Fisher metric.

Key physics:
- Phase trajectory fills the torus densely due to irrational frequency ratios
- Time-averaging eliminates off-diagonal cross-terms via Weyl equidistribution
- The surviving diagonal terms give |ψ_eff(x)|² = Σ_c P_c(x)²

Panel (a): Ergodic trajectory on T² - shows dense filling
Panel (b): Cross-term cancellation - phase averaging mechanism
Panel (c): Emergence of |ψ|² probability from time-averaged intensity

Proof Document: docs/proofs/foundations/Proposition-0.0.17a-Born-Rule-From-Geodesic-Flow.md
Paper Section: Part II - Emergent Quantum Structure (Proposition 5)

Output: fig_born_rule_ergodic_flow.pdf, fig_born_rule_ergodic_flow.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyBboxPatch, Arc
from matplotlib.lines import Line2D
from matplotlib.colors import LinearSegmentedColormap
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'serif',
    'font.serif': ['Times New Roman', 'DejaVu Serif'],
    'font.size': 11,
    'axes.labelsize': 12,
    'axes.titlesize': 13,
    'legend.fontsize': 10,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# Color palette
COLOR_RED = '#E74C3C'      # Red color field
COLOR_GREEN = '#27AE60'    # Green color field
COLOR_BLUE = '#3498DB'     # Blue color field
COLOR_TRAJECTORY = '#9B59B6'  # Purple for trajectory
COLOR_HIGHLIGHT = '#F39C12'   # Gold for highlights


def create_panel_a(ax):
    """
    Panel (a): Ergodic trajectory on the Cartan torus T².

    Shows how a geodesic with irrational frequency ratio fills the torus
    densely and uniformly over time.
    """
    # Background: probability distribution |χ_total|²
    n_grid = 150
    psi1_range = np.linspace(0, 2*np.pi, n_grid)
    psi2_range = np.linspace(0, 2*np.pi, n_grid)
    PSI1, PSI2 = np.meshgrid(psi1_range, psi2_range)

    # Total field: χ = exp(iφ_R) + exp(iφ_G) + exp(iφ_B)
    # With φ_R = 0, φ_G = ψ₁, φ_B = ψ₁ + ψ₂
    chi_total = 1 + np.exp(1j * PSI1) + np.exp(1j * (PSI1 + PSI2))
    P = np.abs(chi_total)**2 / 9  # Normalize to [0, 1]

    # Custom colormap: dark blue -> cyan -> yellow
    colors = ['#0a1628', '#1a3050', '#2a5070', '#3a7090',
              '#4a90b0', '#6ab0c0', '#8ad0d0', '#aae8e0']
    cmap = LinearSegmentedColormap.from_list('field_intensity', colors)

    im = ax.imshow(P, extent=[0, 360, 0, 360], origin='lower',
                   cmap=cmap, aspect='equal', alpha=0.6, vmin=0, vmax=1)

    # Generate ergodic trajectory with golden ratio for irrational slope
    phi = (1 + np.sqrt(5)) / 2  # Golden ratio ≈ 1.618
    v1 = 1.0  # Unit velocity in ψ₁ direction
    v2 = phi  # Golden ratio gives maximally irrational slope

    # Trajectory to show ergodic filling (fewer wraps for clarity)
    # Choose t_max so trajectory ends at ψ₁ ≈ 358° (near right edge)
    n_points = 5000
    target_psi1_end = 358 * np.pi / 180  # 358° in radians
    n_wraps = 5  # Fewer wraps for clearer visualization
    t_max = target_psi1_end - 0.3 + 2 * np.pi * n_wraps
    t = np.linspace(0, t_max, n_points)

    psi1 = (0.3 + v1 * t) % (2 * np.pi)
    psi2 = (0.5 + v2 * t) % (2 * np.pi)

    # Plot trajectory with fading alpha to show time progression
    n_segments = 100
    segment_size = n_points // n_segments

    for i in range(n_segments):
        start = i * segment_size
        end = min((i + 1) * segment_size + 1, n_points)
        alpha = 0.5 + 0.4 * (i / n_segments)  # Higher base alpha for visibility
        label = r'Geodesic trajectory $\phi(\tau)$' if i == n_segments - 1 else None
        ax.plot(np.degrees(psi1[start:end]), np.degrees(psi2[start:end]),
                color='black', linewidth=0.8, alpha=alpha, label=label)

    # Mark starting point
    ax.plot(np.degrees(0.3), np.degrees(0.5), 'o', color=COLOR_HIGHLIGHT,
            markersize=10, markeredgecolor='white', markeredgewidth=2, zorder=10,
            label=r'Starting point $\phi_0$')

    # Add arrow showing direction on a visible segment
    arrow_t = 0.5 * np.pi
    ax1 = np.degrees((0.3 + v1 * arrow_t) % (2 * np.pi))
    ay1 = np.degrees((0.5 + v2 * arrow_t) % (2 * np.pi))
    ax2 = np.degrees((0.3 + v1 * (arrow_t + 0.3)) % (2 * np.pi))
    ay2 = np.degrees((0.5 + v2 * (arrow_t + 0.3)) % (2 * np.pi))

    ax.annotate('', xy=(ax2, ay2), xytext=(ax1, ay1),
                arrowprops=dict(arrowstyle='->', color='black',
                               lw=2.5, mutation_scale=15), zorder=11)

    ax.set_xlabel(r'$\psi_1 = \phi_G - \phi_R$ (degrees)')
    ax.set_ylabel(r'$\psi_2 = \phi_B - \phi_G$ (degrees)')
    ax.set_xlim(0, 360)
    ax.set_ylim(0, 360)
    ax.set_xticks([0, 90, 180, 270, 360])
    ax.set_yticks([0, 90, 180, 270, 360])
    ax.set_aspect('equal')
    ax.grid(True, color='white', alpha=0.5, linestyle='-', linewidth=0.6)

    # Legend
    ax.legend(loc='lower right', fontsize=9, framealpha=0.95)

    # Title with key result
    ax.set_title(r'(a) Ergodic Flow on Cartan Torus $\mathbb{T}^2$',
                 fontsize=13, fontweight='bold', pad=10)

    # Annotation for irrational slope
    ax.text(180, 330, r'Slope $v_2/v_1 = \varphi$ (golden ratio)',
            fontsize=10, ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='white',
                     edgecolor='gray', alpha=0.9))


def create_panel_b(ax):
    """
    Panel (b): Cross-term cancellation via phase averaging.

    Shows how off-diagonal terms e^{i(φ_c - φ_c')} average to zero
    while diagonal terms (c = c') survive.
    """
    # Time axis
    T_max = 4  # In units of 2π
    t = np.linspace(0, T_max * 2 * np.pi, 2000)

    # Frequencies (with irrational ratios)
    omega_diff_RG = 1.0        # ω_G - ω_R = v₁
    omega_diff_GB = 0.618      # ω_B - ω_G ≈ v₂ - v₁ (golden ratio - 1)
    omega_diff_RB = 1.618      # ω_R - ω_B = -v₂

    # Phase factors for cross-terms
    cross_RG = np.exp(1j * omega_diff_RG * t)
    cross_GB = np.exp(1j * omega_diff_GB * t)
    cross_RB = np.exp(1j * omega_diff_RB * t)

    # Compute running time averages
    def running_average(signal, t):
        """Compute running time average up to each time point."""
        avg = np.zeros(len(t), dtype=complex)
        for i in range(1, len(t)):
            avg[i] = np.mean(signal[:i+1])
        return avg

    avg_RG = running_average(cross_RG, t)
    avg_GB = running_average(cross_GB, t)
    avg_RB = running_average(cross_RB, t)

    # Plot real parts of running averages (imaginary similar)
    t_normalized = t / (2 * np.pi)

    ax.plot(t_normalized, np.real(avg_RG), '-', color=COLOR_RED,
            linewidth=2, label=r'$\overline{e^{i(\phi_R - \phi_G)}}$', alpha=0.9)
    ax.plot(t_normalized, np.real(avg_GB), '-', color=COLOR_GREEN,
            linewidth=2, label=r'$\overline{e^{i(\phi_G - \phi_B)}}$', alpha=0.9)
    ax.plot(t_normalized, np.real(avg_RB), '-', color=COLOR_BLUE,
            linewidth=2, label=r'$\overline{e^{i(\phi_R - \phi_B)}}$', alpha=0.9)

    # Reference line at zero
    ax.axhline(y=0, color='black', linestyle='--', linewidth=1, alpha=0.5)

    # Diagonal term (always = 1)
    ax.axhline(y=1, color='gray', linestyle='-', linewidth=2, alpha=0.7,
               label=r'$\overline{e^{i \cdot 0}} = 1$ (diagonal)')

    ax.set_xlabel(r'Time $\tau / 2\pi$ (cycles)')
    ax.set_ylabel(r'Time-averaged phase factor')
    ax.set_xlim(0, T_max)
    ax.set_ylim(-0.5, 1.2)

    ax.legend(loc='upper right', fontsize=9, framealpha=0.95)

    ax.set_title(r'(b) Cross-Term Cancellation by Equidistribution',
                 fontsize=13, fontweight='bold', pad=10)


def create_panel_c(ax):
    """
    Panel (c): Emergence of Born rule probability |ψ|².

    Shows the spatial probability density P(x) = |ψ_eff(x)|² that
    emerges from time-averaged field intensity.
    """
    # Spatial coordinate (1D slice for visualization)
    x = np.linspace(-2, 2, 500)

    # Model pressure functions P_c(x) as Gaussians with different centers
    # representing spatial structure from stella octangula geometry
    sigma = 0.5
    P_R = np.exp(-((x - 0.0)**2) / (2 * sigma**2))  # Centered
    P_G = np.exp(-((x - 0.3)**2) / (2 * sigma**2))  # Offset right
    P_B = np.exp(-((x + 0.3)**2) / (2 * sigma**2))  # Offset left

    # Normalize
    P_R /= np.max(P_R)
    P_G /= np.max(P_G)
    P_B /= np.max(P_B)

    # Individual |χ_c|² contributions
    ax.fill_between(x, 0, P_R**2, color=COLOR_RED, alpha=0.2, label=r'$P_R(x)^2$')
    ax.fill_between(x, 0, P_G**2, color=COLOR_GREEN, alpha=0.2, label=r'$P_G(x)^2$')
    ax.fill_between(x, 0, P_B**2, color=COLOR_BLUE, alpha=0.2, label=r'$P_B(x)^2$')

    # Effective wave function squared: |ψ_eff|² = Σ P_c²
    psi_eff_squared = P_R**2 + P_G**2 + P_B**2

    # Normalize to probability
    psi_eff_squared /= np.trapezoid(psi_eff_squared, x)

    ax.plot(x, psi_eff_squared, '-', color='black', linewidth=3,
            label=r'$|\psi_{\rm eff}|^2 = \sum_c P_c^2$')

    # Show that this equals the Born rule
    ax.fill_between(x, 0, psi_eff_squared, color=COLOR_TRAJECTORY, alpha=0.3)

    ax.set_xlabel(r'Position $x / R_{\rm stella}$')
    ax.set_ylabel(r'Probability density $P(x)$')
    ax.set_xlim(-2, 2)
    ax.set_ylim(0, 1.1 * np.max(psi_eff_squared))

    ax.legend(loc='upper right', fontsize=9, framealpha=0.95)

    ax.set_title(r'(c) Born Rule: $P(x) = |\psi_{\rm eff}(x)|^2$',
                 fontsize=13, fontweight='bold', pad=10)


def create_figure():
    """
    Create three-panel figure showing Born rule derivation via ergodic flow.
    """
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    create_panel_a(axes[0])
    create_panel_b(axes[1])
    create_panel_c(axes[2])

    # Add overall title/caption with the derivation chain
    fig.text(0.5, 0.02,
             r'Ergodic geodesic flow on $(T^2, g^F)$ $\Rightarrow$ '
             r'Weyl equidistribution $\Rightarrow$ '
             r'Cross-terms vanish $\Rightarrow$ '
             r'Born rule $P = |\psi|^2$',
             ha='center', fontsize=12, fontweight='bold',
             bbox=dict(boxstyle='round,pad=0.4', facecolor='lightyellow',
                      edgecolor='goldenrod', linewidth=2, alpha=0.95))

    plt.tight_layout(rect=[0, 0.08, 1, 1])
    return fig


def main():
    """Generate and save the figure."""
    fig = create_figure()

    # Save in both formats
    for ext in ['pdf', 'png']:
        output_path = os.path.join(OUTPUT_DIR, f'fig_born_rule_ergodic_flow.{ext}')
        fig.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {output_path}")

    plt.close('all')


if __name__ == '__main__':
    main()
