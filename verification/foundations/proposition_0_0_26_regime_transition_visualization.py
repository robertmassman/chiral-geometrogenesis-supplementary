#!/usr/bin/env python3
"""
Proposition 0.0.26: Visualization of Strong-Coupling to Weak-Coupling Transition

This script visualizes the transition between:
- Strong coupling (QCD-like): Enhancement factor = 4π ≈ 12.6
- Weak coupling (EW-like): Enhancement factor = dim(adj)

The key insight is that the π factor difference between NDA (4πv) and our
prediction (4v) represents a genuine physics transition, not a discrepancy.

Physical basis:
- At strong coupling (α ~ 1): All loop orders contribute comparably → 4π factor
- At weak coupling (α << 1): Loops suppressed → only gauge multiplicity matters → dim(adj)

Created: 2026-02-02
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import matplotlib.patches as mpatches

# Physical constants
ALPHA_S_LOW = 1.0      # QCD coupling at low energy (strong)
ALPHA_S_MZ = 0.118     # QCD coupling at M_Z
ALPHA_2 = 0.034        # EW coupling (weak)
ALPHA_EM = 1/137       # Electromagnetic coupling

DIM_ADJ_QCD = 8        # dim(su(3)) = 8
DIM_ADJ_EW = 4         # dim(su(2) ⊕ u(1)) = 4
FOUR_PI = 4 * np.pi    # ≈ 12.57


def loop_enhancement_factor(alpha, dim_adj, alpha_critical=0.3):
    """
    Compute the effective enhancement factor as a function of coupling.

    Physics:
    - At strong coupling (α >> α_c): Loops unsuppressed → 4π enhancement
    - At weak coupling (α << α_c): Loops suppressed → dim(adj) enhancement

    The transition is modeled as a smooth crossover.

    Parameters:
    -----------
    alpha : float or array
        The coupling constant (α = g²/4π)
    dim_adj : int
        Dimension of the adjoint representation
    alpha_critical : float
        Critical coupling where transition occurs (~0.3 based on QCD)

    Returns:
    --------
    F : float or array
        The effective enhancement factor Λ/v
    """
    # Smooth crossover function using tanh
    # x = 0 at α = α_c, negative for weak coupling, positive for strong
    x = (alpha - alpha_critical) / alpha_critical

    # Transition function: 0 at weak coupling, 1 at strong coupling
    transition = 0.5 * (1 + np.tanh(2 * x))

    # Interpolate between dim(adj) and 4π
    F = dim_adj + (FOUR_PI - dim_adj) * transition

    return F


def loop_enhancement_physical(alpha, dim_adj):
    """
    Alternative model based on resummed loop series.

    Physics motivation:
    - n-loop contribution scales as (α × dim(adj))^n / (16π²)^n
    - Sum of geometric series: 1/(1 - α × dim(adj)/16π²)
    - At strong coupling, this diverges → need non-perturbative 4π
    - At weak coupling, leading term dominates → dim(adj)

    The enhancement factor interpolates as:
    F(α) = dim(adj) × [1 + (4π/dim(adj) - 1) × α/(1 - α)]
         ≈ dim(adj) at small α
         → 4π as α → 1
    """
    # Regularized version to avoid divergence
    alpha_eff = np.minimum(alpha, 0.95)  # Cap at 0.95 to avoid divergence

    # Loop resummation factor
    loop_factor = alpha_eff / (1 - alpha_eff + 0.01)  # Small regulator

    # Interpolate
    ratio = FOUR_PI / dim_adj  # ≈ 3.14 for EW, ≈ 1.57 for QCD
    F = dim_adj * (1 + (ratio - 1) * np.tanh(loop_factor))

    return F


def create_regime_transition_plot():
    """Create the main visualization of the regime transition."""

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # =========================================================================
    # Panel 1: Enhancement factor vs coupling (log scale)
    # =========================================================================
    ax1 = axes[0, 0]

    alpha = np.logspace(-3, 0, 500)  # 0.001 to 1

    # EW sector (dim(adj) = 4)
    F_ew = loop_enhancement_factor(alpha, DIM_ADJ_EW, alpha_critical=0.25)
    ax1.semilogx(alpha, F_ew, 'b-', linewidth=2.5, label=f'SU(2)×U(1), dim(adj)={DIM_ADJ_EW}')

    # QCD sector (dim(adj) = 8)
    F_qcd = loop_enhancement_factor(alpha, DIM_ADJ_QCD, alpha_critical=0.25)
    ax1.semilogx(alpha, F_qcd, 'r-', linewidth=2.5, label=f'SU(3), dim(adj)={DIM_ADJ_QCD}')

    # Mark specific points
    ax1.axhline(y=FOUR_PI, color='gray', linestyle='--', alpha=0.7, label=f'4π ≈ {FOUR_PI:.2f} (NDA limit)')
    ax1.axhline(y=DIM_ADJ_EW, color='blue', linestyle=':', alpha=0.5)
    ax1.axhline(y=DIM_ADJ_QCD, color='red', linestyle=':', alpha=0.5)

    # Mark QCD and EW positions
    ax1.plot(ALPHA_S_LOW, loop_enhancement_factor(ALPHA_S_LOW, DIM_ADJ_QCD), 'ro',
             markersize=12, markeredgecolor='black', markeredgewidth=2,
             label=f'QCD @ α_s~1: F≈{loop_enhancement_factor(ALPHA_S_LOW, DIM_ADJ_QCD):.1f}')
    ax1.plot(ALPHA_2, loop_enhancement_factor(ALPHA_2, DIM_ADJ_EW), 'bs',
             markersize=12, markeredgecolor='black', markeredgewidth=2,
             label=f'EW @ α₂≈0.034: F≈{loop_enhancement_factor(ALPHA_2, DIM_ADJ_EW):.1f}')

    # Shade regions
    ax1.axvspan(0.001, 0.1, alpha=0.1, color='blue', label='Weak coupling regime')
    ax1.axvspan(0.3, 1.0, alpha=0.1, color='red', label='Strong coupling regime')

    ax1.set_xlabel('Coupling constant α = g²/4π', fontsize=12)
    ax1.set_ylabel('Enhancement factor Λ/v', fontsize=12)
    ax1.set_title('Transition from Weak to Strong Coupling Regimes', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left', fontsize=9)
    ax1.set_xlim(0.001, 1)
    ax1.set_ylim(0, 15)
    ax1.grid(True, alpha=0.3)

    # =========================================================================
    # Panel 2: The π factor as a function of coupling
    # =========================================================================
    ax2 = axes[0, 1]

    # Ratio of NDA prediction to our prediction
    # At strong coupling: ratio → 1 (both give 4π)
    # At weak coupling: ratio → 4π/dim(adj) = π for EW

    F_nda = FOUR_PI * np.ones_like(alpha)  # NDA always predicts 4π
    ratio_ew = F_nda / F_ew
    ratio_qcd = F_nda / F_qcd

    ax2.semilogx(alpha, ratio_ew, 'b-', linewidth=2.5, label='SU(2)×U(1): 4π/F(α)')
    ax2.semilogx(alpha, ratio_qcd, 'r-', linewidth=2.5, label='SU(3): 4π/F(α)')

    ax2.axhline(y=np.pi, color='purple', linestyle='--', linewidth=2,
                label=f'π ≈ {np.pi:.3f} (EW weak-coupling limit)')
    ax2.axhline(y=FOUR_PI/DIM_ADJ_QCD, color='orange', linestyle='--', linewidth=2,
                label=f'4π/8 ≈ {FOUR_PI/DIM_ADJ_QCD:.3f} (QCD weak-coupling limit)')
    ax2.axhline(y=1, color='gray', linestyle=':', alpha=0.7, label='Strong coupling (NDA valid)')

    # Mark positions
    ax2.plot(ALPHA_2, FOUR_PI/loop_enhancement_factor(ALPHA_2, DIM_ADJ_EW), 'bs',
             markersize=12, markeredgecolor='black', markeredgewidth=2)
    ax2.plot(ALPHA_S_LOW, FOUR_PI/loop_enhancement_factor(ALPHA_S_LOW, DIM_ADJ_QCD), 'ro',
             markersize=12, markeredgecolor='black', markeredgewidth=2)

    ax2.set_xlabel('Coupling constant α = g²/4π', fontsize=12)
    ax2.set_ylabel('Ratio: Λ_NDA / Λ_framework', fontsize=12)
    ax2.set_title('The π Factor: Departure from NDA', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right', fontsize=9)
    ax2.set_xlim(0.001, 1)
    ax2.set_ylim(0.8, 4)
    ax2.grid(True, alpha=0.3)

    # Add annotation
    ax2.annotate('EW sector:\nNDA overestimates\nby factor of π',
                 xy=(ALPHA_2, np.pi), xytext=(0.002, 2.5),
                 fontsize=10, ha='left',
                 arrowprops=dict(arrowstyle='->', color='blue', lw=1.5))

    # =========================================================================
    # Panel 3: Physical picture - Loop contributions
    # =========================================================================
    ax3 = axes[1, 0]

    # Show how loop contributions build up
    n_loops = np.arange(0, 8)

    # Strong coupling (α = 0.8)
    alpha_strong = 0.8
    loop_contrib_strong = (alpha_strong * DIM_ADJ_QCD / (16 * np.pi**2)) ** n_loops

    # Weak coupling (α = 0.034)
    alpha_weak = 0.034
    loop_contrib_weak = (alpha_weak * DIM_ADJ_EW / (16 * np.pi**2)) ** n_loops

    bar_width = 0.35
    x = n_loops

    bars1 = ax3.bar(x - bar_width/2, loop_contrib_strong, bar_width,
                    label=f'Strong coupling (α={alpha_strong})', color='red', alpha=0.7)
    bars2 = ax3.bar(x + bar_width/2, loop_contrib_weak, bar_width,
                    label=f'Weak coupling (α={alpha_weak})', color='blue', alpha=0.7)

    ax3.set_xlabel('Loop order n', fontsize=12)
    ax3.set_ylabel('Relative contribution (α × dim(adj) / 16π²)ⁿ', fontsize=12)
    ax3.set_title('Loop Contributions by Order', fontsize=14, fontweight='bold')
    ax3.legend(fontsize=10)
    ax3.set_yscale('log')
    ax3.set_ylim(1e-16, 10)
    ax3.set_xticks(n_loops)
    ax3.grid(True, alpha=0.3, axis='y')

    # Add text annotations
    ax3.text(3, 1e-1, 'Strong coupling:\nAll loops matter\n→ 4π enhancement',
             fontsize=10, ha='center', color='darkred',
             bbox=dict(boxstyle='round', facecolor='mistyrose', alpha=0.8))
    ax3.text(5, 1e-10, 'Weak coupling:\nHigher loops negligible\n→ dim(adj) counting',
             fontsize=10, ha='center', color='darkblue',
             bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8))

    # =========================================================================
    # Panel 4: Gradient visualization of the transition
    # =========================================================================
    ax4 = axes[1, 1]

    # Create a 2D gradient showing the transition
    alpha_range = np.linspace(0.01, 1.0, 100)
    dim_adj_range = np.linspace(2, 12, 100)

    Alpha, Dim = np.meshgrid(alpha_range, dim_adj_range)

    # Enhancement factor across the space
    F_map = np.zeros_like(Alpha)
    for i in range(len(dim_adj_range)):
        for j in range(len(alpha_range)):
            F_map[i, j] = loop_enhancement_factor(Alpha[i, j], Dim[i, j])

    # Normalize to show deviation from dim(adj)
    Ratio_map = F_map / Dim  # = 1 at weak coupling, = 4π/dim(adj) at strong

    im = ax4.contourf(Alpha, Dim, Ratio_map, levels=20, cmap='RdYlBu_r')
    cbar = plt.colorbar(im, ax=ax4, label='F(α)/dim(adj)')

    # Mark specific theories
    ax4.plot(ALPHA_2, DIM_ADJ_EW, 'bs', markersize=15, markeredgecolor='white',
             markeredgewidth=2, label='EW: SU(2)×U(1)')
    ax4.plot(ALPHA_S_LOW, DIM_ADJ_QCD, 'ro', markersize=15, markeredgecolor='white',
             markeredgewidth=2, label='QCD: SU(3)')
    ax4.plot(ALPHA_S_MZ, DIM_ADJ_QCD, 'r^', markersize=12, markeredgecolor='white',
             markeredgewidth=2, label='QCD @ M_Z')

    # Contour lines
    cs = ax4.contour(Alpha, Dim, Ratio_map, levels=[1.1, 1.5, 2.0, 2.5, 3.0],
                     colors='black', linewidths=0.5, alpha=0.5)
    ax4.clabel(cs, inline=True, fontsize=8)

    ax4.set_xlabel('Coupling constant α', fontsize=12)
    ax4.set_ylabel('dim(adj)', fontsize=12)
    ax4.set_title('Phase Diagram: Enhancement Factor Regimes', fontsize=14, fontweight='bold')
    ax4.legend(loc='upper left', fontsize=9)

    # Add region labels
    ax4.text(0.1, 3, 'Weak coupling\nF ≈ dim(adj)', fontsize=10, ha='center',
             bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8))
    ax4.text(0.8, 10, 'Strong coupling\nF → 4π', fontsize=10, ha='center',
             bbox=dict(boxstyle='round', facecolor='mistyrose', alpha=0.8))

    plt.tight_layout()
    plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_0_0_26_regime_transition.png',
                dpi=150, bbox_inches='tight')
    plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_0_0_26_regime_transition.pdf',
                bbox_inches='tight')
    print("Saved: prop_0_0_26_regime_transition.png/pdf")

    return fig


def create_interpolation_formula_plot():
    """
    Create a detailed plot showing the interpolation formula and its physical basis.
    """
    fig, ax = plt.subplots(figsize=(12, 8))

    alpha = np.logspace(-3, 0, 500)

    # Different interpolation models
    F_tanh = loop_enhancement_factor(alpha, DIM_ADJ_EW, alpha_critical=0.25)
    F_phys = loop_enhancement_physical(alpha, DIM_ADJ_EW)

    # Simple linear interpolation for comparison
    F_linear = DIM_ADJ_EW + (FOUR_PI - DIM_ADJ_EW) * alpha
    F_linear = np.minimum(F_linear, FOUR_PI)

    ax.semilogx(alpha, F_tanh, 'b-', linewidth=3, label='Tanh crossover model')
    ax.semilogx(alpha, F_phys, 'g--', linewidth=2.5, label='Loop resummation model')
    ax.semilogx(alpha, F_linear, 'r:', linewidth=2, label='Linear interpolation')

    # Asymptotic limits
    ax.axhline(y=FOUR_PI, color='gray', linestyle='--', alpha=0.5, label=f'4π = {FOUR_PI:.2f}')
    ax.axhline(y=DIM_ADJ_EW, color='gray', linestyle=':', alpha=0.5, label=f'dim(adj) = {DIM_ADJ_EW}')

    # Mark the EW point
    ax.axvline(x=ALPHA_2, color='blue', linestyle='--', alpha=0.3)
    ax.plot(ALPHA_2, DIM_ADJ_EW, 'bs', markersize=15, markeredgecolor='black',
            markeredgewidth=2, zorder=10)
    ax.annotate(f'EW sector\nα₂ ≈ {ALPHA_2}\nF = {DIM_ADJ_EW}',
                xy=(ALPHA_2, DIM_ADJ_EW), xytext=(0.001, 6),
                fontsize=11, ha='left',
                arrowprops=dict(arrowstyle='->', color='blue', lw=2),
                bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.9))

    # Mark the QCD point (using α_s ~ 0.3 at GeV scale)
    alpha_qcd_gev = 0.35
    F_qcd_val = loop_enhancement_factor(alpha_qcd_gev, DIM_ADJ_QCD, alpha_critical=0.25)
    ax.plot(alpha_qcd_gev, F_qcd_val, 'ro', markersize=15, markeredgecolor='black',
            markeredgewidth=2, zorder=10)
    ax.annotate(f'QCD @ 1 GeV\nα_s ≈ {alpha_qcd_gev}\nF ≈ {F_qcd_val:.1f}',
                xy=(alpha_qcd_gev, F_qcd_val), xytext=(0.5, 8),
                fontsize=11, ha='left',
                arrowprops=dict(arrowstyle='->', color='red', lw=2),
                bbox=dict(boxstyle='round', facecolor='mistyrose', alpha=0.9))

    # Shade the transition region
    ax.axvspan(0.1, 0.5, alpha=0.15, color='yellow', label='Crossover region')

    ax.set_xlabel('Coupling constant α = g²/4π', fontsize=14)
    ax.set_ylabel('Enhancement factor F = Λ/v', fontsize=14)
    ax.set_title('The Weak-to-Strong Coupling Crossover\n'
                 'How the cutoff enhancement factor transitions from dim(adj) to 4π',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='center right', fontsize=10)
    ax.set_xlim(0.001, 1)
    ax.set_ylim(0, 15)
    ax.grid(True, alpha=0.3)

    # Add formula box
    formula_text = (
        r'$\mathbf{Interpolation\ Formula:}$' + '\n\n'
        r'$F(\alpha) = \mathrm{dim(adj)} + (4\pi - \mathrm{dim(adj)}) \cdot T(\alpha)$' + '\n\n'
        r'where $T(\alpha) = \frac{1}{2}\left(1 + \tanh\left(\frac{\alpha - \alpha_c}{\alpha_c}\right)\right)$' + '\n\n'
        r'$\alpha_c \approx 0.25$ (crossover coupling)'
    )
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.9)
    ax.text(0.02, 0.97, formula_text, transform=ax.transAxes, fontsize=11,
            verticalalignment='top', bbox=props, family='serif')

    plt.tight_layout()
    plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/prop_0_0_26_interpolation_formula.png',
                dpi=150, bbox_inches='tight')
    print("Saved: prop_0_0_26_interpolation_formula.png")

    return fig


def print_summary():
    """Print a summary of the physics and numerical values."""
    print("=" * 70)
    print("Proposition 0.0.26: Regime Transition Visualization")
    print("=" * 70)
    print()
    print("PHYSICAL PICTURE:")
    print("-" * 70)
    print("The enhancement factor F = Λ/v transitions between two regimes:")
    print()
    print("  WEAK COUPLING (α << 1):   F → dim(adj)")
    print("    - Loops suppressed by factors of α")
    print("    - Higher-order corrections negligible")
    print("    - Cutoff set by operator counting = number of gauge generators")
    print()
    print("  STRONG COUPLING (α ~ 1):  F → 4π")
    print("    - All loop orders contribute comparably")
    print("    - NDA (Naive Dimensional Analysis) applies")
    print("    - Cutoff set by geometric series: 1 + α + α² + ... → 4π factor")
    print()
    print("-" * 70)
    print("NUMERICAL VALUES:")
    print("-" * 70)
    print(f"  4π = {FOUR_PI:.4f}")
    print(f"  dim(adj_EW) = {DIM_ADJ_EW}")
    print(f"  dim(adj_QCD) = {DIM_ADJ_QCD}")
    print()
    print(f"  α_EW = {ALPHA_2} (weak coupling)")
    print(f"  α_s(M_Z) = {ALPHA_S_MZ} (perturbative)")
    print(f"  α_s(1 GeV) ~ 0.35 (approaching strong)")
    print(f"  α_s(Λ_QCD) ~ 1 (strong coupling)")
    print()
    print("-" * 70)
    print("THE π FACTOR:")
    print("-" * 70)
    print(f"  Λ_NDA / Λ_EW = 4π / 4 = π ≈ {np.pi:.4f}")
    print()
    print("  This is NOT a discrepancy!")
    print("  It is the signature of weak coupling vs strong coupling physics.")
    print()
    print("  At weak coupling: F = dim(adj) = 4  →  Λ_EW = 4 × v_H = 985 GeV")
    print("  NDA predicts:     F = 4π ≈ 12.6   →  Λ_NDA = 4π × v_H = 3094 GeV")
    print()
    print("  The factor of π difference tells us the EW sector is weakly coupled!")
    print("=" * 70)


if __name__ == "__main__":
    print_summary()
    print()
    print("Generating visualizations...")
    print()

    fig1 = create_regime_transition_plot()
    fig2 = create_interpolation_formula_plot()

    print()
    print("Done! Check verification/plots/ for output files.")

    plt.show()
