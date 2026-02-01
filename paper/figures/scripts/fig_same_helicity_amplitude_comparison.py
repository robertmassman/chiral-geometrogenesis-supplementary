#!/usr/bin/env python3
"""
Figure: Same-Helicity Gluon Scattering Amplitude Comparison (Theorem 6.2.2)

Two-panel comparison showing:
(a) Standard QCD: M(g⁺g⁺ → g⁺g⁺) = 0 (exactly zero at tree level)
(b) Chiral Geometrogenesis: Non-zero amplitude via χGG̃ coupling

Key physics:
- Standard QCD forbids same-helicity gluon scattering at tree level (Parke-Taylor)
- CG framework predicts non-zero amplitude via χ exchange between χGG̃ vertices
- Cross-section ratio: σ/σ_tot ~ 10⁻⁹ at GeV scale
- Unique experimental signature distinguishing CG from Standard Model

Proof Document: docs/proofs/Phase6/Theorem-6.2.2-Helicity-Amplitudes-Spinor-Helicity-Formalism.md
Paper Section: Section 6.4.2 (Helicity Structure and Spinor-Helicity Formalism)

Output: fig_same_helicity_amplitude_comparison.pdf, fig_same_helicity_amplitude_comparison.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.patches import FancyBboxPatch
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

# Colors - consistent with CLAUDE.md palette
COLOR_QCD_ZERO = '#2C3E50'      # Dark gray for zero amplitude
COLOR_CG_HIGH = '#FFD700'       # Gold for high coupling
COLOR_CG_LOW = '#1a0033'        # Deep purple for low coupling
COLOR_HIGHLIGHT = '#E74C3C'     # Red for annotations
COLOR_SUPPRESSION = '#9B59B6'   # Purple for suppression note


def create_amplitude_comparison_figure():
    """
    Create the 2-panel amplitude comparison figure.

    Panel (a): Standard QCD - exactly zero everywhere
    Panel (b): CG framework - non-zero but highly suppressed
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # Define phase space grid
    # √s from 0.5 to 5 GeV (typical QCD scale)
    # t from -5 to -0.1 GeV² (physical scattering region, t < 0)
    sqrt_s = np.linspace(0.5, 5, 200)
    t = np.linspace(-5, -0.1, 200)
    S, T = np.meshgrid(sqrt_s, t)
    s = S**2  # s = (√s)²

    # =========================================================================
    # Panel (a): Standard QCD - M = 0
    # =========================================================================

    # QCD amplitude: exactly zero for same-helicity at tree level
    M_qcd_squared = np.zeros_like(S)

    # Gray colormap for "nothing here"
    im1 = ax1.imshow(M_qcd_squared, extent=[0.5, 5, -5, -0.1], origin='lower',
                     cmap='gray', vmin=0, vmax=1, aspect='auto')

    # Large "ZERO" annotation
    ax1.text(2.75, -2.5, r'$\mathcal{M} = 0$', fontsize=28, ha='center', va='center',
             color='white', fontweight='bold', alpha=0.9,
             bbox=dict(boxstyle='round,pad=0.4', facecolor='black', alpha=0.7))

    # Explanation text
    ax1.text(2.75, -4.2, 'Tree-level amplitude\nvanishes by Parke-Taylor',
             fontsize=10, ha='center', va='center', color='lightgray',
             style='italic')

    ax1.set_xlabel(r'$\sqrt{s}$ (GeV)', fontsize=12)
    ax1.set_ylabel(r'$t$ (GeV$^2$)', fontsize=12)
    ax1.set_title(r'(a) Standard QCD: $|\mathcal{M}(g^+g^+ \to g^+g^+)|^2$',
                  fontsize=12, fontweight='bold')

    # =========================================================================
    # Panel (b): CG Framework - Non-zero via χ exchange
    # =========================================================================

    # CG amplitude from Theorem 6.2.2:
    # |M|² ∝ C_χ⁴ α_s⁴ s² / (8π)⁸

    # Physical parameters
    C_chi = 1.5      # N_f/2 for 3 light flavors
    alpha_s = 0.3    # Strong coupling at GeV scale

    # Compute |M|² (normalized for visualization)
    prefactor = (C_chi**4 * alpha_s**4) / (8 * np.pi)**4
    M_cg_squared = prefactor * s**2
    M_cg_norm = M_cg_squared / M_cg_squared.max()

    # Custom colormap: deep purple to bright gold
    colors_cg = ['#1a0033', '#2d004d', '#400066', '#530080', '#6600cc',
                 '#8833ff', '#aa66ff', '#cc99ff', '#ffcc00', '#ffdd44']
    cmap_cg = LinearSegmentedColormap.from_list('cg_amplitude', colors_cg)

    im2 = ax2.imshow(M_cg_norm, extent=[0.5, 5, -5, -0.1], origin='lower',
                     cmap=cmap_cg, vmin=0, vmax=1, aspect='auto')

    # Single clean annotation for suppression
    ax2.text(2.75, -2.5, r'$\sigma/\sigma_{\rm tot} \sim 10^{-9}$',
             fontsize=12, ha='center', va='center', color='white',
             fontweight='bold',
             bbox=dict(boxstyle='round,pad=0.4', facecolor=COLOR_SUPPRESSION, alpha=0.85))

    ax2.set_xlabel(r'$\sqrt{s}$ (GeV)', fontsize=12)
    ax2.set_ylabel(r'$t$ (GeV$^2$)', fontsize=12)
    ax2.set_title(r'(b) Chiral Geometrogenesis: $|\mathcal{M}(g^+g^+ \to g^+g^+)|^2$',
                  fontsize=12, fontweight='bold')

    # Colorbar
    divider = make_axes_locatable(ax2)
    cax = divider.append_axes("right", size="5%", pad=0.1)
    cbar = plt.colorbar(im2, cax=cax)
    cbar.set_label(r'$|\mathcal{M}|^2$ (normalized)', fontsize=10)

    plt.tight_layout()
    return fig


def create_figure_with_mechanism():
    """
    Alternative version with mechanism diagram included.
    """
    fig = plt.figure(figsize=(14, 5))

    # Panel (a): QCD = 0
    ax1 = fig.add_subplot(131)

    # Panel (b): CG non-zero
    ax2 = fig.add_subplot(132)

    # Panel (c): Mechanism diagram
    ax3 = fig.add_subplot(133)

    # ... (implement if needed)

    return fig


def print_physics_summary():
    """Print the physics behind the figure."""
    print()
    print("=" * 70)
    print("PHYSICS SUMMARY: Same-Helicity Gluon Scattering")
    print("=" * 70)
    print()
    print("Standard QCD (Parke-Taylor formula):")
    print("  • MHV amplitudes require exactly 2 negative helicities")
    print("  • M(g⁺g⁺ → g⁺g⁺) = 0 at tree level")
    print("  • This is a consequence of supersymmetric Ward identities")
    print()
    print("Chiral Geometrogenesis:")
    print("  • χGG̃ anomaly coupling enables same-helicity scattering")
    print("  • Mechanism: g⁺g⁺ → χ → g⁺g⁺ via two anomaly vertices")
    print("  • GG̃ ∝ |G⁺|² - |G⁻|² selects same-helicity pairs")
    print()

    # Calculate numerical values
    C_chi = 1.5
    alpha_s = 0.3

    print("Amplitude formula:")
    print(f"  M = (C_χ² α_s²)/(8π)² × [12]²[34]*²/s")
    print(f"  where C_χ = N_f/2 = {C_chi}")
    print()

    # Cross-section ratio
    prefactor = (C_chi**4 * alpha_s**4) / ((8 * np.pi)**4)
    qcd_prefactor = (4 * np.pi * alpha_s)**2
    ratio = prefactor / qcd_prefactor

    print("Cross-section ratio:")
    print(f"  σ(++++)/σ_tot ~ {ratio:.1e}")
    print()
    print("Experimental signature:")
    print("  • Non-zero same-helicity scattering is unique to CG")
    print("  • Would require polarized gluon beams to test")
    print("  • Currently beyond experimental reach (~10⁻⁹ suppression)")
    print()


def main():
    """Generate figures and save to the paper figures directory."""

    print("=" * 70)
    print("Generating Same-Helicity Amplitude Comparison (Theorem 6.2.2)")
    print("=" * 70)
    print(f"\nOutput directory: {OUTPUT_DIR}/")
    print()

    # Create main figure
    print("Creating 2-panel amplitude comparison figure...")
    fig = create_amplitude_comparison_figure()

    # Save outputs
    png_path = os.path.join(OUTPUT_DIR, 'fig_same_helicity_amplitude_comparison.png')
    pdf_path = os.path.join(OUTPUT_DIR, 'fig_same_helicity_amplitude_comparison.pdf')

    fig.savefig(png_path, dpi=300, bbox_inches='tight', facecolor='white')
    fig.savefig(pdf_path, bbox_inches='tight', facecolor='white')

    print(f"   Saved: fig_same_helicity_amplitude_comparison.png")
    print(f"   Saved: fig_same_helicity_amplitude_comparison.pdf")

    # Print physics summary
    print_physics_summary()

    print("=" * 70)
    print("Done!")

    plt.close('all')


if __name__ == '__main__':
    main()
