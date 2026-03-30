#!/usr/bin/env python3
"""
Figure: Higgs Trilinear Coupling Prediction and Experimental Reach
===================================================================

Shows the CG prediction kappa_lambda = 0.97 +/- 0.03 in context with:
- Standard Model value (kappa_lambda = 1.0 by definition)
- Current LHC bounds (Run 2 combination)
- Projected HL-LHC, FCC-hh, and muon collider sensitivities
- BSM model ranges for comparison (2HDM, MSSM, Composite Higgs)

Key physics:
- lambda_CG = 1/8 = 0.125 from stella octangula vertex counting (Prop 0.0.27)
- lambda_SM = m_H^2/(2v^2) = 0.1293 from measured Higgs mass
- The 3.3% deficit is a robust geometric prediction with no free parameters
- Coleman-Weinberg one-loop correction shifts ratio by only -0.24%

Proof Document: docs/proofs/foundations/Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md
Paper Section: Section 10.6 (Higgs Mass from Stella Geometry)

Output: fig_prop_0_0_37_trilinear_coupling.pdf, fig_prop_0_0_37_trilinear_coupling.png
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from pathlib import Path

# Output directory (parent of scripts/)
OUTPUT_DIR = Path(__file__).parent.parent
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# ============================================================================
# DATA FROM PROP 0.0.37
# ============================================================================

# CG prediction (Prop 0.0.37)
KAPPA_CG = 0.97
KAPPA_CG_ERR = 0.03
KAPPA_CG_TREE = 0.9669

# SM value
KAPPA_SM = 1.0

# Current LHC Run 2 bounds (ATLAS+CMS, 95% CL)
LHC_R2_LO = -0.71
LHC_R2_HI = 6.1

# Projected experimental sensitivities (1-sigma on kappa_lambda)
HLLHC_ERR = 0.30      # HL-LHC ~30%
FCCHH_ERR = 0.075      # FCC-hh ~5-10% (use 7.5% midpoint)
MUONCOLL_ERR = 0.04    # Muon collider >= 10 TeV, ~3-5%

# BSM model ranges (typical ranges from literature)
BSM_MODELS = {
    '2HDM\n(Type II)': (0.5, 2.0),
    'MSSM': (0.8, 1.2),
    'Composite\nHiggs': (0.5, 1.0),
}


# ============================================================================
# FIGURE GENERATION
# ============================================================================

def generate_figure():
    """
    Generate kappa_lambda comparison figure.

    Single panel showing CG prediction band with experimental reach
    and BSM model ranges for context.
    """
    plt.rcParams.update({
        'font.family': 'sans-serif',
        'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
        'font.size': 10,
        'axes.labelsize': 12,
        'axes.titlesize': 13,
        'legend.fontsize': 9,
        'xtick.labelsize': 10,
        'ytick.labelsize': 10,
        'figure.dpi': 150,
        'savefig.dpi': 300,
        'text.usetex': False,
        'mathtext.fontset': 'dejavusans',
    })

    fig, ax = plt.subplots(figsize=(8, 5.5))

    # --- CG prediction band ---
    ax.axhspan(KAPPA_CG - KAPPA_CG_ERR, KAPPA_CG + KAPPA_CG_ERR,
               color='#27AE60', alpha=0.25, zorder=2)
    ax.axhline(KAPPA_CG, color='#27AE60', lw=2.5, zorder=3,
               label=rf'CG: $\kappa_\lambda = {KAPPA_CG} \pm {KAPPA_CG_ERR}$')

    # --- SM reference line ---
    ax.axhline(KAPPA_SM, color='black', lw=1.5, ls='--', zorder=3,
               label=r'SM: $\kappa_\lambda = 1.0$')

    # --- Invisible handle for LHC bounds in legend ---
    ax.plot([], [], ' ',
            label=f'LHC Run 2 95% CL: [{LHC_R2_LO}, {LHC_R2_HI}]')

    # --- Experimental sensitivities (centered on SM for illustration) ---
    # Show as error bars at different x positions
    exp_x = [1.5, 2.5, 3.5]
    exp_labels = ['HL-LHC\n(2035)', 'FCC-hh\n(2050s)', r'$\mu$-collider' + '\n(2060s?)']
    exp_errs = [HLLHC_ERR, FCCHH_ERR, MUONCOLL_ERR]
    exp_colors = ['#3498DB', '#E67E22', '#E74C3C']

    for i, (x, label, err, color) in enumerate(
            zip(exp_x, exp_labels, exp_errs, exp_colors)):
        # Show projected measurement assuming SM-like central value
        ax.errorbar(x, KAPPA_SM, yerr=err, fmt='o', markersize=8,
                    color=color, ecolor=color, elinewidth=2.5,
                    capsize=6, capthick=2, zorder=5)
        ax.text(x, KAPPA_SM - err - 0.06, label,
                ha='center', va='top', fontsize=9, color=color,
                fontweight='bold')

    # --- BSM model ranges (shown as vertical bands on the right) ---
    bsm_x_start = 5.0
    bsm_width = 0.6
    bsm_colors = ['#9B59B6', '#2980B9', '#D35400']
    y_max = 1.45  # clip ranges that extend beyond axis

    for i, (name, (lo, hi)) in enumerate(BSM_MODELS.items()):
        x_center = bsm_x_start + i * 1.0
        hi_clipped = min(hi, y_max)
        ax.fill_between([x_center - bsm_width/2, x_center + bsm_width/2],
                        lo, hi_clipped, color=bsm_colors[i], alpha=0.3, zorder=2)
        ax.plot([x_center - bsm_width/2, x_center + bsm_width/2],
                [lo, lo], color=bsm_colors[i], lw=1.5)
        if hi <= y_max:
            ax.plot([x_center - bsm_width/2, x_center + bsm_width/2],
                    [hi, hi], color=bsm_colors[i], lw=1.5)
        # Label inside the band for tall ranges; above for short ones
        if hi > y_max:
            label_y = y_max - 0.04
            ax.text(x_center, label_y, name.replace('\n', ' ') + f'\n({lo}\u2013{hi})',
                    ha='center', va='top', fontsize=8, color=bsm_colors[i],
                    fontweight='bold')
        else:
            ax.text(x_center, hi + 0.03, name,
                    ha='center', va='bottom', fontsize=8, color=bsm_colors[i],
                    fontweight='bold')

    # --- Axes ---
    ax.set_xlim(0, 7.5)
    ax.set_ylim(0.3, 1.50)
    ax.set_ylabel(r'$\kappa_\lambda \equiv \lambda_3 / \lambda_3^{\mathrm{SM}}$',
                  fontsize=13)

    # Remove x-axis ticks (categories, not continuous)
    ax.set_xticks([])

    # Section labels along bottom
    ax.text(2.5, 0.33, 'Projected Experimental Precision',
            ha='center', va='bottom', fontsize=10, color='#555555',
            fontweight='bold')
    ax.text(6.0, 0.33, 'BSM Ranges',
            ha='center', va='bottom', fontsize=10, color='#555555',
            fontweight='bold')

    # Vertical separator
    ax.axvline(4.25, color='gray', lw=0.8, ls=':', alpha=0.5)

    # Title
    ax.set_title(
        r'Higgs Trilinear Coupling: CG Prediction ($\lambda = 1/8$) vs Experiment',
        fontsize=13, fontweight='bold')

    # Legend
    ax.legend(loc='upper left', framealpha=0.95, fontsize=10)

    # Grid
    ax.grid(axis='y', alpha=0.3, linestyle='-', linewidth=0.5)

    plt.tight_layout()

    # Save
    png_path = OUTPUT_DIR / 'fig_prop_0_0_37_trilinear_coupling.png'
    pdf_path = OUTPUT_DIR / 'fig_prop_0_0_37_trilinear_coupling.pdf'

    plt.savefig(png_path, dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(pdf_path, bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")

    return png_path, pdf_path


def print_data_summary():
    """Print numerical summary for verification."""
    print("\n" + "=" * 65)
    print("Higgs Trilinear Coupling - Data Summary (Prop 0.0.37)")
    print("=" * 65)

    print(f"\nCG Prediction:")
    print(f"  kappa_lambda (tree)  = {KAPPA_CG_TREE:.4f}")
    print(f"  kappa_lambda (final) = {KAPPA_CG} +/- {KAPPA_CG_ERR}")
    print(f"  lambda_3^CG          = 30.9 +/- 1.0 GeV")
    print(f"  lambda_3^SM          = 31.8 +/- 0.06 GeV")

    print(f"\nSM Value:  kappa_lambda = {KAPPA_SM:.3f}")

    print(f"\nFalsification window: [{KAPPA_CG - 3*KAPPA_CG_ERR:.2f}, "
          f"{KAPPA_CG + 3*KAPPA_CG_ERR:.2f}] at >3sigma")
    print(f"  => [0.91, 1.03] (from Prop 0.0.37)")

    print(f"\nCurrent LHC bounds (95% CL): [{LHC_R2_LO}, {LHC_R2_HI}]")
    print(f"  Width: {LHC_R2_HI - LHC_R2_LO:.2f}")
    print(f"  CG window width: 0.12 => ~57x tighter")

    print(f"\nProjected sensitivities (1-sigma):")
    print(f"  HL-LHC:       +/- {HLLHC_ERR:.2f} ({HLLHC_ERR*100:.0f}%)")
    print(f"  FCC-hh:       +/- {FCCHH_ERR:.3f} ({FCCHH_ERR*100:.1f}%)")
    print(f"  Muon collider: +/- {MUONCOLL_ERR:.2f} ({MUONCOLL_ERR*100:.0f}%)")

    for name, (lo, hi) in BSM_MODELS.items():
        print(f"  {name.replace(chr(10), ' ')}: [{lo}, {hi}]")

    print("=" * 65 + "\n")


if __name__ == "__main__":
    print_data_summary()
    generate_figure()
