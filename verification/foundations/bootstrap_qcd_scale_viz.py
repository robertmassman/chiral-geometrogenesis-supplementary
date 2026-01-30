#!/usr/bin/env python3
"""
Visualization: Bootstrap & QCD Scale Determination Chain
=========================================================

Creates a visual image showing how QCD parameters emerge from pure geometry.

Group 1 Propositions:
- 0.0.17j: String Tension from Casimir Energy
- 0.0.17q: QCD Scale from Dimensional Transmutation
- 0.0.17y: Bootstrap Fixed-Point Uniqueness
- 0.0.17z: Non-Perturbative Corrections to Bootstrap
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle, Polygon
import numpy as np
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

# Style settings
plt.rcParams['font.family'] = 'DejaVu Sans'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.linewidth'] = 1.5

# =============================================================================
# CONSTANTS
# =============================================================================

# Topological inputs
N_c = 3
N_f = 3
chi = 4
b0 = (11*N_c - 2*N_f) / (12 * np.pi)
adj_squared = (N_c**2 - 1)**2  # = 64

# Physical values
hbar_c = 197.327  # MeV·fm
sqrt_sigma_oneloop = 481.1  # MeV
sqrt_sigma_corrected = 434.6  # MeV
sqrt_sigma_observed = 440  # MeV
R_stella = 0.44847  # fm
exponent = 128 * np.pi / 9


def create_bootstrap_visualization():
    """Create a comprehensive visual representation of the bootstrap chain."""

    fig = plt.figure(figsize=(16, 12), facecolor='white')

    # Create grid for subplots
    # Main panel: derivation chain as visual equation
    ax_main = fig.add_axes([0.05, 0.35, 0.9, 0.55])

    # Bottom left: stella octangula
    ax_stella = fig.add_axes([0.05, 0.05, 0.25, 0.25], projection='3d')

    # Bottom middle: scale ladder
    ax_scales = fig.add_axes([0.35, 0.05, 0.3, 0.25])

    # Bottom right: correction pie
    ax_pie = fig.add_axes([0.7, 0.05, 0.25, 0.25])

    # =========================================================================
    # MAIN PANEL: The Derivation Chain as Visual Equation
    # =========================================================================

    ax_main.set_xlim(0, 10)
    ax_main.set_ylim(0, 6)
    ax_main.axis('off')

    # Title
    ax_main.text(5, 5.8, "Bootstrap & QCD Scale Determination",
                fontsize=20, fontweight='bold', ha='center', va='top')
    ax_main.text(5, 5.4, "From Pure Topology to QCD Confinement",
                fontsize=14, ha='center', va='top', style='italic', color='#555')

    # --- Row 1: Topological Inputs ---
    y1 = 4.5

    # Box: Topology
    box1 = FancyBboxPatch((0.3, y1-0.4), 2.4, 0.8, boxstyle="round,pad=0.05",
                          facecolor='#E3F2FD', edgecolor='#1565C0', linewidth=2)
    ax_main.add_patch(box1)
    ax_main.text(1.5, y1, "TOPOLOGY", fontsize=12, fontweight='bold',
                ha='center', va='center', color='#1565C0')

    # Inputs display
    inputs_text = r"$N_c = 3$   $N_f = 3$   $\chi = 4$"
    ax_main.text(1.5, y1-0.25, inputs_text, fontsize=11, ha='center', va='center')

    # Arrow
    ax_main.annotate('', xy=(3.2, y1), xytext=(2.8, y1),
                    arrowprops=dict(arrowstyle='->', color='#333', lw=2))

    # Box: Derived Constants
    box2 = FancyBboxPatch((3.4, y1-0.4), 2.8, 0.8, boxstyle="round,pad=0.05",
                          facecolor='#E8F5E9', edgecolor='#2E7D32', linewidth=2)
    ax_main.add_patch(box2)
    ax_main.text(4.8, y1+0.15, "DERIVED", fontsize=10, fontweight='bold',
                ha='center', va='center', color='#2E7D32')
    ax_main.text(4.8, y1-0.2, r"$b_0 = \frac{9}{4\pi}$   $(N_c^2-1)^2 = 64$",
                fontsize=10, ha='center', va='center')

    # Arrow
    ax_main.annotate('', xy=(6.7, y1), xytext=(6.3, y1),
                    arrowprops=dict(arrowstyle='->', color='#333', lw=2))

    # Box: UV Coupling
    box3 = FancyBboxPatch((6.9, y1-0.4), 2.6, 0.8, boxstyle="round,pad=0.05",
                          facecolor='#FFF3E0', edgecolor='#E65100', linewidth=2)
    ax_main.add_patch(box3)
    ax_main.text(8.2, y1+0.15, "UV COUPLING", fontsize=10, fontweight='bold',
                ha='center', va='center', color='#E65100')
    ax_main.text(8.2, y1-0.2, r"$\alpha_s(M_P)^{-1} = 64$",
                fontsize=12, ha='center', va='center')

    # --- Row 2: The Key Equations ---
    y2 = 3.2

    # Large central equation box
    box_eq = FancyBboxPatch((1.5, y2-0.6), 7, 1.2, boxstyle="round,pad=0.1",
                            facecolor='#F3E5F5', edgecolor='#7B1FA2', linewidth=3)
    ax_main.add_patch(box_eq)

    # Main equations
    ax_main.text(5, y2+0.35, "BOOTSTRAP EQUATIONS", fontsize=12, fontweight='bold',
                ha='center', va='center', color='#7B1FA2')

    eq_text = (r"$\sqrt{\sigma} = \frac{\hbar c}{R_{\mathrm{stella}}}$" +
               r"$\qquad$" +
               r"$\frac{R_{\mathrm{stella}}}{\ell_P} = \exp\left(\frac{128\pi}{9}\right)$")
    ax_main.text(5, y2-0.1, eq_text, fontsize=14, ha='center', va='center')

    # Reference to propositions
    ax_main.text(2.0, y2-0.45, "Prop 0.0.17j", fontsize=9, ha='center', color='#555')
    ax_main.text(7.2, y2-0.45, "Prop 0.0.17q, 0.0.17y", fontsize=9, ha='center', color='#555')

    # --- Row 3: Results ---
    y3 = 1.8

    # Arrow down
    ax_main.annotate('', xy=(5, y3+0.5), xytext=(5, y2-0.7),
                    arrowprops=dict(arrowstyle='->', color='#333', lw=2))

    # One-loop result
    box_ol = FancyBboxPatch((1.2, y3-0.35), 2.6, 0.7, boxstyle="round,pad=0.05",
                            facecolor='#FFECB3', edgecolor='#FF8F00', linewidth=2)
    ax_main.add_patch(box_ol)
    ax_main.text(2.5, y3+0.1, "ONE-LOOP", fontsize=9, fontweight='bold',
                ha='center', va='center', color='#FF8F00')
    ax_main.text(2.5, y3-0.15, r"$\sqrt{\sigma} = 481$ MeV", fontsize=12,
                ha='center', va='center')

    # Arrow with correction
    ax_main.annotate('', xy=(4.3, y3), xytext=(3.9, y3),
                    arrowprops=dict(arrowstyle='->', color='#D32F2F', lw=2))
    ax_main.text(4.1, y3+0.25, "−9.6%", fontsize=10, ha='center', color='#D32F2F',
                fontweight='bold')
    ax_main.text(4.1, y3-0.3, "Prop 0.0.17z", fontsize=8, ha='center', color='#555')

    # Corrected result
    box_corr = FancyBboxPatch((4.5, y3-0.35), 2.6, 0.7, boxstyle="round,pad=0.05",
                              facecolor='#E1BEE7', edgecolor='#7B1FA2', linewidth=2)
    ax_main.add_patch(box_corr)
    ax_main.text(5.8, y3+0.1, "CORRECTED", fontsize=9, fontweight='bold',
                ha='center', va='center', color='#7B1FA2')
    ax_main.text(5.8, y3-0.15, r"$\sqrt{\sigma} = 435$ MeV", fontsize=12,
                ha='center', va='center')

    # Arrow to observation
    ax_main.annotate('', xy=(7.6, y3), xytext=(7.2, y3),
                    arrowprops=dict(arrowstyle='<->', color='#2E7D32', lw=2))

    # Observation
    box_obs = FancyBboxPatch((7.8, y3-0.35), 2.0, 0.7, boxstyle="round,pad=0.05",
                             facecolor='#C8E6C9', edgecolor='#2E7D32', linewidth=2)
    ax_main.add_patch(box_obs)
    ax_main.text(8.8, y3+0.1, "OBSERVED", fontsize=9, fontweight='bold',
                ha='center', va='center', color='#2E7D32')
    ax_main.text(8.8, y3-0.15, r"$440 \pm 30$ MeV", fontsize=11,
                ha='center', va='center')

    # Final verdict
    ax_main.text(5, 0.95, r"$\mathbf{Agreement:\ 0.17\sigma}$ — Topology predicts QCD!",
                fontsize=14, fontweight='bold', ha='center', va='center',
                color='#1B5E20',
                bbox=dict(boxstyle='round', facecolor='#A5D6A7', edgecolor='#1B5E20', lw=2))

    # =========================================================================
    # STELLA OCTANGULA (bottom left)
    # =========================================================================

    ax_stella.set_title("Stella Octangula\n(χ = 4)", fontsize=11, fontweight='bold')

    # Create stella octangula vertices
    a = 1
    # T+ tetrahedron
    t1_verts = np.array([
        [a, a, a], [-a, -a, a], [-a, a, -a], [a, -a, -a]
    ])
    # T- tetrahedron
    t2_verts = np.array([
        [-a, -a, -a], [a, a, -a], [a, -a, a], [-a, a, a]
    ])

    # T+ faces
    t1_faces = [
        [t1_verts[0], t1_verts[1], t1_verts[2]],
        [t1_verts[0], t1_verts[1], t1_verts[3]],
        [t1_verts[0], t1_verts[2], t1_verts[3]],
        [t1_verts[1], t1_verts[2], t1_verts[3]]
    ]
    # T- faces
    t2_faces = [
        [t2_verts[0], t2_verts[1], t2_verts[2]],
        [t2_verts[0], t2_verts[1], t2_verts[3]],
        [t2_verts[0], t2_verts[2], t2_verts[3]],
        [t2_verts[1], t2_verts[2], t2_verts[3]]
    ]

    ax_stella.add_collection3d(Poly3DCollection(t1_faces, alpha=0.6,
                               facecolor='#2196F3', edgecolor='#0D47A1', linewidth=1))
    ax_stella.add_collection3d(Poly3DCollection(t2_faces, alpha=0.6,
                               facecolor='#FF5722', edgecolor='#BF360C', linewidth=1))

    ax_stella.set_xlim([-1.5, 1.5])
    ax_stella.set_ylim([-1.5, 1.5])
    ax_stella.set_zlim([-1.5, 1.5])
    ax_stella.set_box_aspect([1, 1, 1])
    ax_stella.axis('off')

    # =========================================================================
    # SCALE LADDER (bottom middle)
    # =========================================================================

    ax_scales.set_title("Scale Hierarchy", fontsize=11, fontweight='bold')

    # Create vertical scale ladder
    scales = [
        (r"$\ell_P$", 0, "#9C27B0"),
        (r"$R_{\mathrm{stella}}$", 19.4, "#FF9800"),
        (r"$1/\sqrt{\sigma}$", 19.4, "#4CAF50"),
    ]

    y_pos = np.array([s[1] for s in scales])

    for i, (label, val, color) in enumerate(scales):
        ax_scales.barh(i, val, color=color, height=0.6, alpha=0.8)
        ax_scales.text(val + 0.5, i, f"{val}", va='center', fontsize=10)
        ax_scales.text(-1, i, label, va='center', ha='right', fontsize=12)

    ax_scales.set_xlim(-5, 25)
    ax_scales.set_xlabel(r"$\log_{10}$(scale / ℓ$_P$)", fontsize=10)
    ax_scales.set_yticks([])
    ax_scales.spines['top'].set_visible(False)
    ax_scales.spines['right'].set_visible(False)
    ax_scales.spines['left'].set_visible(False)

    # Annotation for the hierarchy
    ax_scales.annotate('', xy=(19.4, 0.5), xytext=(0, 0.5),
                      arrowprops=dict(arrowstyle='<->', color='#D32F2F', lw=2))
    ax_scales.text(10, 0.75, r"$\exp(128\pi/9) \approx 10^{19}$",
                  ha='center', fontsize=10, color='#D32F2F')

    # =========================================================================
    # CORRECTION PIE (bottom right)
    # =========================================================================

    ax_pie.set_title("Non-Perturbative\nCorrections (Prop 0.0.17z)", fontsize=11, fontweight='bold')

    corrections = ['Gluon\nCondensate', 'Threshold\nMatching', 'Two-loop', 'Instantons']
    sizes = [3.0, 3.0, 2.0, 1.6]
    colors_pie = ['#EF5350', '#FF7043', '#FFA726', '#FFCA28']
    explode = (0.05, 0.05, 0.05, 0.05)

    wedges, texts, autotexts = ax_pie.pie(sizes, explode=explode, labels=corrections,
                                          colors=colors_pie, autopct='%1.1f%%',
                                          startangle=90, textprops={'fontsize': 8})

    for autotext in autotexts:
        autotext.set_fontsize(9)
        autotext.set_fontweight('bold')

    ax_pie.text(0, -1.4, f"Total: −{sum(sizes):.1f}%", ha='center',
               fontsize=11, fontweight='bold', color='#C62828')

    # =========================================================================
    # SAVE
    # =========================================================================

    import os
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_dir = os.path.join(script_dir, '..', 'plots')
    os.makedirs(output_dir, exist_ok=True)

    png_path = os.path.join(output_dir, 'bootstrap_qcd_scale_determination.png')
    pdf_path = os.path.join(output_dir, 'bootstrap_qcd_scale_determination.pdf')

    plt.savefig(png_path, dpi=200, bbox_inches='tight', facecolor='white')
    plt.savefig(pdf_path, bbox_inches='tight', facecolor='white')
    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")

    plt.show()


if __name__ == "__main__":
    create_bootstrap_visualization()
