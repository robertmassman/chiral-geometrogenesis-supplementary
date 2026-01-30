#!/usr/bin/env python3
"""
Single Image: Bootstrap & QCD Scale Determination
==================================================

One focused visualization showing the key result:
Topology → exp(128π/9) → QCD Scale
"""

import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import os

# Constants
N_c = 3
exponent = 128 * np.pi / 9  # ≈ 44.68
hierarchy = np.exp(exponent)  # ≈ 2.5 × 10^19

def create_single_image():
    """Create one unified image showing the bootstrap result."""

    fig = plt.figure(figsize=(14, 8), facecolor='#0a0a1a')
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, 14)
    ax.set_ylim(0, 8)
    ax.set_facecolor('#0a0a1a')
    ax.axis('off')

    # =========================================================================
    # TITLE
    # =========================================================================
    ax.text(7, 7.5, "Bootstrap & QCD Scale Determination",
            fontsize=24, fontweight='bold', ha='center', va='center',
            color='white')
    ax.text(7, 6.9, "Group 1: Props 0.0.17j, 0.0.17q, 0.0.17y, 0.0.17z",
            fontsize=12, ha='center', va='center', color='#888888')

    # =========================================================================
    # LEFT: STELLA OCTANGULA (3D inset)
    # =========================================================================
    ax_stella = fig.add_axes([0.02, 0.35, 0.25, 0.45], projection='3d',
                             facecolor='#0a0a1a')

    # Create stella octangula
    a = 1
    t1_verts = np.array([[a,a,a], [-a,-a,a], [-a,a,-a], [a,-a,-a]])
    t2_verts = np.array([[-a,-a,-a], [a,a,-a], [a,-a,a], [-a,a,a]])

    t1_faces = [[t1_verts[0], t1_verts[1], t1_verts[2]],
                [t1_verts[0], t1_verts[1], t1_verts[3]],
                [t1_verts[0], t1_verts[2], t1_verts[3]],
                [t1_verts[1], t1_verts[2], t1_verts[3]]]
    t2_faces = [[t2_verts[0], t2_verts[1], t2_verts[2]],
                [t2_verts[0], t2_verts[1], t2_verts[3]],
                [t2_verts[0], t2_verts[2], t2_verts[3]],
                [t2_verts[1], t2_verts[2], t2_verts[3]]]

    ax_stella.add_collection3d(Poly3DCollection(t1_faces, alpha=0.7,
                               facecolor='#4FC3F7', edgecolor='#0288D1', linewidth=1.5))
    ax_stella.add_collection3d(Poly3DCollection(t2_faces, alpha=0.7,
                               facecolor='#FF7043', edgecolor='#E64A19', linewidth=1.5))

    ax_stella.set_xlim([-1.5, 1.5])
    ax_stella.set_ylim([-1.5, 1.5])
    ax_stella.set_zlim([-1.5, 1.5])
    ax_stella.set_box_aspect([1, 1, 1])
    ax_stella.axis('off')
    ax_stella.view_init(elev=20, azim=45)

    # Label under stella
    ax.text(1.8, 2.2, "Stella Octangula", fontsize=14, fontweight='bold',
            ha='center', color='white')
    ax.text(1.8, 1.8, r"$\chi = 4$", fontsize=16, ha='center', color='#4FC3F7')

    # =========================================================================
    # CENTER: THE KEY EQUATION
    # =========================================================================

    # Big central equation box
    from matplotlib.patches import FancyBboxPatch
    box = FancyBboxPatch((3.5, 3.2), 7, 2.6, boxstyle="round,pad=0.1",
                         facecolor='#1a1a2e', edgecolor='#4FC3F7', linewidth=3)
    ax.add_patch(box)

    # The hierarchy equation
    ax.text(7, 5.3, r"$\frac{R_{\mathrm{stella}}}{\ell_P} = \exp\left(\frac{128\pi}{9}\right)$",
            fontsize=28, ha='center', va='center', color='white')

    # Numerical value
    ax.text(7, 4.3, r"$= 2.5 \times 10^{19}$",
            fontsize=22, ha='center', va='center', color='#FFD54F')

    # Sub-equation: string tension
    ax.text(7, 3.5, r"$\sqrt{\sigma} = \hbar c / R_{\mathrm{stella}} = 440\ \mathrm{MeV}$",
            fontsize=16, ha='center', va='center', color='#81C784')

    # =========================================================================
    # RIGHT: SCALE VISUALIZATION
    # =========================================================================

    # Vertical scale bar
    x_bar = 12
    y_bottom = 1.5
    y_top = 6.0
    bar_width = 0.4

    # Create gradient bar (Planck to QCD)
    n_segments = 50
    cmap = plt.cm.plasma
    for i in range(n_segments):
        y0 = y_bottom + i * (y_top - y_bottom) / n_segments
        y1 = y_bottom + (i + 1) * (y_top - y_bottom) / n_segments
        color = cmap(i / n_segments)
        ax.fill_between([x_bar - bar_width/2, x_bar + bar_width/2],
                       [y0, y0], [y1, y1], color=color)

    # Labels on scale
    ax.text(x_bar, y_bottom - 0.3, r"$\ell_P$", fontsize=14, ha='center',
            va='top', color='#9C27B0', fontweight='bold')
    ax.text(x_bar + 0.8, y_bottom, r"$10^{-35}$ m", fontsize=10, ha='left',
            va='center', color='#888')

    ax.text(x_bar, y_top + 0.3, r"$R_{\mathrm{stella}}$", fontsize=14, ha='center',
            va='bottom', color='#FFD54F', fontweight='bold')
    ax.text(x_bar + 0.8, y_top, r"$0.45$ fm", fontsize=10, ha='left',
            va='center', color='#888')

    # Arrow showing hierarchy
    ax.annotate('', xy=(x_bar - 0.8, y_top), xytext=(x_bar - 0.8, y_bottom),
               arrowprops=dict(arrowstyle='<->', color='white', lw=2))
    ax.text(x_bar - 1.1, (y_top + y_bottom)/2, r"$10^{19}$", fontsize=16,
            ha='right', va='center', color='white', fontweight='bold', rotation=90)

    # =========================================================================
    # BOTTOM: THE RESULT
    # =========================================================================

    # Result box
    result_box = FancyBboxPatch((2.5, 0.4), 9, 1.2, boxstyle="round,pad=0.05",
                                facecolor='#1B5E20', edgecolor='#4CAF50', linewidth=2)
    ax.add_patch(result_box)

    ax.text(7, 1.0, r"Topology $\rightarrow$ QCD Scale:  $\sqrt{\sigma}_{\mathrm{predicted}} = 435$ MeV  vs  $\sqrt{\sigma}_{\mathrm{observed}} = 440 \pm 30$ MeV",
            fontsize=13, ha='center', va='center', color='white')
    ax.text(7, 0.55, r"Agreement: $\mathbf{0.17\sigma}$ — QCD emerges from pure geometry",
            fontsize=12, ha='center', va='center', color='#A5D6A7', fontweight='bold')

    # =========================================================================
    # TOPOLOGICAL INPUTS (top left area)
    # =========================================================================
    ax.text(1.8, 6.3, "Topological Inputs:", fontsize=11, ha='center',
            color='#888', fontweight='bold')
    ax.text(1.8, 5.85, r"$N_c = 3$   $N_f = 3$", fontsize=12, ha='center', color='#4FC3F7')
    ax.text(1.8, 5.45, r"$b_0 = 9/(4\pi)$", fontsize=12, ha='center', color='#4FC3F7')
    ax.text(1.8, 5.05, r"$\alpha_s^{-1}(M_P) = 64$", fontsize=12, ha='center', color='#4FC3F7')

    # =========================================================================
    # SAVE
    # =========================================================================
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_dir = os.path.join(script_dir, '..', 'plots')
    os.makedirs(output_dir, exist_ok=True)

    png_path = os.path.join(output_dir, 'bootstrap_qcd_scale.png')
    pdf_path = os.path.join(output_dir, 'bootstrap_qcd_scale.pdf')

    plt.savefig(png_path, dpi=200, bbox_inches='tight', facecolor='#0a0a1a')
    plt.savefig(pdf_path, bbox_inches='tight', facecolor='#0a0a1a')
    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")

    plt.close()

if __name__ == "__main__":
    create_single_image()
