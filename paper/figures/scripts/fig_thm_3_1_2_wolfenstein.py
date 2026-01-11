#!/usr/bin/env python3
"""
Figure 4: Wolfenstein Parameter from Golden Ratio

Generates publication-quality figure showing the geometric derivation of
the Wolfenstein parameter: λ = (1/φ³)sin(72°)

Two panels:
- Panel (a): Pentagon geometry showing the golden ratio and 72° angle
- Panel (b): Plot showing geometric prediction vs PDG measurement

Source Theorems:
- Theorem 3.1.2: Mass hierarchy from geometry

Output: fig_thm_3_1_2_wolfenstein.pdf, fig_thm_3_1_2_wolfenstein.png
"""

import numpy as np
import matplotlib.pyplot as plt
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'serif',
    'font.serif': ['Times New Roman', 'DejaVu Serif'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
    'text.usetex': False,
    'mathtext.fontset': 'cm',
})

# ============================================================================
# PHYSICAL CONSTANTS AND PARAMETERS
# ============================================================================

# Golden ratio
PHI = (1 + np.sqrt(5)) / 2  # 1.618034...

# Wolfenstein parameter from geometry
LAMBDA_GEOMETRIC = (1 / PHI**3) * np.sin(np.radians(72))  # 0.2245
LAMBDA_PDG = 0.22650  # PDG 2024: 0.22650 ± 0.00048


def create_figure_4():
    """
    Show the geometric derivation of λ = (1/φ³)sin(72°).
    """
    fig, axes = plt.subplots(1, 2, figsize=(7, 3.5))

    # Panel (a): Pentagon with golden ratio
    ax1 = axes[0]

    # Draw regular pentagon
    angles = np.linspace(np.pi/2, np.pi/2 + 2*np.pi, 6)
    x_pent = np.cos(angles)
    y_pent = np.sin(angles)
    ax1.plot(x_pent, y_pent, 'b-', lw=2)
    ax1.fill(x_pent, y_pent, alpha=0.2, color='blue')

    # Draw diagonals to show golden ratio
    ax1.plot([x_pent[0], x_pent[2]], [y_pent[0], y_pent[2]], 'r--', lw=1.5)
    ax1.plot([x_pent[0], x_pent[3]], [y_pent[0], y_pent[3]], 'r--', lw=1.5)

    # Mark 72 degree angle at the apex (top vertex)
    # The apex is at x_pent[0], y_pent[0] which is at angle 90 degrees
    # The diagonals go to vertices at indices 2 and 3
    apex = np.array([x_pent[0], y_pent[0]])
    v2 = np.array([x_pent[2], y_pent[2]])
    v3 = np.array([x_pent[3], y_pent[3]])

    # Calculate angles of diagonals from apex
    angle_to_v2 = np.arctan2(v2[1] - apex[1], v2[0] - apex[0])
    angle_to_v3 = np.arctan2(v3[1] - apex[1], v3[0] - apex[0])

    # Draw arc at apex between the two diagonals
    theta = np.linspace(angle_to_v2, angle_to_v3, 30)
    r_arc = 0.40
    ax1.plot(apex[0] + r_arc * np.cos(theta), apex[1] + r_arc * np.sin(theta), 'g-', lw=2)
    # Center the label at the midpoint of the arc
    mid_angle = (angle_to_v2 + angle_to_v3) / 2
    label_r = 0.60
    ax1.text(apex[0] + label_r * np.cos(mid_angle), apex[1] + label_r * np.sin(mid_angle),
             '72°', fontsize=10, color='green', ha='center', va='center')

    # Label golden ratio in a box centered below the pentagon
    ax1.text(0, -1.2, r'$\varphi = \frac{1+\sqrt{5}}{2}$', fontsize=11,
             ha='center', va='center',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.9, edgecolor='black'))

    ax1.set_xlim(-1.4, 1.4)
    ax1.set_ylim(-1.4, 1.4)
    ax1.set_aspect('equal')
    ax1.axis('off')
    ax1.set_title('(a) Pentagon & Golden Ratio')

    # Panel (b): λ derivation
    ax2 = axes[1]

    # Show the formula components
    phi_vals = np.linspace(1.5, 1.8, 100)
    lambda_func = (1 / phi_vals**3) * np.sin(np.radians(72))

    ax2.plot(phi_vals, lambda_func, 'b-', lw=2, label=r'$\lambda = \frac{\sin 72°}{\varphi^3}$')
    ax2.axhline(LAMBDA_PDG, color='red', ls='--', lw=2, label=f'PDG: {LAMBDA_PDG:.4f}')
    ax2.axhline(LAMBDA_GEOMETRIC, color='green', ls=':', lw=2,
                label=f'Geometric: {LAMBDA_GEOMETRIC:.4f}')
    ax2.axvline(PHI, color='purple', ls='-.', lw=1.5, alpha=0.7)

    ax2.scatter([PHI], [LAMBDA_GEOMETRIC], c='green', s=100, zorder=5, marker='*')

    # Agreement annotation
    agreement = 100 * abs(LAMBDA_GEOMETRIC - LAMBDA_PDG) / LAMBDA_PDG
    ax2.text(1.55, 0.21, f'Agreement:\n{agreement:.2f}%', fontsize=9,
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    ax2.set_xlabel(r'Golden ratio $\varphi$')
    ax2.set_ylabel(r'Wolfenstein $\lambda$')
    ax2.set_title('(b) Geometric Prediction')
    ax2.legend(loc='upper right', fontsize=8)
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(1.5, 1.8)
    ax2.set_ylim(0.18, 0.28)

    plt.tight_layout()

    for ext in ['pdf', 'png']:
        plt.savefig(f'{OUTPUT_DIR}/fig_thm_3_1_2_wolfenstein.{ext}')
    plt.close()
    print(f"✓ Figure 4 saved to {OUTPUT_DIR}/fig_thm_3_1_2_wolfenstein.pdf")
    print(f"✓ Figure 4 saved to {OUTPUT_DIR}/fig_thm_3_1_2_wolfenstein.png")


if __name__ == '__main__':
    create_figure_4()
