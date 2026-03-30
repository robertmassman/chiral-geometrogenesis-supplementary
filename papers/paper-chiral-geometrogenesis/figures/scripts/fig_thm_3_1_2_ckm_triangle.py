#!/usr/bin/env python3
"""
Figure 5: CKM Unitarity Triangle

Generates publication-quality figure showing the CKM unitarity triangle
with geometric predictions compared to PDG 2024 measurements.

Geometric predictions (from Extension-3.1.2b):
- rho_bar = 0.159 (from tan(beta)/(tan(beta)+tan(gamma)))
- eta_bar = 0.348 (from rho_bar * tan(gamma))

PDG 2024 values: rho_bar = 0.1581 +/- 0.0092, eta_bar = 0.3548 +/- 0.0072

The unitarity condition: V_ud*V_ub* + V_cd*V_cb* + V_td*V_tb* = 0
forms a triangle in the complex plane.

Output: fig_thm_3_1_2_ckm_triangle.pdf, fig_thm_3_1_2_ckm_triangle.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Arc, Ellipse
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


def create_figure_5():
    """
    Show CKM unitarity triangle with geometric predictions vs PDG 2024.

    Geometric predictions:
    - rho_bar = 0.159 (from tan(beta)/(tan(beta)+tan(gamma)))
    - eta_bar = 0.348 (from rho_bar * tan(gamma))

    PDG 2024 values: rho_bar = 0.1581 +/- 0.0092, eta_bar = 0.3548 +/- 0.0072
    """
    fig, ax = plt.subplots(figsize=(5, 4))

    # Geometric predictions from stella-24-cell connection (Extension 3.1.2b)
    rho_bar_geo = 0.159
    eta_bar_geo = 0.348

    # PDG 2024 values with uncertainties
    rho_bar_pdg = 0.1581
    eta_bar_pdg = 0.3548
    rho_bar_err = 0.0092
    eta_bar_err = 0.0072

    # Use geometric prediction for the main triangle
    rho_bar = rho_bar_geo
    eta_bar = eta_bar_geo

    # Unitarity triangle vertices
    # A = (0, 0), B = (1, 0), C = (rho_bar, eta_bar)
    A = np.array([0, 0])
    B = np.array([1, 0])
    C = np.array([rho_bar, eta_bar])

    vertices = np.array([A, B, C])

    # Draw triangle
    triangle = plt.Polygon(vertices, fill=False, edgecolor='blue', lw=2)
    ax.add_patch(triangle)
    ax.fill(vertices[:, 0], vertices[:, 1], alpha=0.2, color='blue')

    # Mark vertices
    ax.scatter(*A, c='red', s=100, zorder=5)
    ax.scatter(*B, c='red', s=100, zorder=5)
    ax.scatter(*C, c='green', s=150, marker='*', zorder=5)

    # Labels for vertices
    ax.text(-0.05, -0.05, '(0, 0)', fontsize=10)
    ax.text(1.02, -0.05, '(1, 0)', fontsize=10)
    ax.text(rho_bar + 0.03, eta_bar + 0.02,
            f'Geometric:\n$({rho_bar_geo:.3f}, {eta_bar_geo:.3f})$',
            fontsize=9, color='green')

    # Add PDG 2024 error ellipse (1-sigma)
    pdg_ellipse = Ellipse((rho_bar_pdg, eta_bar_pdg),
                          width=2*rho_bar_err, height=2*eta_bar_err,
                          fill=False, edgecolor='red', linestyle='--', lw=1.5,
                          label=f'PDG 2024: ({rho_bar_pdg:.4f}, {eta_bar_pdg:.4f})')
    ax.add_patch(pdg_ellipse)
    ax.scatter(rho_bar_pdg, eta_bar_pdg, c='red', s=50, marker='x', zorder=6,
               label='PDG 2024 central')

    # Calculate angles using dot product formula for accuracy
    # Interior angle at each vertex

    # gamma at origin (0,0): angle between edges to (1,0) and to (rho_bar, eta_bar)
    vec_AB = B - A  # to (1,0)
    vec_AC = C - A  # to (rho_bar, eta_bar)
    cos_gamma = np.dot(vec_AB, vec_AC) / (np.linalg.norm(vec_AB) * np.linalg.norm(vec_AC))
    gamma_rad = np.arccos(cos_gamma)
    gamma_deg = np.degrees(gamma_rad)

    # beta at (1,0): angle between edges to (0,0) and to (rho_bar, eta_bar)
    vec_BA = A - B  # to (0,0)
    vec_BC = C - B  # to (rho_bar, eta_bar)
    cos_beta = np.dot(vec_BA, vec_BC) / (np.linalg.norm(vec_BA) * np.linalg.norm(vec_BC))
    beta_rad = np.arccos(cos_beta)
    beta_deg = np.degrees(beta_rad)

    # alpha at apex (rho_bar, eta_bar): angle between edges to (0,0) and to (1,0)
    vec_CA = A - C  # to (0,0)
    vec_CB = B - C  # to (1,0)
    cos_alpha = np.dot(vec_CA, vec_CB) / (np.linalg.norm(vec_CA) * np.linalg.norm(vec_CB))
    alpha_rad = np.arccos(cos_alpha)
    alpha_deg = np.degrees(alpha_rad)

    # Draw angle arcs
    arc_radius = 0.08

    # gamma arc at origin (from x-axis=0 deg to line AC)
    angle_AC = np.degrees(np.arctan2(vec_AC[1], vec_AC[0]))
    gamma_arc = Arc(A, 2*arc_radius, 2*arc_radius, angle=0,
                    theta1=0, theta2=angle_AC,
                    color='green', lw=2)
    ax.add_patch(gamma_arc)
    ax.text(0.10, 0.025, r'$\gamma$', fontsize=11, color='green', fontweight='bold')

    # beta arc at (1,0) - from line BC to line BA (which is at 180 deg)
    angle_BC = np.degrees(np.arctan2(vec_BC[1], vec_BC[0]))
    beta_arc = Arc(B, 2*arc_radius, 2*arc_radius, angle=0,
                   theta1=angle_BC, theta2=180,
                   color='#e67e22', lw=2)
    ax.add_patch(beta_arc)
    ax.text(0.82, 0.01, r'$\beta$', fontsize=11, color='#e67e22', fontweight='bold')

    # alpha arc at apex - from line CB to line CA
    angle_CB = np.degrees(np.arctan2(vec_CB[1], vec_CB[0]))  # negative, pointing down-right
    angle_CA = np.degrees(np.arctan2(vec_CA[1], vec_CA[0]))  # negative, pointing down-left
    # Both angles are negative (below horizontal). We want the arc going through
    # the interior which is the shorter path between them.
    alpha_arc = Arc(C, 2*arc_radius, 2*arc_radius, angle=0,
                    theta1=angle_CA, theta2=angle_CB,
                    color='purple', lw=2)
    ax.add_patch(alpha_arc)
    ax.text(rho_bar + 0.02, eta_bar - 0.12, r'$\alpha$', fontsize=11, color='purple', fontweight='bold')

    # Add formula box
    textstr = r'$V_{ud}V_{ub}^* + V_{cd}V_{cb}^* + V_{td}V_{tb}^* = 0$'
    ax.text(0.5, -0.12, textstr, fontsize=10, ha='center',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    # Add angle values in a small legend box (use proper degree symbol)
    angle_text = r'$\alpha = %.1f^\circ$' % alpha_deg + '\n' + \
                 r'$\beta = %.1f^\circ$' % beta_deg + '\n' + \
                 r'$\gamma = %.1f^\circ$' % gamma_deg
    ax.text(0.72, 0.38, angle_text, fontsize=9, va='top',
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9, edgecolor='gray'))

    ax.set_xlim(-0.1, 1.15)
    ax.set_ylim(-0.18, 0.52)
    ax.set_aspect('equal')
    ax.set_xlabel(r'$\bar{\rho}$')
    ax.set_ylabel(r'$\bar{\eta}$')
    ax.set_title('CKM Unitarity Triangle (Geometric Prediction)')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    for ext in ['pdf', 'png']:
        plt.savefig(f'{OUTPUT_DIR}/fig_thm_3_1_2_ckm_triangle.{ext}')
    plt.close()
    print(f"✓ Figure 5 saved to {OUTPUT_DIR}/fig_thm_3_1_2_ckm_triangle.pdf")
    print(f"✓ Figure 5 saved to {OUTPUT_DIR}/fig_thm_3_1_2_ckm_triangle.png")


if __name__ == '__main__':
    create_figure_5()
