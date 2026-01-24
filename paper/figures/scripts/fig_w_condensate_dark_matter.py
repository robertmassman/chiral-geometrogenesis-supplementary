#!/usr/bin/env python3
"""
W-Condensate Dark Matter Visualization for Section 4.9.6

Creates a 4-panel figure showing:
(a) Stella octangula with RGB vertices and W vertex at center
(b) SU(3) weight space projection showing W at origin (color singlet)
(c) Asymmetric Dark Matter production chain diagram
(d) Direct detection cross-section vs. current bounds (LZ, DARWIN)

Based on Prediction-8.3.1-W-Condensate-Dark-Matter.md

Output: fig_w_condensate_dark_matter.pdf and fig_w_condensate_dark_matter.png

Usage:
    python fig_w_condensate_dark_matter.py
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Circle, Polygon, Wedge
from matplotlib.lines import Line2D
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import mpl_toolkits.mplot3d.art3d as art3d
from pathlib import Path

# Output directory
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

# Color scheme matching existing figures
COLORS = {
    'R': '#e74c3c',      # Red vertex
    'G': '#27ae60',      # Green vertex
    'B': '#3498db',      # Blue vertex
    'W': '#9b59b6',      # W vertex (purple for dark sector)
    'gold': '#f1c40f',   # Gold for singlet
    'dark': '#2c3e50',   # Dark text
    'light_blue': '#3498db',
    'light_red': '#e74c3c',
}


def panel_a_stella_with_w(ax):
    """
    Panel (a): Stella octangula showing RGB vertices mapping to color triplet
    and W vertex at the geometric center.
    """
    # Tetrahedron T+ vertices (normalized to unit sphere for projection)
    sqrt3 = np.sqrt(3)
    T_plus = np.array([
        [1, 1, 1],      # W apex
        [1, -1, -1],    # R
        [-1, 1, -1],    # G
        [-1, -1, 1]     # B
    ]) / sqrt3

    # Tetrahedron T- vertices (dual)
    T_minus = np.array([
        [-1, -1, -1],   # W-bar apex
        [-1, 1, 1],     # R-bar
        [1, -1, 1],     # G-bar
        [1, 1, -1]      # B-bar
    ]) / sqrt3

    # Define faces for each tetrahedron
    def get_tetra_faces(verts):
        return [
            [verts[0], verts[1], verts[2]],
            [verts[0], verts[1], verts[3]],
            [verts[0], verts[2], verts[3]],
            [verts[1], verts[2], verts[3]]
        ]

    # Plot T+ (blue, transparent)
    faces_plus = get_tetra_faces(T_plus)
    poly_plus = Poly3DCollection(faces_plus, alpha=0.1, facecolor='blue',
                                  edgecolor='blue', linewidth=0.8)
    ax.add_collection3d(poly_plus)

    # Plot T- (red, transparent)
    faces_minus = get_tetra_faces(T_minus)
    poly_minus = Poly3DCollection(faces_minus, alpha=0.1, facecolor='red',
                                   edgecolor='red', linewidth=0.8)
    ax.add_collection3d(poly_minus)

    # Draw edges
    edges = [(0,1), (0,2), (0,3), (1,2), (2,3), (3,1)]
    for i, j in edges:
        ax.plot3D(*zip(T_plus[i], T_plus[j]), 'b-', linewidth=1.5, alpha=0.7)
        ax.plot3D(*zip(T_minus[i], T_minus[j]), 'r--', linewidth=1.5, alpha=0.7)

    # Plot the CENTER - W domain center (origin)
    ax.scatter(0, 0, 0, c=COLORS['W'], s=400, marker='o', edgecolor='black',
               linewidth=2, zorder=10, label='W (singlet)')

    # Plot RGB vertices (T+ base)
    ax.scatter(*T_plus[1], c=COLORS['R'], s=200, edgecolor='black', linewidth=1.5, zorder=5)
    ax.scatter(*T_plus[2], c=COLORS['G'], s=200, edgecolor='black', linewidth=1.5, zorder=5)
    ax.scatter(*T_plus[3], c=COLORS['B'], s=200, edgecolor='black', linewidth=1.5, zorder=5)

    # Plot apex vertices (W and W-bar)
    ax.scatter(*T_plus[0], c=COLORS['gold'], s=150, marker='*', edgecolor='black', linewidth=1, zorder=5)
    ax.scatter(*T_minus[0], c=COLORS['gold'], s=150, marker='*', edgecolor='black', linewidth=1, zorder=5)

    # Draw dotted lines from RGB vertices to center (W domain)
    for v, c in zip([T_plus[1], T_plus[2], T_plus[3]], [COLORS['R'], COLORS['G'], COLORS['B']]):
        ax.plot3D([v[0], 0], [v[1], 0], [v[2], 0], color=c, linestyle=':', linewidth=2, alpha=0.6)

    # Labels with adjusted positions
    offset = 0.15
    ax.text(0 + 0.12, 0, 0 + 0.12, 'W', fontsize=11, fontweight='bold', color=COLORS['W'])
    ax.text(T_plus[1][0]+offset, T_plus[1][1], T_plus[1][2]-offset, 'R', fontsize=10, fontweight='bold', color=COLORS['R'])
    ax.text(T_plus[2][0]-offset*1.5, T_plus[2][1]+offset, T_plus[2][2], 'G', fontsize=10, fontweight='bold', color=COLORS['G'])
    ax.text(T_plus[3][0], T_plus[3][1]-offset, T_plus[3][2]+offset, 'B', fontsize=10, fontweight='bold', color=COLORS['B'])

    # Set viewing angle and limits
    ax.set_box_aspect([1,1,1])
    limit = 0.8
    ax.set_xlim([-limit, limit])
    ax.set_ylim([-limit, limit])
    ax.set_zlim([-limit, limit])
    ax.view_init(elev=20, azim=35)

    # Remove axis labels for cleaner look
    ax.set_xticklabels([])
    ax.set_yticklabels([])
    ax.set_zticklabels([])
    ax.set_xlabel('')
    ax.set_ylabel('')
    ax.set_zlabel('')

    ax.set_title('(a) Stella Octangula:\nRGB + W vertex structure', fontsize=10, fontweight='bold', pad=5)


def panel_b_weight_space(ax):
    """
    Panel (b): SU(3) weight space projection showing W at origin (color singlet).
    Shows the fundamental triplet R, G, B and the W singlet at center.
    """
    # SU(3) weight coordinates for fundamental 3
    # T_3 and T_8 coordinates (Gell-Mann convention)
    sqrt3 = np.sqrt(3)

    # Fundamental triplet vertices in weight space
    R = np.array([0.5, 1/(2*sqrt3)])      # (1/2, 1/2√3)
    G = np.array([-0.5, 1/(2*sqrt3)])     # (-1/2, 1/2√3)
    B = np.array([0, -1/sqrt3])           # (0, -1/√3)
    W = np.array([0, 0])                   # Origin (singlet)

    # Draw the fundamental triangle
    triangle = plt.Polygon([R, G, B], fill=False, edgecolor='blue',
                           linewidth=2, linestyle='-', label=r'$\mathbf{3}$')
    ax.add_patch(triangle)

    # Fill the triangle with light color
    triangle_fill = plt.Polygon([R, G, B], fill=True, facecolor='lightblue',
                                 alpha=0.2, edgecolor='none')
    ax.add_patch(triangle_fill)

    # Draw anti-fundamental triangle (inverted)
    R_bar = -R
    G_bar = -G
    B_bar = -B
    anti_triangle = plt.Polygon([R_bar, G_bar, B_bar], fill=False, edgecolor='red',
                                 linewidth=2, linestyle='--', label=r'$\bar{\mathbf{3}}$')
    ax.add_patch(anti_triangle)

    # Plot vertices
    ax.scatter(*R, c=COLORS['R'], s=200, edgecolor='black', linewidth=1.5, zorder=5)
    ax.scatter(*G, c=COLORS['G'], s=200, edgecolor='black', linewidth=1.5, zorder=5)
    ax.scatter(*B, c=COLORS['B'], s=200, edgecolor='black', linewidth=1.5, zorder=5)

    # Plot W at origin (larger, emphasized)
    ax.scatter(*W, c=COLORS['W'], s=400, edgecolor='black', linewidth=2, zorder=10)

    # Draw circle around W to emphasize singlet nature
    circle = plt.Circle(W, 0.12, fill=False, edgecolor=COLORS['W'],
                        linewidth=2, linestyle='-', alpha=0.8)
    ax.add_patch(circle)

    # Add shaded region showing W domain (pie slice representation)
    # W domain covers 25% = π steradians out of 4π
    for i, (start, end, c) in enumerate([(0, 90, COLORS['R']), (90, 180, COLORS['G']),
                                          (180, 270, COLORS['B']), (270, 360, COLORS['W'])]):
        wedge = Wedge(W, 0.3, start, end, alpha=0.15, facecolor=c, edgecolor='none')
        ax.add_patch(wedge)

    # Labels
    label_offset = 0.12
    ax.text(R[0]+label_offset, R[1]+0.05, 'R', fontsize=11, fontweight='bold', color=COLORS['R'])
    ax.text(G[0]-label_offset*2, G[1]+0.05, 'G', fontsize=11, fontweight='bold', color=COLORS['G'])
    ax.text(B[0]+0.05, B[1]-label_offset, 'B', fontsize=11, fontweight='bold', color=COLORS['B'])
    ax.text(W[0]+0.15, W[1]+0.02, r'W $\rightarrow$ (0,0)', fontsize=10, fontweight='bold', color=COLORS['W'])

    # Axis labels
    ax.set_xlabel(r'$T_3$', fontsize=11)
    ax.set_ylabel(r'$T_8$', fontsize=11)

    # Draw axes through origin
    ax.axhline(y=0, color='gray', linewidth=0.5, linestyle='-', alpha=0.5)
    ax.axvline(x=0, color='gray', linewidth=0.5, linestyle='-', alpha=0.5)

    # Annotation for singlet
    ax.annotate(r'$\mathbf{1}$ (singlet)', xy=(0, 0), xytext=(0.35, -0.45),
                fontsize=9, color=COLORS['W'],
                arrowprops=dict(arrowstyle='->', color=COLORS['W'], lw=1.5))

    # Set limits
    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.75, 0.55)
    ax.set_aspect('equal')

    # Legend
    ax.legend(loc='upper right', fontsize=8)

    ax.set_title(r'(b) SU(3) Weight Space: W $\rightarrow$ Origin', fontsize=10, fontweight='bold')


def panel_c_adm_production(ax):
    """
    Panel (c): Asymmetric Dark Matter production chain diagram.
    Shows how CG chirality generates both baryon asymmetry and W-asymmetry.
    """
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')

    # Box style
    bbox_style = dict(boxstyle='round,pad=0.3', facecolor='white', edgecolor='black', linewidth=1.5)

    # Title at top
    ax.text(5, 9.5, 'Asymmetric Dark Matter Production', fontsize=11, fontweight='bold',
            ha='center', va='center')

    # CG Chirality at the source
    ax.text(5, 8.2, r'CG Geometric Chirality ($\alpha = 2\pi/3$)', fontsize=10,
            ha='center', va='center', bbox=dict(boxstyle='round,pad=0.4',
            facecolor='#f0e68c', edgecolor='#b8860b', linewidth=2))

    # Arrow down splitting into two
    ax.annotate('', xy=(3.5, 6.8), xytext=(5, 7.6),
                arrowprops=dict(arrowstyle='->', lw=2, color='black'))
    ax.annotate('', xy=(6.5, 6.8), xytext=(5, 7.6),
                arrowprops=dict(arrowstyle='->', lw=2, color='black'))

    # Baryon asymmetry box (left branch)
    ax.text(3, 6.2, r'$\eta_B = 6.1 \times 10^{-10}$', fontsize=9,
            ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='lightblue', edgecolor='blue', linewidth=1.5))
    ax.text(3, 5.5, 'Baryon Asymmetry', fontsize=8, ha='center', va='center', color='blue')

    # W asymmetry box (right branch)
    ax.text(7, 6.2, r'$\epsilon_W = 2.9 \times 10^{-13}$', fontsize=9,
            ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='#e8d5e8', edgecolor=COLORS['W'], linewidth=1.5))
    ax.text(7, 5.5, 'W-Asymmetry', fontsize=8, ha='center', va='center', color=COLORS['W'])

    # Suppression factor annotation
    ax.text(5, 6.0, r'$\kappa_W^{geom} = 4.8 \times 10^{-4}$', fontsize=8,
            ha='center', va='center', style='italic', color='gray')

    # Arrows down to final products
    ax.annotate('', xy=(3, 4.2), xytext=(3, 5.0),
                arrowprops=dict(arrowstyle='->', lw=2, color='blue'))
    ax.annotate('', xy=(7, 4.2), xytext=(7, 5.0),
                arrowprops=dict(arrowstyle='->', lw=2, color=COLORS['W']))

    # Final products
    # Baryons
    ax.text(3, 3.6, 'Baryons (p, n)', fontsize=9, ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='lightblue', edgecolor='blue', linewidth=1.5))
    ax.text(3, 2.9, r'$\Omega_b h^2 = 0.0224$', fontsize=8, ha='center', color='blue')

    # W solitons (Dark Matter)
    ax.text(7, 3.6, 'W Solitons (DM)', fontsize=9, ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='#e8d5e8', edgecolor=COLORS['W'], linewidth=1.5))
    ax.text(7, 2.9, r'$\Omega_W h^2 = 0.12$', fontsize=8, ha='center', color=COLORS['W'])

    # Key result box at bottom
    result_text = r'$\frac{\Omega_{DM}}{\Omega_b} = \frac{\epsilon_W}{\eta_B} \times \frac{M_W}{m_p} \times 7.04 \approx 5.3$'
    ax.text(5, 1.5, result_text, fontsize=10, ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.4', facecolor='#ffffcc', edgecolor='#cc9900', linewidth=2))

    # Connection between final products
    ax.annotate('', xy=(5.8, 3.6), xytext=(4.2, 3.6),
                arrowprops=dict(arrowstyle='<->', lw=1.5, color='gray', linestyle='--'))
    ax.text(5, 3.85, 'Same origin!', fontsize=7, ha='center', color='gray', style='italic')

    ax.set_title('(c) ADM Production Chain', fontsize=10, fontweight='bold')


def panel_d_detection_limits(ax):
    """
    Panel (d): Direct detection cross-section vs. mass with current bounds.
    Shows LZ bounds, DARWIN projected sensitivity, and CG prediction.
    """
    # Mass range (GeV)
    masses = np.logspace(1, 4, 100)  # 10 GeV to 10 TeV

    # LZ 2024 bound (approximate parameterization)
    # Minimum around 30-50 GeV, rising at low and high mass
    def lz_bound(m):
        # Approximate LZ sensitivity curve
        m0 = 40  # Mass at minimum
        sigma_min = 9e-48  # Minimum cross-section
        # Parabolic in log-log space
        return sigma_min * (1 + 0.5 * np.log10(m/m0)**2 + 0.1 * np.abs(np.log10(m/m0))**3)

    lz_sigma = np.array([lz_bound(m) for m in masses])

    # DARWIN projected sensitivity (factor ~100 better than LZ)
    darwin_sigma = lz_sigma / 100

    # Neutrino floor (approximate)
    def neutrino_floor(m):
        # Approximate neutrino coherent scattering floor
        m0 = 6  # GeV
        sigma_floor = 1e-49
        return sigma_floor * np.maximum(1, (m0/m)**2)

    neutrino_sigma = np.array([neutrino_floor(m) for m in masses])

    # CG W-condensate prediction
    # M_W = 1620 GeV (from paper), σ_SI = 1.6 × 10^-47 cm²
    M_W_pred = 1620
    sigma_W_pred = 1.6e-47

    # Mass range uncertainty
    M_W_min = 1460  # 1620 - 160
    M_W_max = 1780  # 1620 + 160

    # Plot bounds (no labels - we'll add them manually to control order)
    lz_fill = ax.fill_between(masses, lz_sigma, 1e-43, alpha=0.3, color='red')
    lz_line, = ax.plot(masses, lz_sigma, 'r-', linewidth=2)

    darwin_line, = ax.plot(masses, darwin_sigma, 'g--', linewidth=2)

    neutrino_fill = ax.fill_between(masses, neutrino_sigma, 1e-52, alpha=0.2, color='orange')
    ax.plot(masses, neutrino_sigma, 'orange', linewidth=1.5, linestyle=':')

    # CG prediction with uncertainty band
    cg_point = ax.errorbar(M_W_pred, sigma_W_pred, xerr=160,
                fmt='o', markersize=8, color='black',
                markeredgecolor='black', markeredgewidth=1.5,
                capsize=4, capthick=1.5, ecolor='black')
    # Invisible marker for cross-section line
    sigma_line, = ax.plot([], [], ' ')

    # Build legend with custom order: CG first, then sigma below it, then others
    from matplotlib.lines import Line2D
    legend_handles = [
        lz_fill,
        lz_line,
        darwin_line,
        neutrino_fill,
        Line2D([], [], marker='o', color='black', markersize=6, linestyle='none'),  # simple circle for CG
        Line2D([], [], linestyle='none'),  # invisible spacer for sigma text
    ]
    legend_labels = [
        'LZ 2024 Excluded',
        'LZ 2024 Limit',
        'DARWIN (projected)',
        'Neutrino floor',
        r'CG W-soliton: $M_W = 1620 \pm 160$ GeV',
        r'    $\sigma_{SI} = 1.6 \times 10^{-47}$ cm$^2$',
    ]

    # Labels and formatting
    ax.set_xlabel(r'WIMP Mass $M_{\chi}$ [GeV]', fontsize=11)
    ax.set_ylabel(r'SI Cross-section $\sigma_{SI}$ [cm$^2$]', fontsize=11)

    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlim(100, 5e3)
    ax.set_ylim(1e-50, 1e-45)

    ax.legend(legend_handles, legend_labels, loc='upper right', fontsize=7, framealpha=0.9)
    ax.grid(True, alpha=0.3, which='both')

    ax.set_title('(d) Direct Detection: LZ \u2192 DARWIN', fontsize=10, fontweight='bold')


def create_w_condensate_figure():
    """Create the W-Condensate Dark Matter detection figure (single panel)."""

    fig, ax = plt.subplots(figsize=(7, 5))

    # Single panel - Detection limits
    panel_d_detection_limits(ax)

    # Remove the panel label from title since it's now the only panel
    ax.set_title('Direct Detection: LZ → DARWIN', fontsize=11, fontweight='bold')

    fig.tight_layout()

    return fig


if __name__ == "__main__":
    print("Creating W-Condensate Dark Matter figure...")

    fig = create_w_condensate_figure()

    # Save to output directory
    for ext in ['pdf', 'png']:
        filepath = output_dir / f'fig_w_condensate_dark_matter.{ext}'
        fig.savefig(filepath, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    plt.close()
    print("Done!")
