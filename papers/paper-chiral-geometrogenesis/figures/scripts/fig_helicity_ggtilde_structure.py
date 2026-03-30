#!/usr/bin/env python3
"""
Figure: Helicity Structure of GG̃ Coupling (Theorem 6.2.2)

Visualizes the helicity selection mechanism in same-helicity gluon scattering.
The dual field strength GG̃ ∝ |G⁺|² - |G⁻|² selects same-helicity gluon pairs,
enabling the non-zero amplitude M(g⁺g⁺ → g⁺g⁺) via χ exchange.

Key physics:
- Standard QCD: M(g⁺g⁺ → g⁺g⁺) = 0 at tree level (Parke-Taylor)
- CG framework: Non-zero via χGG̃ anomaly coupling
- Cross-section ratio: σ/σ_tot ~ 10⁻⁹ at GeV scale

Proof Document: docs/proofs/Phase6/Theorem-6.2.2-Helicity-Amplitudes-Spinor-Helicity-Formalism.md
Paper Section: Section 6.4.2 (Helicity Structure)

Output: fig_helicity_ggtilde_structure.pdf, fig_helicity_ggtilde_structure.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.patches import Circle, FancyArrowPatch, Arc, FancyBboxPatch, Wedge
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

# Colors
COLOR_POSITIVE = '#FFD700'    # Gold for positive helicity
COLOR_NEGATIVE = '#4169E1'    # Royal blue for negative helicity
COLOR_CHI = '#9B59B6'         # Purple for χ field
COLOR_GLUON = '#E67E22'       # Orange for gluons
COLOR_VERTEX = '#2C3E50'      # Dark for vertices
COLOR_BACKGROUND = '#0d1b2a'  # Dark blue background for gradient


def create_helicity_gradient():
    """
    Create 2D gradient showing helicity structure of GG̃ coupling.
    The pattern shows |G⁺|² - |G⁻|² structure.
    """
    x = np.linspace(-2, 2, 500)
    y = np.linspace(-2, 2, 500)
    X, Y = np.meshgrid(x, y)
    R = np.sqrt(X**2 + Y**2)
    theta = np.arctan2(Y, X)

    # Self-dual pattern: represents helicity selection
    # cos²(2θ) creates quadrupole pattern showing G⁺G⁺ coupling regions
    helicity_pattern = np.cos(2 * theta)**2 * np.exp(-R**2 / 2)

    return X, Y, R, theta, helicity_pattern


def plot_helicity_gradient_panel(ax):
    """
    Plot the helicity structure gradient with annotations.
    """
    X, Y, R, theta, helicity_pattern = create_helicity_gradient()

    # Custom colormap: dark blue to bright yellow (for self-dual enhancement)
    colors = ['#0d1b2a', '#1b263b', '#415a77', '#778da9', '#e0e1dd',
              '#ffd700', '#ffb700', '#ff9500', '#ff7300', '#ff5100']
    cmap = LinearSegmentedColormap.from_list('helicity', colors)

    im = ax.imshow(helicity_pattern, extent=[-2, 2, -2, 2],
                   origin='lower', cmap=cmap, vmin=0, vmax=1)

    # Draw helicity indicators at cardinal directions
    arrow_positions = [
        (0, 1.5, r'$g^+$'),
        (0, -1.5, r'$g^+$'),
        (1.5, 0, r'$g^+$'),
        (-1.5, 0, r'$g^+$'),
    ]

    for x, y, label in arrow_positions:
        # Circular arrow indicating positive helicity
        angle = np.degrees(np.arctan2(y, x))
        arc = Arc((x, y), 0.35, 0.35, angle=angle,
                  theta1=0, theta2=270, color='white', lw=2)
        ax.add_patch(arc)
        # Small arrow head
        ax.annotate('',
                   xy=(x + 0.12*np.cos(np.radians(angle + 270)),
                       y + 0.12*np.sin(np.radians(angle + 270))),
                   xytext=(x + 0.05*np.cos(np.radians(angle + 220)),
                           y + 0.05*np.sin(np.radians(angle + 220))),
                   arrowprops=dict(arrowstyle='->', color='white', lw=1.5))
        # Label
        label_offset = 0.35
        ax.text(x * (1 + label_offset/abs(x) if x != 0 else 1),
                y * (1 + label_offset/abs(y) if y != 0 else 1),
                label, fontsize=12, ha='center', va='center',
                color='white', fontweight='bold')

    # Central annotation box
    ax.text(0, 0, r'$G\tilde{G} \propto$' + '\n' + r'$|G^+|^2 - |G^-|^2$',
            fontsize=11, ha='center', va='center', color='black',
            bbox=dict(boxstyle='round,pad=0.4', facecolor='white',
                     edgecolor='gray', alpha=0.95))

    # Diagonal annotations showing enhanced coupling regions
    for angle, label in [(np.pi/4, 'Enhanced'), (3*np.pi/4, 'Enhanced'),
                         (5*np.pi/4, 'Enhanced'), (7*np.pi/4, 'Enhanced')]:
        r = 1.1
        ax.text(r*np.cos(angle), r*np.sin(angle), label,
                fontsize=8, ha='center', va='center', color='#ffd700',
                rotation=np.degrees(angle) if angle < np.pi else np.degrees(angle) - 180,
                alpha=0.9)

    ax.set_xlabel(r'$x$ (transverse)', fontsize=11)
    ax.set_ylabel(r'$y$ (transverse)', fontsize=11)
    ax.set_title(r'$G\tilde{G}$ Helicity Selection Pattern', fontsize=13, fontweight='bold')
    ax.set_aspect('equal')

    # Colorbar
    divider = make_axes_locatable(ax)
    cax = divider.append_axes("right", size="5%", pad=0.1)
    cbar = plt.colorbar(im, cax=cax)
    cbar.set_label('Same-helicity coupling strength', fontsize=10)

    return im


def plot_feynman_diagram_panel(ax):
    """
    Draw the Feynman diagram for g⁺g⁺ → g⁺g⁺ via χ exchange.
    """
    ax.set_xlim(-2.8, 2.8)
    ax.set_ylim(-2.2, 2.2)
    ax.set_aspect('equal')

    # Gluon lines (incoming) - with spring/coil representation
    # g⁺(p₁) - top left
    ax.annotate('', xy=(-1.0, 1.0), xytext=(-2.2, 1.8),
                arrowprops=dict(arrowstyle='->', color=COLOR_GLUON, lw=2.5,
                              connectionstyle='arc3,rad=0.1'))
    ax.text(-2.4, 1.9, r'$g^+(p_1)$', fontsize=11, color=COLOR_GLUON, fontweight='bold')

    # g⁺(p₂) - bottom left
    ax.annotate('', xy=(-1.0, -1.0), xytext=(-2.2, -1.8),
                arrowprops=dict(arrowstyle='->', color=COLOR_GLUON, lw=2.5,
                              connectionstyle='arc3,rad=-0.1'))
    ax.text(-2.4, -1.95, r'$g^+(p_2)$', fontsize=11, color=COLOR_GLUON, fontweight='bold')

    # Gluon lines (outgoing)
    # g⁺(p₃) - top right
    ax.annotate('', xy=(2.2, 1.8), xytext=(1.0, 1.0),
                arrowprops=dict(arrowstyle='->', color=COLOR_GLUON, lw=2.5,
                              connectionstyle='arc3,rad=0.1'))
    ax.text(2.3, 1.9, r'$g^+(p_3)$', fontsize=11, color=COLOR_GLUON, fontweight='bold')

    # g⁺(p₄) - bottom right
    ax.annotate('', xy=(2.2, -1.8), xytext=(1.0, -1.0),
                arrowprops=dict(arrowstyle='->', color=COLOR_GLUON, lw=2.5,
                              connectionstyle='arc3,rad=-0.1'))
    ax.text(2.3, -1.95, r'$g^+(p_4)$', fontsize=11, color=COLOR_GLUON, fontweight='bold')

    # χ propagator (dashed line)
    ax.plot([-1.0, 1.0], [0, 0], '--', color=COLOR_CHI, linewidth=3.5, alpha=0.9)
    ax.text(0, 0.35, r'$\chi$', fontsize=14, ha='center', color=COLOR_CHI, fontweight='bold')

    # Vertices (χGG̃ anomaly coupling) - filled circles
    left_vertex = Circle((-1.0, 0), 0.22, facecolor=COLOR_VERTEX,
                         edgecolor='white', linewidth=2, zorder=5)
    right_vertex = Circle((1.0, 0), 0.22, facecolor=COLOR_VERTEX,
                          edgecolor='white', linewidth=2, zorder=5)
    ax.add_patch(left_vertex)
    ax.add_patch(right_vertex)

    # Vertex labels
    ax.text(-1.0, -0.55, r'$\chi G\tilde{G}$', fontsize=10, ha='center',
            color=COLOR_VERTEX, fontweight='bold')
    ax.text(1.0, -0.55, r'$\chi G\tilde{G}$', fontsize=10, ha='center',
            color=COLOR_VERTEX, fontweight='bold')

    # Connecting lines from vertices to gluons
    ax.plot([-1.0, -1.0], [0.22, 1.0], '-', color=COLOR_VERTEX, lw=1.8)
    ax.plot([-1.0, -1.0], [-0.22, -1.0], '-', color=COLOR_VERTEX, lw=1.8)
    ax.plot([1.0, 1.0], [0.22, 1.0], '-', color=COLOR_VERTEX, lw=1.8)
    ax.plot([1.0, 1.0], [-0.22, -1.0], '-', color=COLOR_VERTEX, lw=1.8)

    # Title
    ax.set_title(r'$g^+g^+ \to g^+g^+$ via $\chi$ Exchange', fontsize=13, fontweight='bold')

    # Comparison note
    ax.text(0, -1.9, r'Standard QCD: $\mathcal{M}_{\rm QCD} = 0$ (tree level)',
            fontsize=10, ha='center', style='italic', color='gray')

    ax.axis('off')


def plot_amplitude_formula_panel(ax):
    """
    Display the amplitude formula and cross-section ratio.
    """
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')

    # Main formula box
    formula_box = FancyBboxPatch((0.5, 5.5), 9, 3.5,
                                  boxstyle="round,pad=0.3",
                                  facecolor='#F8F9FA', edgecolor='#2C3E50', lw=2)
    ax.add_patch(formula_box)

    ax.text(5, 8.2, 'CG Amplitude (one loop):', fontsize=11, ha='center',
            fontweight='bold', color='#2C3E50')
    ax.text(5, 7.0, r'$\mathcal{M}_{\rm CG}(g^+g^+ \to g^+g^+) = \frac{C_\chi^2 \alpha_s^2}{(8\pi)^2} \cdot \frac{[12]^2[34]^{*2}}{s}$',
            fontsize=12, ha='center', color='#8E44AD')
    ax.text(5, 5.9, r'where $C_\chi = N_f/2$ (anomaly coefficient)',
            fontsize=9, ha='center', color='gray')

    # Cross-section box
    sigma_box = FancyBboxPatch((0.5, 2.0), 9, 2.8,
                                boxstyle="round,pad=0.3",
                                facecolor='#FDF2E9', edgecolor='#E67E22', lw=2)
    ax.add_patch(sigma_box)

    ax.text(5, 4.0, 'Cross-section ratio (GeV scale):', fontsize=11, ha='center',
            fontweight='bold', color='#D35400')
    ax.text(5, 2.9, r'$\frac{\sigma(g^+g^+ \to g^+g^+)}{\sigma_{\rm tot}} \sim 10^{-9}$',
            fontsize=14, ha='center', color='#C0392B', fontweight='bold')

    # Key insight
    ax.text(5, 0.8, r'$\bullet$ Unique CG signature: non-zero where QCD vanishes',
            fontsize=10, ha='center', color='#1A5276', style='italic')


def create_combined_figure():
    """
    Create the combined 3-panel figure for the paper.
    """
    fig = plt.figure(figsize=(14, 5))

    # Panel (a): Helicity gradient
    ax1 = fig.add_subplot(131)
    plot_helicity_gradient_panel(ax1)
    ax1.text(-0.12, 1.05, '(a)', transform=ax1.transAxes, fontsize=14, fontweight='bold')

    # Panel (b): Feynman diagram
    ax2 = fig.add_subplot(132)
    plot_feynman_diagram_panel(ax2)
    ax2.text(-0.05, 1.05, '(b)', transform=ax2.transAxes, fontsize=14, fontweight='bold')

    # Panel (c): Amplitude formula
    ax3 = fig.add_subplot(133)
    plot_amplitude_formula_panel(ax3)
    ax3.text(-0.05, 1.05, '(c)', transform=ax3.transAxes, fontsize=14, fontweight='bold')

    plt.tight_layout()
    return fig


def draw_helicity_arrow(ax, cx, cy, radius=0.25, direction='ccw', color='white', lw=2.5):
    """
    Draw a circular arrow indicating helicity (spin rotation).

    Parameters:
    - cx, cy: center position
    - radius: size of the circular arrow
    - direction: 'ccw' for positive helicity, 'cw' for negative
    - color: arrow color
    - lw: line width
    """
    # Draw arc (270 degrees of a circle)
    if direction == 'ccw':
        theta1, theta2 = 45, 315  # Counter-clockwise (positive helicity)
        # Arrow head at the end of the arc
        arrow_angle = np.radians(315)
        head_angle = np.radians(315 + 90)  # Perpendicular to arc end
    else:
        theta1, theta2 = 315, 45  # Clockwise (negative helicity)
        arrow_angle = np.radians(45)
        head_angle = np.radians(45 - 90)

    arc = Arc((cx, cy), 2*radius, 2*radius, angle=0,
              theta1=theta1, theta2=theta2, color=color, lw=lw)
    ax.add_patch(arc)

    # Calculate arrow head position (at end of arc)
    head_x = cx + radius * np.cos(arrow_angle)
    head_y = cy + radius * np.sin(arrow_angle)

    # Arrow head direction (tangent to circle)
    if direction == 'ccw':
        dx = -np.sin(arrow_angle) * 0.12
        dy = np.cos(arrow_angle) * 0.12
    else:
        dx = np.sin(arrow_angle) * 0.12
        dy = -np.cos(arrow_angle) * 0.12

    # Draw arrow head
    ax.annotate('', xy=(head_x + dx, head_y + dy), xytext=(head_x, head_y),
                arrowprops=dict(arrowstyle='->', color=color, lw=lw,
                              mutation_scale=15))


def create_single_panel_figure():
    """
    Create a single-panel version of just the helicity gradient.
    This is the primary figure for the paper.
    """
    fig, ax = plt.subplots(figsize=(7, 6))

    X, Y, R, theta, helicity_pattern = create_helicity_gradient()

    # Custom colormap
    colors = ['#0d1b2a', '#1b263b', '#415a77', '#778da9', '#e0e1dd',
              '#ffd700', '#ffb700', '#ff9500', '#ff7300', '#ff5100']
    cmap = LinearSegmentedColormap.from_list('helicity', colors)

    im = ax.imshow(helicity_pattern, extent=[-2, 2, -2, 2],
                   origin='lower', cmap=cmap, vmin=0, vmax=1)

    # Helicity indicators at cardinal positions with circular arrows
    # Position closer to center so labels don't get clipped
    helicity_positions = [
        (0, 1.35),    # Top
        (0, -1.35),   # Bottom
        (1.35, 0),    # Right
        (-1.35, 0),   # Left
    ]

    for x, y in helicity_positions:
        # Draw circular arrow indicating positive helicity
        draw_helicity_arrow(ax, x, y, radius=0.22, direction='ccw',
                           color='white', lw=2.5)

        # Label positioned outside the arrow but within plot bounds
        if y > 0:  # Top
            ax.text(x, y + 0.38, r'$g^+$', fontsize=14, ha='center', va='bottom',
                    color='white', fontweight='bold')
        elif y < 0:  # Bottom
            ax.text(x, y - 0.38, r'$g^+$', fontsize=14, ha='center', va='top',
                    color='white', fontweight='bold')
        elif x > 0:  # Right
            ax.text(x + 0.38, y, r'$g^+$', fontsize=14, ha='left', va='center',
                    color='white', fontweight='bold')
        else:  # Left
            ax.text(x - 0.38, y, r'$g^+$', fontsize=14, ha='right', va='center',
                    color='white', fontweight='bold')

    # Corner annotations
    corner_text = [
        (-1.4, 1.4, 'Same-helicity\nenhanced'),
        (1.4, 1.4, 'Same-helicity\nenhanced'),
        (-1.4, -1.4, 'Same-helicity\nenhanced'),
        (1.4, -1.4, 'Same-helicity\nenhanced'),
    ]
    for x, y, text in corner_text:
        ax.text(x, y, text, fontsize=8, ha='center', va='center',
                color='#ffd700', alpha=0.9)

    ax.set_xlabel(r'Transverse coordinate $x$', fontsize=12)
    ax.set_ylabel(r'Transverse coordinate $y$', fontsize=12)
    ax.set_title(r'Helicity Selection: $G\tilde{G}$ Coupling Pattern' + '\n' +
                 r'$G\tilde{G} \propto |G^+|^2 - |G^-|^2$',
                 fontsize=13, fontweight='bold')
    ax.set_aspect('equal')

    # Colorbar
    divider = make_axes_locatable(ax)
    cax = divider.append_axes("right", size="5%", pad=0.12)
    cbar = plt.colorbar(im, cax=cax)
    cbar.set_label('Same-helicity coupling strength', fontsize=11)

    plt.tight_layout()
    return fig


def main():
    """Generate figures and save to the paper figures directory."""

    print("=" * 70)
    print("Generating Helicity Structure Figure (Theorem 6.2.2)")
    print("=" * 70)
    print(f"\nOutput directory: {OUTPUT_DIR}/")
    print()

    # 1. Single-panel figure (primary for paper)
    print("1. Creating single-panel helicity gradient figure...")
    fig1 = create_single_panel_figure()
    fig1.savefig(os.path.join(OUTPUT_DIR, 'fig_helicity_ggtilde_structure.png'),
                 dpi=300, bbox_inches='tight', facecolor='white')
    fig1.savefig(os.path.join(OUTPUT_DIR, 'fig_helicity_ggtilde_structure.pdf'),
                 bbox_inches='tight', facecolor='white')
    print(f"   Saved: fig_helicity_ggtilde_structure.png/pdf")

    # 2. Combined 3-panel figure (supplementary)
    print("2. Creating combined 3-panel figure...")
    fig2 = create_combined_figure()
    fig2.savefig(os.path.join(OUTPUT_DIR, 'fig_helicity_ggtilde_combined.png'),
                 dpi=300, bbox_inches='tight', facecolor='white')
    fig2.savefig(os.path.join(OUTPUT_DIR, 'fig_helicity_ggtilde_combined.pdf'),
                 bbox_inches='tight', facecolor='white')
    print(f"   Saved: fig_helicity_ggtilde_combined.png/pdf")

    print()
    print("=" * 70)
    print("FIGURE DESCRIPTION")
    print("=" * 70)
    print()
    print("The GG̃ helicity selection pattern shows how the dual field strength")
    print("coupling selects same-helicity gluon pairs:")
    print()
    print("  GG̃ = G_μν G̃^μν ∝ |G⁺|² - |G⁻|²")
    print()
    print("This decomposition means:")
    print("  • g⁺g⁺ couples to G⁺G⁺ (self-dual × self-dual) → ENHANCED")
    print("  • g⁻g⁻ couples to G⁻G⁻ (anti-self-dual × anti-self-dual) → ENHANCED")
    print("  • g⁺g⁻ terms cancel in GG̃ → SUPPRESSED")
    print()
    print("Result: Same-helicity gluon scattering is non-zero in CG,")
    print("        providing a unique signature absent in tree-level QCD.")
    print()
    print("=" * 70)
    print("Done!")

    plt.close('all')


if __name__ == '__main__':
    main()
