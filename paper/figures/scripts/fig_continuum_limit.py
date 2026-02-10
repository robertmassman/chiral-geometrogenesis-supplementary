#!/usr/bin/env python3
"""
Figure: Continuum Limit from Discrete Structure
================================================

Two-panel figure showing how discrete stella octangula structure
connects to continuous SU(3) gauge theory.

Panel (a): A₂ root system derived from stella octangula weight differences
Panel (b): Discrete → Continuous limit visualization (a → 0)

Related:
- Proposition 0.0.6b: Continuum Limit Procedure
- Paper Section: Continuum Limit from Discrete Structure (sec:continuum-limit)
- Verification: verification/foundations/continuum_limit_verification.py

Output:
- fig_continuum_limit.png
- fig_continuum_limit.pdf

Author: Chiral Geometrogenesis Project
Date: 2026-02-04
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, Arc
from matplotlib.collections import LineCollection
from pathlib import Path

# Output directory
OUTPUT_DIR = Path(__file__).parent.parent
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# ============================================================================
# COLOR SCHEME
# ============================================================================

# Color palette for the three color charges
COLOR_R = '#E74C3C'  # Red
COLOR_G = '#27AE60'  # Green
COLOR_B = '#3498DB'  # Blue
COLOR_RBAR = '#F1948A'  # Light red (anti-red)
COLOR_GBAR = '#82E0AA'  # Light green (anti-green)
COLOR_BBAR = '#85C1E9'  # Light blue (anti-blue)
COLOR_ROOT = '#2C3E50'  # Dark gray for root arrows
COLOR_DISCRETE = '#8E44AD'  # Purple for discrete points
COLOR_CONTINUOUS = '#F39C12'  # Orange/gold for continuous

# ============================================================================
# PHYSICS DATA
# ============================================================================

def get_stella_weights():
    """
    Return the weight vectors for the stella octangula vertices.

    SU(3) fundamental representation weights (2D weight diagram):
    w_R = (1/2, 1/(2√3))
    w_G = (-1/2, 1/(2√3))
    w_B = (0, -1/√3)

    Anti-fundamental weights are negatives.
    """
    sqrt3 = np.sqrt(3)

    weights = {
        'R': np.array([1/2, 1/(2*sqrt3)]),
        'G': np.array([-1/2, 1/(2*sqrt3)]),
        'B': np.array([0, -1/sqrt3]),
    }
    weights['R̄'] = -weights['R']
    weights['Ḡ'] = -weights['G']
    weights['B̄'] = -weights['B']

    return weights


def get_a2_roots():
    """
    Get the A₂ root system from weight differences.

    Simple roots:
    α₁ = w_R - w_G
    α₂ = w_G - w_B
    """
    weights = get_stella_weights()

    alpha1 = weights['R'] - weights['G']  # (1, 0)
    alpha2 = weights['G'] - weights['B']  # (-1/2, √3/2)
    alpha3 = alpha1 + alpha2              # (1/2, √3/2) = w_R - w_B

    roots = {
        'α₁': alpha1,
        'α₂': alpha2,
        'α₁+α₂': alpha3,
        '-α₁': -alpha1,
        '-α₂': -alpha2,
        '-(α₁+α₂)': -alpha3
    }

    return roots, alpha1, alpha2

# ============================================================================
# PANEL A: ROOT SYSTEM
# ============================================================================

def draw_root_system(ax):
    """
    Draw the A₂ root system with weight vertices.
    """
    weights = get_stella_weights()
    roots, alpha1, alpha2 = get_a2_roots()

    # Draw weight lattice circle at the correct radius
    # Weight magnitude: |w| = sqrt((1/2)² + (1/(2√3))²) = 1/√3 ≈ 0.577
    weight_radius = 1 / np.sqrt(3)
    circle = Circle((0, 0), weight_radius, fill=False, linestyle='--',
                    color='gray', alpha=0.6, linewidth=1.2)
    ax.add_patch(circle)

    # Draw thin lines connecting adjacent weights (hexagon edges)
    # These show the root directions: α = w_i - w_j
    weight_order = ['R', 'B̄', 'G', 'R̄', 'B', 'Ḡ']  # Order around hexagon
    for i in range(6):
        w1 = weights[weight_order[i]]
        w2 = weights[weight_order[(i+1) % 6]]
        ax.plot([w1[0], w2[0]], [w1[1], w2[1]],
               color='gray', linewidth=1, linestyle='-', alpha=0.5, zorder=2)

    # Highlight the root edges connecting R, G, B (fundamental colors)
    # α₁ = w_R - w_G (edge from G to R)
    ax.plot([weights['G'][0], weights['R'][0]],
           [weights['G'][1], weights['R'][1]],
           color=COLOR_ROOT, linewidth=2.5, linestyle='-', alpha=0.9, zorder=4)
    # α₂ = w_G - w_B (edge from B to G)
    ax.plot([weights['B'][0], weights['G'][0]],
           [weights['B'][1], weights['G'][1]],
           color=COLOR_ROOT, linewidth=2.5, linestyle='-', alpha=0.9, zorder=4)
    # α₁ + α₂ = w_R - w_B (edge from B to R)
    ax.plot([weights['B'][0], weights['R'][0]],
           [weights['B'][1], weights['R'][1]],
           color=COLOR_ROOT, linewidth=2.5, linestyle='-', alpha=0.9, zorder=4)

    # Draw weight vertices as filled circles
    weight_colors = {
        'R': COLOR_R, 'G': COLOR_G, 'B': COLOR_B,
        'R̄': COLOR_RBAR, 'Ḡ': COLOR_GBAR, 'B̄': COLOR_BBAR
    }

    for name, w in weights.items():
        ax.scatter(w[0], w[1], s=150, c=weight_colors[name],
                  edgecolors='black', linewidth=1.5, zorder=5)

    # Label weights
    label_offsets = {
        'R': (0.12, 0.06), 'G': (-0.12, 0.06), 'B': (0.12, 0.0),
        'R̄': (-0.12, -0.06), 'Ḡ': (0.12, -0.06), 'B̄': (-0.12, 0.0)
    }
    # Display names with proper LaTeX bars
    display_names = {
        'R': 'R', 'G': 'G', 'B': 'B',
        'R̄': r'$\bar{\mathrm{R}}$', 'Ḡ': r'$\bar{\mathrm{G}}$', 'B̄': r'$\bar{\mathrm{B}}$'
    }

    for name, w in weights.items():
        offset = label_offsets[name]
        ax.text(w[0] + offset[0], w[1] + offset[1], display_names[name],
               fontsize=11, fontweight='bold', ha='center', va='center')

    # Mark origin (Cartan subalgebra)
    ax.scatter(0, 0, s=80, c='white', edgecolors='black', linewidth=2, zorder=5)
    ax.text(0.08, 0.08, '0', fontsize=10, ha='left', va='bottom')

    # Draw simple roots α₁ and α₂ as distinct black arrows
    # α₁ = w_R - w_G (points from G to R)
    # α₂ = w_G - w_B (points from B to G)

    # α₁ arrow - extend to the circle edge (radius = 1/√3 ≈ 0.577)
    arrow_scale_1 = weight_radius  # 1/√3
    ax.annotate('', xy=(alpha1[0]*arrow_scale_1, alpha1[1]*arrow_scale_1), xytext=(0, 0),
               arrowprops=dict(arrowstyle='->', color=COLOR_ROOT, lw=2.5,
                              shrinkA=0, shrinkB=0))
    # Label outside the circle, just above the arrow
    ax.text(alpha1[0]*arrow_scale_1 + 0.02, alpha1[1]*arrow_scale_1 + 0.02,
           r'$\alpha_1$', fontsize=12, color=COLOR_ROOT, fontweight='bold')

    # α₂ arrow - extend to the circle edge (radius = 1/√3 ≈ 0.577)
    arrow_scale_2 = weight_radius  # 1/√3
    ax.annotate('', xy=(alpha2[0]*arrow_scale_2, alpha2[1]*arrow_scale_2), xytext=(0, 0),
               arrowprops=dict(arrowstyle='->', color=COLOR_ROOT, lw=2.5,
                              shrinkA=0, shrinkB=0))
    # Label outside the circle
    ax.text(alpha2[0]*arrow_scale_2 - 0.08, alpha2[1]*arrow_scale_2 + 0.06,
           r'$\alpha_2$', fontsize=12, color=COLOR_ROOT, fontweight='bold')

    # Axis settings
    ax.set_xlim(-0.75, 0.75)
    ax.set_ylim(-0.75, 0.75)
    ax.set_aspect('equal')
    ax.axhline(y=0, color='gray', linewidth=0.5, alpha=0.5)
    ax.axvline(x=0, color='gray', linewidth=0.5, alpha=0.5)

    ax.set_xlabel('Weight space $h_1$', fontsize=11)
    ax.set_ylabel('Weight space $h_2$', fontsize=11)
    ax.set_title(r'(a) $A_2$ Root System from Stella Weights', fontsize=12, fontweight='bold')

    # Add annotation about the physics
    ax.text(0.02, 0.02, r'$\alpha_1 = w_R - w_G$' + '\n' + r'$\alpha_2 = w_G - w_B$' + '\n' + r'$\alpha_1 + \alpha_2 = w_R - w_B$',
           transform=ax.transAxes, fontsize=9, va='bottom', ha='left',
           bbox=dict(boxstyle='round', facecolor='white', alpha=0.8, edgecolor='gray'))

# ============================================================================
# PANEL B: DISCRETE → CONTINUOUS LIMIT
# ============================================================================

def draw_continuum_limit(ax):
    """
    Visualize the discrete → continuous limit (a → 0).

    Shows how discrete points fill in to become a continuous manifold
    as the lattice spacing decreases.
    """
    weight_radius = 1 / np.sqrt(3)

    # Three stages of the continuum limit
    # Stage 1: Discrete (only 6 points) - shown as large dots
    # Stage 2: Finer lattice (more points) - shown as medium dots
    # Stage 3: Continuous (filled ring) - shown as solid ring

    # Draw continuous ring (background) - the a → 0 limit
    theta_continuous = np.linspace(0, 2*np.pi, 500)
    r_outer = weight_radius * 1.08
    r_inner = weight_radius * 0.92

    # Fill the ring with a gradient
    # Shift by π/6 to align with discrete R, G, B positions
    hue_offset = np.pi/6
    for i, t in enumerate(np.linspace(0, 2*np.pi, 360)):
        # Shifted angle for color calculation
        t_shifted = (t - hue_offset) % (2*np.pi)
        # Color based on angle (R, G, B sectors) - ensure values stay in [0,1]
        if (t_shifted >= 0 and t_shifted < 2*np.pi/3):
            frac = t_shifted / (2*np.pi/3)
            color = (max(0, min(1, 0.9-0.4*frac)), max(0, min(1, 0.3+0.4*frac)), 0.2)  # R to G
        elif (t_shifted >= 2*np.pi/3 and t_shifted < 4*np.pi/3):
            frac = (t_shifted - 2*np.pi/3) / (2*np.pi/3)
            color = (max(0, min(1, 0.5-0.3*frac)), max(0, min(1, 0.7-0.4*frac)), max(0, min(1, 0.2+0.6*frac)))  # G to B
        else:
            frac = (t_shifted - 4*np.pi/3) / (2*np.pi/3)
            color = (max(0, min(1, 0.2+0.7*frac)), 0.3, max(0, min(1, 0.8-0.6*frac)))  # B to R

        t_next = t + 2*np.pi/360
        ax.fill([r_inner*np.cos(t), r_outer*np.cos(t), r_outer*np.cos(t_next), r_inner*np.cos(t_next)],
                [r_inner*np.sin(t), r_outer*np.sin(t), r_outer*np.sin(t_next), r_inner*np.sin(t_next)],
                color=color, alpha=0.5, linewidth=0, zorder=7)


    # Draw intermediate points (finer lattice) - 18 points with colors based on angle
    n_intermediate = 18
    angles_intermediate = np.linspace(0, 2*np.pi, n_intermediate, endpoint=False) + np.pi/6
    r_intermediate = weight_radius * 0.75

    for i, angle in enumerate(angles_intermediate):
        x = r_intermediate * np.cos(angle)
        y = r_intermediate * np.sin(angle)

        # Color based on angular position (R, G, B sectors)
        # Apply same hue offset as outer ring to align colors
        a_norm = (angle - hue_offset) % (2*np.pi)
        if a_norm < 2*np.pi/3:
            # R to G sector
            frac = a_norm / (2*np.pi/3)
            color = (0.9-0.5*frac, 0.3+0.5*frac, 0.2)
        elif a_norm < 4*np.pi/3:
            # G to B sector
            frac = (a_norm - 2*np.pi/3) / (2*np.pi/3)
            color = (0.4-0.2*frac, 0.8-0.5*frac, 0.2+0.6*frac)
        else:
            # B to R sector
            frac = (a_norm - 4*np.pi/3) / (2*np.pi/3)
            color = (0.2+0.7*frac, 0.3, 0.8-0.6*frac)

        ax.scatter(x, y, s=50, c=[color], edgecolors='black', linewidth=0.5, zorder=4, alpha=0.9)

    # Store intermediate positions for connections
    intermediate_positions = [(r_intermediate * np.cos(a), r_intermediate * np.sin(a))
                              for a in angles_intermediate]

    # Draw discrete points (original 6 vertices) - innermost
    weights = get_stella_weights()
    weight_colors_list = [COLOR_R, COLOR_G, COLOR_B, COLOR_RBAR, COLOR_GBAR, COLOR_BBAR]
    weight_names = ['R', 'G', 'B', r'$\bar{\mathrm{R}}$', r'$\bar{\mathrm{G}}$', r'$\bar{\mathrm{B}}$']

    r_discrete = weight_radius * 0.45
    discrete_angles = [np.pi/6, 5*np.pi/6, -np.pi/2, -5*np.pi/6, np.pi/2, -np.pi/6]  # R, G, B, R̄, B̄, Ḡ

    # Draw connections between all discrete points (complete graph)
    for i in range(6):
        for j in range(i + 1, 6):
            angle1 = discrete_angles[i]
            angle2 = discrete_angles[j]
            x1, y1 = r_discrete * np.cos(angle1), r_discrete * np.sin(angle1)
            x2, y2 = r_discrete * np.cos(angle2), r_discrete * np.sin(angle2)
            ax.plot([x1, x2], [y1, y2], color='#2C3E50', linewidth=1.2, alpha=0.7, zorder=3)

    # Draw connections from discrete points to intermediate points
    for i, d_angle in enumerate(discrete_angles):
        x_d = r_discrete * np.cos(d_angle)
        y_d = r_discrete * np.sin(d_angle)
        # Connect to all intermediate points
        for x_int, y_int in intermediate_positions:
            ax.plot([x_d, x_int], [y_d, y_int], color='gray', linewidth=0.4, alpha=0.3, zorder=2)

    # Draw connections from intermediate points to continuous ring (many points)
    r_ring = weight_radius  # radius of continuous ring
    n_ring_points = 36  # points along the continuous ring
    ring_angles = np.linspace(0, 2*np.pi, n_ring_points, endpoint=False)

    for int_angle in angles_intermediate:
        x_int = r_intermediate * np.cos(int_angle)
        y_int = r_intermediate * np.sin(int_angle)
        # Connect to all ring points
        for ring_angle in ring_angles:
            x_ring = r_ring * np.cos(ring_angle)
            y_ring = r_ring * np.sin(ring_angle)
            ax.plot([x_int, x_ring], [y_int, y_ring], color='gray', linewidth=0.28, alpha=0.10, zorder=1)

    for i, (angle, color, name) in enumerate(zip(discrete_angles, weight_colors_list, weight_names)):
        x = r_discrete * np.cos(angle)
        y = r_discrete * np.sin(angle)
        ax.scatter(x, y, s=120, c=color, edgecolors='black', linewidth=1.5, zorder=5)
        # Label inside the circle - use black text for light colors (anti-colors, indices 3,4,5)
        text_color = 'black' if i >= 3 else 'white'
        # Shift anti-color labels down slightly to show the bar
        y_offset = -0.012 if i >= 3 else 0
        ax.text(x, y + y_offset, name,
               fontsize=7, ha='center', va='center', fontweight='bold', color=text_color, zorder=6)


    # Draw arrows showing the progression: discrete → intermediate → continuous
    arrow_style = dict(arrowstyle='->', color='black', lw=1.5)
    ax.annotate('', xy=(r_intermediate*0.85, 0), xytext=(r_discrete*1.15, 0),
               arrowprops=arrow_style)
    ax.annotate('', xy=(weight_radius*0.95, 0), xytext=(r_intermediate*1.1, 0),
               arrowprops=arrow_style)

    # Center point
    ax.scatter(0, 0, s=50, c='white', edgecolors='black', linewidth=1.5, zorder=6)

    # Z₃ symmetry indicator - show 120° sectors
    for angle in [np.pi/6, np.pi/6 + 2*np.pi/3, np.pi/6 + 4*np.pi/3]:
        ax.plot([0, weight_radius*1.15*np.cos(angle)],
                [0, weight_radius*1.15*np.sin(angle)],
                'k--', alpha=0.3, linewidth=1)

    # Legend in upper right
    from matplotlib.patches import Circle as LegendCircle
    from matplotlib.lines import Line2D

    # Create custom legend handles
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_R,
               markersize=10, markeredgecolor='black', markeredgewidth=1.5,
               label=r'$a = a_0$ (discrete)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='#7a9e7a',
               markersize=8, markeredgecolor='black', markeredgewidth=0.5,
               label=r'$a = a_1$ (finer)'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='#e07050',
               markersize=10, markeredgecolor='black', markeredgewidth=0.5,
               alpha=0.6, label=r'$a \to 0$ (continuous)'),
    ]

    ax.legend(handles=legend_elements, loc='upper left', fontsize=7,
             framealpha=0.95, edgecolor='gray', bbox_to_anchor=(-0.15, 1.0))

    # Axis settings
    ax.set_xlim(-0.85, 0.85)
    ax.set_ylim(-0.85, 0.85)
    ax.set_aspect('equal')
    ax.axis('off')

    ax.set_title(r'(b) Continuum Limit: Discrete $\to$ Continuous', fontsize=12, fontweight='bold')

    # Bottom annotation
    ax.text(0.5, 0.02, r'$\mathbb{Z}_3$ symmetry preserved at all scales',
           transform=ax.transAxes, fontsize=9, ha='center', va='bottom',
           bbox=dict(boxstyle='round', facecolor='white', alpha=0.8, edgecolor='gray'))

# ============================================================================
# MAIN FIGURE
# ============================================================================

def generate_figure():
    """
    Generate the two-panel continuum limit figure.
    """
    # Publication settings
    plt.rcParams.update({
        'font.size': 10,
        'axes.labelsize': 11,
        'axes.titlesize': 12,
        'legend.fontsize': 9,
        'xtick.labelsize': 9,
        'ytick.labelsize': 9,
        'font.family': 'serif',
        'mathtext.fontset': 'dejavuserif',
    })

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4.5))

    # Panel A: Root system
    draw_root_system(ax1)

    # Panel B: Continuum limit
    draw_continuum_limit(ax2)

    plt.tight_layout()

    # Save
    png_path = OUTPUT_DIR / 'fig_continuum_limit.png'
    pdf_path = OUTPUT_DIR / 'fig_continuum_limit.pdf'

    plt.savefig(png_path, dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(pdf_path, bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Saved: {png_path}")
    print(f"Saved: {pdf_path}")

    return png_path, pdf_path


def print_physics_summary():
    """Print the key physics being visualized."""
    print("\n" + "="*60)
    print("Continuum Limit Figure - Physics Summary")
    print("="*60)

    weights = get_stella_weights()
    roots, alpha1, alpha2 = get_a2_roots()

    print("\nPanel (a): A₂ Root System")
    print("-" * 40)
    print("Simple roots from weight differences:")
    print(f"  α₁ = w_R - w_G = {alpha1}")
    print(f"  α₂ = w_G - w_B = {alpha2}")
    print(f"  Angle between simple roots: 120°")
    print(f"  Cartan matrix: [[2, -1], [-1, 2]]")

    print("\nPanel (b): Discrete → Continuous Limit")
    print("-" * 40)
    print("  Discrete: 8 stella vertices (6 weights + 2 apex)")
    print("  Continuous: SU(3) Lie group (8-dimensional)")
    print("  Preserved: Z₃ center structure")
    print("  Key identity: 1 + ω + ω² = 0 (cube roots of unity)")
    print("="*60 + "\n")


if __name__ == "__main__":
    print_physics_summary()
    generate_figure()
