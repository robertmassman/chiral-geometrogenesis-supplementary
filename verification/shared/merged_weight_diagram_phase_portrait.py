#!/usr/bin/env python3
"""
Merged Visualization: SU(3) Weight Diagram + Phase Portrait
============================================================

This script creates a unified figure showing how the geometric structure
of SU(3) (weight diagram) emerges from the dynamical phase evolution
(Sakaguchi-Kuramoto phase portrait).

The connection:
- Left panel: SU(3) weight diagram shows the ALGEBRAIC structure
  (cube roots of unity defining color charge positions)
- Right panel: Phase portrait shows the DYNAMICAL emergence
  (how the system evolves to the 120° locked state)
- The 120° phase separation in dynamics corresponds exactly to
  the cube roots of unity in the weight diagram

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Circle, Polygon
from matplotlib.gridspec import GridSpec
from scipy.integrate import odeint
from pathlib import Path

# ============================================================================
# CONSTANTS
# ============================================================================

ALPHA = 2 * np.pi / 3  # Phase frustration parameter (120°)

# ============================================================================
# DYNAMICAL SYSTEM (from Theorem 2.2.1)
# ============================================================================

def phase_difference_dynamics(psi: np.ndarray, t: float, K: float) -> np.ndarray:
    """
    Phase-difference dynamics (reduced 2D system) from symmetric
    Sakaguchi-Kuramoto model.

    ψ₁ = φ_G - φ_R,  ψ₂ = φ_B - φ_G
    """
    psi1, psi2 = psi
    alpha = ALPHA

    dpsi1 = (K/2) * (
        np.sin(-psi1 - alpha) + np.sin(psi2 - alpha)
        - np.sin(psi1 - alpha) - np.sin(psi1 + psi2 - alpha)
    )

    dpsi2 = (K/2) * (
        np.sin(-psi1 - psi2 - alpha) + np.sin(-psi2 - alpha)
        - np.sin(-psi1 - alpha) - np.sin(psi2 - alpha)
    )

    return np.array([dpsi1, dpsi2])

# ============================================================================
# WEIGHT DIAGRAM PANEL
# ============================================================================

def plot_weight_diagram(ax, show_phases=True):
    """
    Plot the SU(3) weight diagram with fundamental (3) and anti-fundamental (3̄)
    representations, emphasizing the connection to cube roots of unity.
    """
    # Fundamental representation weights (quarks)
    # Using standard normalization: T_3 (isospin), Y (hypercharge)
    w_R = np.array([0.5, 1/(2*np.sqrt(3))])
    w_G = np.array([-0.5, 1/(2*np.sqrt(3))])
    w_B = np.array([0, -1/np.sqrt(3)])

    # Anti-fundamental weights
    w_Rbar = -w_R
    w_Gbar = -w_G
    w_Bbar = -w_B

    # Draw triangles with fill
    fund_verts = np.array([w_R, w_G, w_B])
    fund_tri = Polygon(fund_verts, fill=True, facecolor='blue', alpha=0.15,
                       edgecolor='blue', linewidth=2.5, linestyle='-')
    ax.add_patch(fund_tri)

    antifund_verts = np.array([w_Rbar, w_Gbar, w_Bbar])
    anti_tri = Polygon(antifund_verts, fill=True, facecolor='red', alpha=0.15,
                       edgecolor='red', linewidth=2.5, linestyle='--')
    ax.add_patch(anti_tri)

    # Plot vertices - fundamental (circles)
    colors_fund = ['#D32F2F', '#388E3C', '#1976D2']  # Material design colors
    labels_fund = ['R', 'G', 'B']
    for w, c, l in zip([w_R, w_G, w_B], colors_fund, labels_fund):
        ax.scatter(*w, c=c, s=300, zorder=10, edgecolor='black', linewidth=2)
        offset = np.array([0.08, 0.06]) if l != 'B' else np.array([0.08, -0.10])
        ax.annotate(l, w + offset, fontsize=16, fontweight='bold', color=c)

    # Plot vertices - anti-fundamental (squares)
    colors_anti = ['#EF9A9A', '#A5D6A7', '#90CAF9']  # Lighter versions
    labels_anti = ['R̄', 'Ḡ', 'B̄']
    for w, c, l in zip([w_Rbar, w_Gbar, w_Bbar], colors_anti, labels_anti):
        ax.scatter(*w, c=c, s=250, zorder=10, edgecolor='black', linewidth=2, marker='s')
        offset = np.array([-0.15, -0.08])
        ax.annotate(l, w + offset, fontsize=14, color='gray')

    # Origin (singlet)
    ax.scatter(0, 0, c='black', s=150, marker='+', zorder=10, linewidth=3)
    ax.annotate('O\n(singlet)', (0.05, -0.12), fontsize=10, ha='left')

    # Show phase angles if requested
    if show_phases:
        # Draw phase angle annotations
        r_label = 0.45
        for angle, label, color in [(0, '0°', '#D32F2F'),
                                    (120, '120°', '#388E3C'),
                                    (240, '240°', '#1976D2')]:
            rad = np.radians(angle)
            # Small arc showing angle
            arc_angles = np.linspace(0, rad, 30)
            arc_r = 0.25
            if angle > 0:
                ax.plot(arc_r * np.cos(arc_angles), arc_r * np.sin(arc_angles),
                       color=color, linewidth=1.5, alpha=0.7)

    # Root vector α₁
    ax.annotate('', xy=w_R, xytext=w_G,
                arrowprops=dict(arrowstyle='->', color='purple', lw=2))
    ax.annotate('α₁', (0, w_R[1] + 0.08), fontsize=12, color='purple', ha='center')

    # Axis labels and styling
    ax.set_xlim(-0.75, 0.75)
    ax.set_ylim(-0.75, 0.75)
    ax.set_xlabel('$T_3$ (Isospin)', fontsize=12)
    ax.set_ylabel('$Y$ (Hypercharge)', fontsize=12)
    ax.set_title('SU(3) Weight Diagram\n(Algebraic Structure)', fontsize=14, fontweight='bold')
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3, linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='k', linewidth=0.8, alpha=0.5)
    ax.axvline(x=0, color='k', linewidth=0.8, alpha=0.5)

    # Legend
    from matplotlib.patches import Patch
    from matplotlib.lines import Line2D
    legend_elements = [
        Patch(facecolor='blue', alpha=0.3, edgecolor='blue', linewidth=2,
              label='Fundamental (3)'),
        Patch(facecolor='red', alpha=0.3, edgecolor='red', linewidth=2,
              linestyle='--', label='Anti-fundamental (3̄)'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=9)

# ============================================================================
# PHASE PORTRAIT PANEL
# ============================================================================

def plot_phase_portrait(ax, K=1.0):
    """
    Plot phase portrait showing dynamics converging to 120° locked state.
    """
    # Vector field
    n_grid = 18
    psi1_grid = np.linspace(0, 2*np.pi, n_grid)
    psi2_grid = np.linspace(0, 2*np.pi, n_grid)
    PSI1, PSI2 = np.meshgrid(psi1_grid, psi2_grid)

    DPSI1 = np.zeros_like(PSI1)
    DPSI2 = np.zeros_like(PSI2)

    for i in range(n_grid):
        for j in range(n_grid):
            psi = np.array([PSI1[i, j], PSI2[i, j]])
            dpsi = phase_difference_dynamics(psi, 0, K)
            DPSI1[i, j] = dpsi[0]
            DPSI2[i, j] = dpsi[1]

    # Normalize for visualization
    magnitude = np.sqrt(DPSI1**2 + DPSI2**2)
    magnitude[magnitude == 0] = 1
    DPSI1_norm = DPSI1 / magnitude
    DPSI2_norm = DPSI2 / magnitude

    # Plot vector field with color indicating flow speed
    Q = ax.quiver(np.degrees(PSI1), np.degrees(PSI2), DPSI1_norm, DPSI2_norm,
                  magnitude, cmap='plasma', alpha=0.6, scale=25)

    # Sample trajectories converging to FP1 (the "good" chirality)
    np.random.seed(42)
    t_span = np.linspace(0, 40, 400)

    # Trajectories to FP1 (blue region)
    for _ in range(8):
        psi0 = np.array([np.random.uniform(0, 2*np.pi/3 + 0.5),
                        np.random.uniform(0, 2*np.pi/3 + 0.5)])
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))
        ax.plot(np.degrees(solution[:, 0] % (2*np.pi)),
               np.degrees(solution[:, 1] % (2*np.pi)),
               'b-', alpha=0.6, linewidth=1.2)

    # Trajectories to FP2 (red region)
    for _ in range(8):
        psi0 = np.array([np.random.uniform(np.pi, 2*np.pi),
                        np.random.uniform(np.pi, 2*np.pi)])
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))
        ax.plot(np.degrees(solution[:, 0] % (2*np.pi)),
               np.degrees(solution[:, 1] % (2*np.pi)),
               'r-', alpha=0.6, linewidth=1.2)

    # Mark fixed points with clear styling
    # FP1: Stable attractor (R→G→B chirality) - corresponds to fundamental triangle
    ax.plot(120, 120, 'o', color='#1976D2', markersize=18,
           markeredgecolor='black', markeredgewidth=2, zorder=15)
    ax.annotate('FP₁\n(120°, 120°)\nR→G→B', (130, 130), fontsize=10,
               fontweight='bold', color='#1976D2',
               bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.8))

    # FP2: Stable attractor (R→B→G chirality) - corresponds to anti-fundamental
    ax.plot(240, 240, 'o', color='#D32F2F', markersize=18,
           markeredgecolor='black', markeredgewidth=2, zorder=15)
    ax.annotate('FP₂\n(240°, 240°)\nR→B→G', (250, 250), fontsize=10,
               fontweight='bold', color='#D32F2F',
               bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.8))

    # FP3: Unstable (synchronized state)
    ax.plot(0, 0, 's', color='gray', markersize=12,
           markeredgecolor='black', markeredgewidth=2, zorder=15)
    ax.annotate('Unstable\n(sync)', (10, 20), fontsize=9, color='gray')

    # Styling
    ax.set_xlabel('ψ₁ = φ_G − φ_R (degrees)', fontsize=12)
    ax.set_ylabel('ψ₂ = φ_B − φ_G (degrees)', fontsize=12)
    ax.set_title('Phase Portrait on 𝕋²\n(Dynamical Evolution)', fontsize=14, fontweight='bold')
    ax.set_xlim(0, 360)
    ax.set_ylim(0, 360)
    ax.set_xticks([0, 60, 120, 180, 240, 300, 360])
    ax.set_yticks([0, 60, 120, 180, 240, 300, 360])
    ax.grid(True, alpha=0.3)
    ax.set_aspect('equal')

# ============================================================================
# CONNECTION PANEL (Center)
# ============================================================================

def plot_connection_diagram(ax):
    """
    Plot the conceptual connection between weight diagram and phase dynamics.
    Shows how the cube roots of unity ω = e^(2πi/3) connect both representations.
    """
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')

    # Title
    ax.text(0.5, 0.95, 'Connection: Geometry ↔ Dynamics',
            fontsize=13, fontweight='bold', ha='center', va='top')

    # Key insight box
    insight_text = (
        "The SU(3) color structure\n"
        "emerges dynamically:\n\n"
        "• Cube roots of unity\n"
        "   ω = e^(2πi/3)\n"
        "   1 + ω + ω² = 0\n\n"
        "• Phase locking at 120°\n"
        "   φ_G − φ_R = 2π/3\n"
        "   φ_B − φ_G = 2π/3\n\n"
        "• Color neutrality\n"
        "   e^(iφ_R) + e^(iφ_G) + e^(iφ_B) = 0"
    )
    ax.text(0.5, 0.55, insight_text, fontsize=11, ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow',
                     edgecolor='orange', linewidth=2),
            family='monospace')

    # Arrows indicating the connection
    ax.annotate('', xy=(0.1, 0.5), xytext=(0.0, 0.5),
                arrowprops=dict(arrowstyle='->', color='green', lw=3))
    ax.annotate('', xy=(1.0, 0.5), xytext=(0.9, 0.5),
                arrowprops=dict(arrowstyle='->', color='green', lw=3))

    # Bottom annotation
    ax.text(0.5, 0.08,
            'Static algebraic structure ← Sakaguchi-Kuramoto dynamics → Stable fixed points',
            fontsize=9, ha='center', va='bottom', style='italic')

# ============================================================================
# MAIN FIGURE
# ============================================================================

def create_merged_figure():
    """
    Create the merged 3-panel figure showing weight diagram, connection, and phase portrait.
    """
    # Use GridSpec for flexible layout
    fig = plt.figure(figsize=(18, 7))
    gs = GridSpec(1, 5, width_ratios=[2, 0.3, 1.2, 0.3, 2], wspace=0.1)

    # Left panel: Weight diagram
    ax1 = fig.add_subplot(gs[0])
    plot_weight_diagram(ax1)

    # Left arrow
    ax_arrow1 = fig.add_subplot(gs[1])
    ax_arrow1.axis('off')
    ax_arrow1.annotate('', xy=(0.9, 0.5), xytext=(0.1, 0.5),
                       arrowprops=dict(arrowstyle='->', color='#4CAF50', lw=4,
                                      connectionstyle='arc3,rad=0'))
    ax_arrow1.text(0.5, 0.65, 'emerges\nfrom', fontsize=10, ha='center', va='bottom',
                  color='#4CAF50', fontweight='bold')

    # Center panel: Connection explanation
    ax2 = fig.add_subplot(gs[2])
    plot_connection_diagram(ax2)

    # Right arrow
    ax_arrow2 = fig.add_subplot(gs[3])
    ax_arrow2.axis('off')
    ax_arrow2.annotate('', xy=(0.1, 0.5), xytext=(0.9, 0.5),
                       arrowprops=dict(arrowstyle='->', color='#4CAF50', lw=4,
                                      connectionstyle='arc3,rad=0'))
    ax_arrow2.text(0.5, 0.65, 'drives', fontsize=10, ha='center', va='bottom',
                  color='#4CAF50', fontweight='bold')

    # Right panel: Phase portrait
    ax3 = fig.add_subplot(gs[4])
    plot_phase_portrait(ax3)

    # Main title
    fig.suptitle('Geometric Emergence: SU(3) Structure from Phase Dynamics',
                fontsize=16, fontweight='bold', y=0.98)

    # Subtitle
    fig.text(0.5, 0.02,
            'Theorems 0.0.3 (Stella Uniqueness) & 2.2.1 (Phase-Locked Oscillation) — '
            'The color field phases dynamically lock to the SU(3) weight structure',
            ha='center', fontsize=10, style='italic')

    plt.tight_layout(rect=[0, 0.04, 1, 0.95])

    return fig


def create_compact_figure():
    """
    Create a more compact 2-panel figure (side by side).
    """
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))

    # Left: Weight diagram
    plot_weight_diagram(axes[0])

    # Right: Phase portrait
    plot_phase_portrait(axes[1])

    # Connection annotation between panels
    fig.text(0.5, 0.5, '⟷', fontsize=40, ha='center', va='center',
            transform=fig.transFigure, color='#4CAF50', fontweight='bold')

    # Main title
    fig.suptitle('Geometric Emergence: SU(3) Weight Structure ↔ Phase Dynamics',
                fontsize=16, fontweight='bold', y=0.98)

    # Subtitle explaining connection
    fig.text(0.5, 0.02,
            'The 120° phase locking (right) realizes the cube-roots-of-unity structure (left): '
            '1 + ω + ω² = 0 ↔ e^(iφ_R) + e^(iφ_G) + e^(iφ_B) = 0',
            ha='center', fontsize=11, style='italic')

    plt.tight_layout(rect=[0, 0.05, 1, 0.95])

    return fig


def main():
    """Generate and save the merged figure."""

    # Create output directory
    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    print("Generating merged Weight Diagram + Phase Portrait figure...")

    # Create the full 3-panel figure
    fig1 = create_merged_figure()
    output_path1 = output_dir / "merged_weight_diagram_phase_portrait.png"
    fig1.savefig(output_path1, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {output_path1}")
    plt.close(fig1)

    # Create compact 2-panel version
    fig2 = create_compact_figure()
    output_path2 = output_dir / "merged_weight_diagram_phase_portrait_compact.png"
    fig2.savefig(output_path2, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {output_path2}")
    plt.close(fig2)

    print("\nMerged figures generated successfully!")
    print("\nKey insight shown:")
    print("  • Left panel: SU(3) weight diagram (algebraic structure)")
    print("  • Right panel: Phase portrait (dynamical system)")
    print("  • Connection: 120° phase locking ↔ cube roots of unity")
    print("  • The geometry EMERGES from the dynamics")


if __name__ == "__main__":
    main()
