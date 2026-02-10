#!/usr/bin/env python3
"""
Theorem 5.1.2: Vacuum Energy Density — Visualization
=====================================================

This script generates publication-quality plots for Theorem 5.1.2:

1. Stella octangula geometry (two interlocked tetrahedra)
2. Position-dependent vacuum energy profile
3. Scale hierarchy and suppression diagram
4. Phase cancellation visualization
5. Holographic derivation chain

Output: verification/plots/theorem_5_1_2_*.png

Verification Date: 2026-02-05
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
import matplotlib.gridspec as gridspec
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle, Wedge
import matplotlib.colors as mcolors
import os

# Create output directory
os.makedirs('plots', exist_ok=True)

# Set style
plt.style.use('default')
plt.rcParams.update({
    'figure.facecolor': 'white',
    'axes.facecolor': 'white',
    'font.family': 'sans-serif',
    'font.size': 11,
    'axes.labelsize': 12,
    'axes.titlesize': 14,
    'legend.fontsize': 10
})

# Physical constants
M_P_GEV = 1.22e19
H_0_GEV = 1.44e-42
OMEGA_LAMBDA = 0.685
RHO_OBS_GEV4 = 2.5e-47

# ==============================================================================
# HELPER FUNCTIONS
# ==============================================================================

def stella_octangula_vertices():
    """
    Return vertices of stella octangula (two interlocked tetrahedra).

    The stella octangula is a compound of two interpenetrating tetrahedra.
    NOT an octahedron.
    """
    # First tetrahedron T+ (alternating cube corners)
    tet1 = np.array([
        [+1, +1, +1],
        [+1, -1, -1],
        [-1, +1, -1],
        [-1, -1, +1]
    ]) / np.sqrt(3)

    # Second tetrahedron T- (other alternating cube corners)
    tet2 = np.array([
        [-1, -1, -1],
        [-1, +1, +1],
        [+1, -1, +1],
        [+1, +1, -1]
    ]) / np.sqrt(3)

    return tet1, tet2


def tetrahedron_faces(vertices):
    """Return face indices for a tetrahedron."""
    return [
        [vertices[0], vertices[1], vertices[2]],
        [vertices[0], vertices[1], vertices[3]],
        [vertices[0], vertices[2], vertices[3]],
        [vertices[1], vertices[2], vertices[3]]
    ]


def pressure_function(x, x_c, epsilon=0.01):
    """Pressure function P_c(x) = 1/(|x - x_c|² + ε²)."""
    if x.ndim == 1:
        r_sq = np.sum((x - x_c)**2)
    else:
        r_sq = np.sum((x - x_c)**2, axis=-1)
    return 1.0 / (r_sq + epsilon**2)


def compute_vev_squared(x, color_vertices, epsilon=0.01):
    """Compute v_χ²(x) from pressure functions."""
    if x.ndim == 1:
        P = np.array([pressure_function(x, x_c, epsilon) for x_c in color_vertices])
    else:
        P = np.array([pressure_function(x, x_c, epsilon) for x_c in color_vertices])
        P = P.T  # Shape: (N_points, 3)

    # v_χ² = (a₀²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]
    if P.ndim == 1:
        v_sq = 0.5 * ((P[0] - P[1])**2 + (P[1] - P[2])**2 + (P[2] - P[0])**2)
    else:
        v_sq = 0.5 * ((P[:, 0] - P[:, 1])**2 + (P[:, 1] - P[:, 2])**2 + (P[:, 2] - P[:, 0])**2)

    return v_sq


# ==============================================================================
# FIGURE 1: STELLA OCTANGULA GEOMETRY
# ==============================================================================

def plot_stella_octangula():
    """Plot the stella octangula with two interlocked tetrahedra."""
    print("Generating: Stella Octangula Geometry...")

    fig = plt.figure(figsize=(14, 6))

    # Left: 3D view
    ax1 = fig.add_subplot(121, projection='3d')

    tet1, tet2 = stella_octangula_vertices()

    # Draw first tetrahedron (red)
    faces1 = tetrahedron_faces(tet1)
    poly1 = Poly3DCollection(faces1, alpha=0.4, facecolor='red', edgecolor='darkred', linewidth=1.5)
    ax1.add_collection3d(poly1)

    # Draw second tetrahedron (blue)
    faces2 = tetrahedron_faces(tet2)
    poly2 = Poly3DCollection(faces2, alpha=0.4, facecolor='blue', edgecolor='darkblue', linewidth=1.5)
    ax1.add_collection3d(poly2)

    # Plot vertices
    ax1.scatter(*tet1.T, s=100, c='red', marker='o', label='T₊ vertices (4)')
    ax1.scatter(*tet2.T, s=100, c='blue', marker='^', label='T₋ vertices (4)')

    # Mark center
    ax1.scatter([0], [0], [0], s=200, c='gold', marker='*', edgecolors='black',
                linewidths=1.5, label='Center (ρ_vac = 0)', zorder=10)

    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Stella Octangula\n(Two Interlocked Tetrahedra)', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left', fontsize=9)

    # Set equal aspect ratio
    ax1.set_xlim(-1, 1)
    ax1.set_ylim(-1, 1)
    ax1.set_zlim(-1, 1)

    # Right: Comparison with octahedron
    ax2 = fig.add_subplot(122)
    ax2.axis('off')

    comparison_text = """
    STELLA OCTANGULA vs OCTAHEDRON
    ═══════════════════════════════════

    Property          Stella Octangula    Octahedron
    ─────────────────────────────────────────────────
    Vertices                8 (4+4)              6
    Edges                  12 (6+6)             12
    Faces                   8 (4+4)              8
    Components                  2                1
    Euler χ                     4                2
    Surface topology       Two S²           One S²

    ═══════════════════════════════════

    KEY INSIGHT:
    The stella octangula provides DISJOINT
    surfaces for the color fields to live on.

    This enables the phase cancellation
    mechanism (1 + ω + ω² = 0) that
    suppresses vacuum energy at the center.
    """

    ax2.text(0.1, 0.95, comparison_text, fontsize=11, fontfamily='monospace',
             verticalalignment='top', transform=ax2.transAxes)

    plt.tight_layout()
    plt.savefig('plots/theorem_5_1_2_stella_octangula.png', dpi=150, bbox_inches='tight')
    plt.close()
    print("  Saved: plots/theorem_5_1_2_stella_octangula.png")


# ==============================================================================
# FIGURE 2: VACUUM ENERGY PROFILE
# ==============================================================================

def plot_vacuum_energy_profile():
    """Plot position-dependent vacuum energy density."""
    print("Generating: Vacuum Energy Profile...")

    fig = plt.figure(figsize=(18, 6))

    # Color vertex positions (equilateral triangle in xy-plane)
    color_vertices = np.array([
        [1, 0, 0],
        [-0.5, np.sqrt(3)/2, 0],
        [-0.5, -np.sqrt(3)/2, 0]
    ])
    color_vertices = color_vertices / np.linalg.norm(color_vertices[0])
    epsilon = 0.01

    N = 150

    # Panel A: XY slice (z=0 plane)
    ax1 = fig.add_subplot(131)

    x = np.linspace(-1.5, 1.5, N)
    y = np.linspace(-1.5, 1.5, N)
    X_xy, Y_xy = np.meshgrid(x, y)

    # Compute v_χ² on grid
    points_xy = np.stack([X_xy.ravel(), Y_xy.ravel(), np.zeros_like(X_xy.ravel())], axis=-1)
    v_sq_xy = compute_vev_squared(points_xy, color_vertices, epsilon)
    V_SQ_xy = v_sq_xy.reshape(N, N)

    # Vacuum energy ρ = λ v⁴ (λ=1)
    RHO_xy = V_SQ_xy**2

    # Plot with log scale
    im1 = ax1.contourf(X_xy, Y_xy, np.log10(RHO_xy + 1e-20), levels=50, cmap='viridis')
    plt.colorbar(im1, ax=ax1, label='log₁₀(ρ_vac)')

    # Mark color vertices
    colors = ['red', 'green', 'blue']
    labels = ['R', 'G', 'B']
    for i, (v, c, l) in enumerate(zip(color_vertices, colors, labels)):
        ax1.plot(v[0], v[1], 'o', color=c, markersize=12, markeredgecolor='white',
                 markeredgewidth=2, label=f'χ_{l}')

    # Mark center
    ax1.plot(0, 0, '*', color='gold', markersize=20, markeredgecolor='black',
             markeredgewidth=1.5, label='Center (ρ=0)')

    ax1.set_xlabel('x')
    ax1.set_ylabel('y')
    ax1.set_title('(A) XY Slice: ρ_vac(x,y,0)\nLog Scale', fontsize=12, fontweight='bold')
    ax1.legend(loc='upper right', fontsize=8)
    ax1.set_aspect('equal')

    # Panel B: XZ slice (y=0 plane)
    ax2 = fig.add_subplot(132)

    x = np.linspace(-1.5, 1.5, N)
    z = np.linspace(-1.5, 1.5, N)
    X_xz, Z_xz = np.meshgrid(x, z)

    # Compute v_χ² on XZ grid (y=0)
    points_xz = np.stack([X_xz.ravel(), np.zeros_like(X_xz.ravel()), Z_xz.ravel()], axis=-1)
    v_sq_xz = compute_vev_squared(points_xz, color_vertices, epsilon)
    V_SQ_xz = v_sq_xz.reshape(N, N)

    # Vacuum energy ρ = λ v⁴ (λ=1)
    RHO_xz = V_SQ_xz**2

    # Plot with log scale (same colormap range as Panel A for consistency)
    vmin = min(np.log10(RHO_xy + 1e-20).min(), np.log10(RHO_xz + 1e-20).min())
    vmax = max(np.log10(RHO_xy + 1e-20).max(), np.log10(RHO_xz + 1e-20).max())
    im2 = ax2.contourf(X_xz, Z_xz, np.log10(RHO_xz + 1e-20), levels=50, cmap='viridis',
                        vmin=vmin, vmax=vmax)
    plt.colorbar(im2, ax=ax2, label='log₁₀(ρ_vac)')

    # Mark where color vertices intersect this plane (only χ_R at x=1, y=0)
    ax2.plot(color_vertices[0, 0], 0, 'o', color='red', markersize=12,
             markeredgecolor='white', markeredgewidth=2, label='χ_R (y=0)')

    # Mark center
    ax2.plot(0, 0, '*', color='gold', markersize=20, markeredgecolor='black',
             markeredgewidth=1.5, label='Center (ρ=0)')

    ax2.set_xlabel('x')
    ax2.set_ylabel('z')
    ax2.set_title('(B) XZ Slice: ρ_vac(x,0,z)\nLog Scale', fontsize=12, fontweight='bold')
    ax2.legend(loc='upper right', fontsize=8)
    ax2.set_aspect('equal')

    # Panel C: Radial profile
    ax3 = fig.add_subplot(133)

    radii = np.linspace(0, 4.0, 400)
    rho_radial = []
    v_chi_radial = []

    for r in radii:
        point = np.array([r, 0, 0])
        v_sq = compute_vev_squared(point, color_vertices, epsilon)
        v_chi_radial.append(np.sqrt(max(0, v_sq)))
        rho_radial.append(max(0, v_sq)**2)

    ax3.semilogy(radii, rho_radial, 'b-', linewidth=2, label='ρ_vac(r)')
    ax3.axvline(x=1.0, color='red', linestyle='--', alpha=0.7, label='Color vertex (r=1)')
    ax3.axhline(y=1e-10, color='gray', linestyle=':', alpha=0.5)

    # Mark r⁴ scaling region
    r_fit = radii[(radii > 0.01) & (radii < 0.2)]
    rho_fit = np.array(rho_radial)[(radii > 0.01) & (radii < 0.2)]
    if len(r_fit) > 0:
        # Fit power law
        log_r = np.log(r_fit)
        log_rho = np.log(rho_fit + 1e-30)
        coeffs = np.polyfit(log_r, log_rho, 1)
        power = coeffs[0]
        ax3.text(0.1, 1e-3, f'Near center: ρ ~ r^{power:.1f}', fontsize=11,
                 bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    ax3.set_xlabel('Radius r')
    ax3.set_ylabel('ρ_vac [arb. units]')
    ax3.set_title('(C) Radial Profile\nρ_vac(r) ~ r⁴ near center', fontsize=12, fontweight='bold')
    ax3.legend(fontsize=8)
    ax3.grid(True, alpha=0.3)
    ax3.set_xlim(0, 4.0)
    ax3.set_ylim(1e-15, 1e20)

    plt.tight_layout()
    plt.savefig('plots/theorem_5_1_2_vacuum_energy_profile.png', dpi=150, bbox_inches='tight')
    plt.close()
    print("  Saved: plots/theorem_5_1_2_vacuum_energy_profile.png")


# ==============================================================================
# FIGURE 3: PHASE CANCELLATION
# ==============================================================================

def plot_phase_cancellation():
    """Visualize the phase cancellation mechanism."""
    print("Generating: Phase Cancellation Diagram...")

    fig = plt.figure(figsize=(14, 5))

    # Left: Complex plane with cube roots of unity
    ax1 = fig.add_subplot(131)

    # Unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1)

    # Cube roots of unity
    omega = np.exp(2j * np.pi / 3)
    roots = [1, omega, omega**2]
    colors = ['red', 'green', 'blue']
    labels = ['χ_R: φ=0°', 'χ_G: φ=120°', 'χ_B: φ=240°']

    for r, c, l in zip(roots, colors, labels):
        ax1.plot(r.real, r.imag, 'o', color=c, markersize=15, markeredgecolor='black', markeredgewidth=2)
        ax1.annotate(l, (r.real, r.imag), xytext=(15, 10), textcoords='offset points',
                     fontsize=10, color=c, fontweight='bold')
        ax1.arrow(0, 0, r.real*0.85, r.imag*0.85, head_width=0.08, head_length=0.05,
                  fc=c, ec=c, alpha=0.7)

    # Sum = 0
    ax1.plot(0, 0, '*', color='gold', markersize=20, markeredgecolor='black',
             markeredgewidth=2, label='Sum = 0')

    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.axhline(y=0, color='gray', linewidth=0.5)
    ax1.axvline(x=0, color='gray', linewidth=0.5)
    ax1.set_xlabel('Re(z)', fontsize=12)
    ax1.set_ylabel('Im(z)', fontsize=12)
    ax1.set_title('SU(3) Cube Roots of Unity\n1 + ω + ω² = 0', fontsize=12, fontweight='bold')
    ax1.legend(loc='upper right')
    ax1.grid(True, alpha=0.2)

    # Middle: Vector addition
    ax2 = fig.add_subplot(132)

    # Draw vectors end-to-end
    start = 0
    for r, c, l in zip(roots, colors, ['1', 'ω', 'ω²']):
        end = start + r
        ax2.annotate('', xy=(end.real, end.imag), xytext=(start.real, start.imag),
                     arrowprops=dict(arrowstyle='->', color=c, lw=3))
        mid = (start + end) / 2
        ax2.text(mid.real + 0.1, mid.imag + 0.1, l, fontsize=12, color=c, fontweight='bold')
        start = end

    # Circle back to origin
    ax2.plot(0, 0, '*', color='gold', markersize=20, markeredgecolor='black',
             markeredgewidth=2, zorder=10)
    ax2.text(0.15, -0.15, 'Sum=0\n(closed triangle)', fontsize=10, ha='left')

    ax2.set_xlim(-0.8, 1.3)
    ax2.set_ylim(-1.2, 0.8)
    ax2.set_aspect('equal')
    ax2.axhline(y=0, color='gray', linewidth=0.5)
    ax2.axvline(x=0, color='gray', linewidth=0.5)
    ax2.set_title('Vector Addition\nForms Closed Triangle', fontsize=12, fontweight='bold')
    ax2.grid(True, alpha=0.2)

    # Right: Multi-scale table
    ax3 = fig.add_subplot(133)
    ax3.axis('off')

    table_text = """
    MULTI-SCALE PHASE CANCELLATION
    ══════════════════════════════════

    Scale   Group  N   Phases      Status
    ──────────────────────────────────────
    QCD     SU(3)  3   0°,120°,240°  ✅ PROVEN
    EW      SU(2)  2   0°,180°       🔸 PARTIAL
    GUT     SU(5)  5   0°,72°,...    🔸 PARTIAL
    Planck    ?    ?       ?         🔮 CONJECTURE

    ══════════════════════════════════

    KEY INSIGHT:
    N-th roots of unity always sum to zero:
    Σₖ e^(2πik/N) = 0  for all N ≥ 2

    But DYNAMICAL REALIZATION requires
    equal amplitudes — only proven at QCD!
    """

    ax3.text(0.05, 0.95, table_text, fontsize=10, fontfamily='monospace',
             verticalalignment='top', transform=ax3.transAxes)

    plt.tight_layout()
    plt.savefig('plots/theorem_5_1_2_phase_cancellation.png', dpi=150, bbox_inches='tight')
    plt.close()
    print("  Saved: plots/theorem_5_1_2_phase_cancellation.png")


# ==============================================================================
# FIGURE 4: SCALE HIERARCHY AND SUPPRESSION
# ==============================================================================

def plot_scale_hierarchy():
    """Plot the energy scale hierarchy and suppression mechanism."""
    print("Generating: Scale Hierarchy Diagram...")

    fig = plt.figure(figsize=(14, 8))
    gs = gridspec.GridSpec(2, 2, figure=fig, hspace=0.35, wspace=0.25)

    # Top left: Energy scale hierarchy
    ax1 = fig.add_subplot(gs[0, 0])

    scales = {
        'Planck': (19, '#e74c3c', 'M_P ~ 10¹⁹ GeV'),
        'GUT': (16, '#9b59b6', 'Λ_GUT ~ 10¹⁶ GeV'),
        'EW': (2, '#3498db', 'v_EW ~ 10² GeV'),
        'QCD': (-1, '#2ecc71', 'Λ_QCD ~ 10⁻¹ GeV'),
        'Hubble': (-42, '#f39c12', 'H₀ ~ 10⁻⁴² GeV'),
    }

    y_pos = np.arange(len(scales))
    values = [v[0] for v in scales.values()]
    colors = [v[1] for v in scales.values()]
    names = list(scales.keys())
    labels = [v[2] for v in scales.values()]

    bars = ax1.barh(y_pos, values, color=colors, alpha=0.7, edgecolor='black', linewidth=1.5)
    ax1.set_yticks(y_pos)
    ax1.set_yticklabels(names, fontsize=11, fontweight='bold')
    ax1.set_xlabel('log₁₀(Energy/GeV)', fontsize=12)
    ax1.set_title('Energy Scale Hierarchy', fontsize=13, fontweight='bold')

    for bar, label in zip(bars, labels):
        width = bar.get_width()
        x_pos = max(width + 1, 5)
        ax1.annotate(label, xy=(x_pos, bar.get_y() + bar.get_height()/2),
                     va='center', ha='left', fontsize=9)

    # Arrow showing span
    ax1.annotate('', xy=(19, 4.5), xytext=(-42, 4.5),
                 arrowprops=dict(arrowstyle='<->', color='red', lw=2))
    ax1.text(-10, 4.65, '61 orders of magnitude', fontsize=10, color='red', fontweight='bold')

    ax1.set_xlim(-50, 30)
    ax1.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
    ax1.grid(axis='x', alpha=0.3)

    # Top right: Vacuum energy estimates
    ax2 = fig.add_subplot(gs[0, 1])

    estimates = {
        'Planck (naive)': (76, '#e74c3c'),
        'GUT': (64, '#9b59b6'),
        'Electroweak': (8, '#3498db'),
        'QCD': (-3, '#2ecc71'),
        'M_P²H₀² formula': (-46, '#f39c12'),
        'Observed': (-47, '#27ae60'),
    }

    y_pos = np.arange(len(estimates))
    values = [v[0] for v in estimates.values()]
    colors = [v[1] for v in estimates.values()]
    names = list(estimates.keys())

    bars = ax2.barh(y_pos, values, color=colors, alpha=0.7, edgecolor='black', linewidth=1.5)
    ax2.set_yticks(y_pos)
    ax2.set_yticklabels(names, fontsize=10, fontweight='bold')
    ax2.set_xlabel('log₁₀(ρ/GeV⁴)', fontsize=12)
    ax2.set_title('Vacuum Energy Estimates', fontsize=13, fontweight='bold')

    # Highlight observed region
    ax2.axvline(x=-47, color='green', linestyle='--', linewidth=2, alpha=0.7)
    ax2.fill_betweenx([-0.5, len(estimates)-0.5], -48, -46, color='green', alpha=0.1)

    ax2.set_xlim(-60, 90)
    ax2.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
    ax2.grid(axis='x', alpha=0.3)

    # Bottom left: Suppression formula
    ax3 = fig.add_subplot(gs[1, 0])
    ax3.axis('off')

    formula_text = r"""
    THE 122-ORDER SUPPRESSION
    ═════════════════════════════════════

    Naive QFT:     ρ ~ M_P⁴ ~ 10⁷⁶ GeV⁴
    Observed:      ρ ~ 10⁻⁴⁷ GeV⁴
    ─────────────────────────────────────
    Discrepancy:   10¹²³ orders!

    ═════════════════════════════════════

    OUR MECHANISM:

         ρ_obs = M_P⁴ × (ℓ_P / L_H)²
               = M_P⁴ × (H₀ / M_P)²
               = M_P² × H₀²

    ═════════════════════════════════════

    This is NOT fine-tuning!

    The ratio (ℓ_P/L_H)² ~ 10⁻¹²² is the
    natural holographic bound relating
    the smallest (Planck) to the largest
    (Hubble) scales in the universe.
    """

    ax3.text(0.05, 0.95, formula_text, fontsize=11, fontfamily='monospace',
             verticalalignment='top', transform=ax3.transAxes)

    # Bottom right: Refined coefficient
    ax4 = fig.add_subplot(gs[1, 1])
    ax4.axis('off')

    coeff_text = r"""
    REFINED O(1) COEFFICIENT
    ═════════════════════════════════════

    From Friedmann equation:

        ρ_c = (3/8π) M_P² H₀²

    Dark energy fraction:

        ρ_Λ = Ω_Λ × ρ_c

    REFINED FORMULA:

        ρ_vac = (3Ω_Λ/8π) M_P² H₀²

    ═════════════════════════════════════

    NUMERICAL CHECK:

        Coefficient = 3 × 0.685 / 8π
                    = 0.0817

        ρ_predicted = 2.52 × 10⁻⁴⁷ GeV⁴
        ρ_observed  = 2.50 × 10⁻⁴⁷ GeV⁴

        AGREEMENT:  0.9% ✅

    ═════════════════════════════════════
    """

    ax4.text(0.05, 0.95, coeff_text, fontsize=11, fontfamily='monospace',
             verticalalignment='top', transform=ax4.transAxes)

    plt.savefig('plots/theorem_5_1_2_scale_hierarchy.png', dpi=150, bbox_inches='tight')
    plt.close()
    print("  Saved: plots/theorem_5_1_2_scale_hierarchy.png")


# ==============================================================================
# FIGURE 5: FOUR DERIVATIONS
# ==============================================================================

def plot_four_derivations():
    """Visualize the four independent derivations of ρ ~ M_P² H_0²."""
    print("Generating: Four Derivations Diagram...")

    fig = plt.figure(figsize=(14, 10))

    # Central result
    ax_center = fig.add_axes([0.35, 0.4, 0.3, 0.2])
    ax_center.axis('off')
    ax_center.add_patch(FancyBboxPatch((0.1, 0.2), 0.8, 0.6, boxstyle="round,pad=0.05",
                                        facecolor='gold', edgecolor='black', linewidth=2))
    ax_center.text(0.5, 0.5, 'ρ ~ M_P² H₀²\n\nFactor ~30 from\nobservation',
                   ha='center', va='center', fontsize=14, fontweight='bold')

    # Four derivations
    positions = [
        (0.05, 0.7, "1. DIMENSIONAL\nANALYSIS", '#e74c3c',
         "Only two scales:\n• M_P (Planck)\n• H₀ (Hubble)\n\nρ ~ M_P^a H₀^b\nwith a+b=4\n\n⟹ a=b=2"),

        (0.65, 0.7, "2. HOLOGRAPHIC\nPRINCIPLE", '#3498db',
         "S = A/(4ℓ_P²)\nN_DOF = S_H\nE_DOF = M_P/√N\n\nρ = E/V\n  = N·E_DOF/V\n  ~ M_P²H₀²"),

        (0.05, 0.05, "3. CAUSAL DIAMOND\n(Cohen-Kaplan-Nelson)", '#2ecc71',
         "IR/UV cutoff:\nL³ρ ≤ M_P²L\n\n⟹ ρ ≤ M_P²/L²\n    = M_P²H₀²"),

        (0.65, 0.05, "4. THERMODYNAMIC\n(de Sitter)", '#9b59b6',
         "de Sitter temp:\nT_dS = H₀/(2π)\n\nWith N ~ (M_P/H₀)²\nholographic DOF:\n\nρ ~ T⁴N\n  ~ M_P²H₀²")
    ]

    for x, y, title, color, text in positions:
        ax = fig.add_axes([x, y, 0.28, 0.22])
        ax.axis('off')
        ax.add_patch(FancyBboxPatch((0.02, 0.02), 0.96, 0.96, boxstyle="round,pad=0.02",
                                     facecolor='white', edgecolor=color, linewidth=3))
        ax.text(0.5, 0.85, title, ha='center', va='top', fontsize=11,
                fontweight='bold', color=color)
        ax.text(0.5, 0.7, text, ha='center', va='top', fontsize=9, fontfamily='monospace')

    # Arrows to center
    arrow_positions = [
        (0.19, 0.7, 0.35, 0.6),   # Top left to center
        (0.81, 0.7, 0.65, 0.6),   # Top right to center
        (0.19, 0.27, 0.35, 0.4),  # Bottom left to center
        (0.81, 0.27, 0.65, 0.4),  # Bottom right to center
    ]

    # Title
    fig.text(0.5, 0.95, 'FOUR INDEPENDENT DERIVATIONS OF ρ ~ M_P² H₀²',
             ha='center', fontsize=16, fontweight='bold')

    plt.savefig('plots/theorem_5_1_2_four_derivations.png', dpi=150, bbox_inches='tight')
    plt.close()
    print("  Saved: plots/theorem_5_1_2_four_derivations.png")


# ==============================================================================
# FIGURE 6: 3D VEV PROFILE
# ==============================================================================

def plot_3d_vev_profile():
    """Plot 3D visualization of VEV profile."""
    print("Generating: 3D VEV Profile...")

    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')

    # Color vertex positions
    color_vertices = np.array([
        [1, 0, 0],
        [-0.5, np.sqrt(3)/2, 0],
        [-0.5, -np.sqrt(3)/2, 0]
    ])
    color_vertices = color_vertices / np.linalg.norm(color_vertices[0])
    epsilon = 0.05

    # Create mesh in xy plane
    N = 80
    x = np.linspace(-1.2, 1.2, N)
    y = np.linspace(-1.2, 1.2, N)
    X, Y = np.meshgrid(x, y)

    # Compute v_χ on grid
    points = np.stack([X.ravel(), Y.ravel(), np.zeros_like(X.ravel())], axis=-1)
    v_sq = compute_vev_squared(points, color_vertices, epsilon)
    V = np.sqrt(np.maximum(v_sq, 0)).reshape(N, N)

    # Normalize for visualization
    V_norm = V / V.max()

    # Plot surface
    surf = ax.plot_surface(X, Y, V_norm, cmap='viridis', alpha=0.8,
                           linewidth=0, antialiased=True)

    # Mark color vertices
    colors = ['red', 'green', 'blue']
    for v, c in zip(color_vertices, colors):
        v_sq_pt = compute_vev_squared(v, color_vertices, epsilon)
        v_val = np.sqrt(max(0, v_sq_pt)) / V.max()
        ax.scatter([v[0]], [v[1]], [v_val], s=150, c=c, marker='o',
                   edgecolors='white', linewidths=2)

    # Mark center
    ax.scatter([0], [0], [0], s=300, c='gold', marker='*',
               edgecolors='black', linewidths=2, label='Center: v_χ = 0')

    ax.set_xlabel('X')
    ax.set_ylabel('Y')
    ax.set_zlabel('v_χ (normalized)')
    ax.set_title('Position-Dependent VEV: v_χ(x,y,0)\nVanishes at Center Due to Phase Cancellation',
                 fontsize=13, fontweight='bold')

    # Add colorbar
    fig.colorbar(surf, ax=ax, shrink=0.5, aspect=10, label='v_χ / v_max')

    plt.savefig('plots/theorem_5_1_2_3d_vev_profile.png', dpi=150, bbox_inches='tight')
    plt.close()
    print("  Saved: plots/theorem_5_1_2_3d_vev_profile.png")


# ==============================================================================
# MAIN
# ==============================================================================

def main():
    """Generate all visualization plots."""
    print("=" * 60)
    print("Theorem 5.1.2: Vacuum Energy Density — Visualization")
    print("=" * 60)
    print()

    plot_stella_octangula()
    plot_vacuum_energy_profile()
    plot_phase_cancellation()
    plot_scale_hierarchy()
    plot_four_derivations()
    plot_3d_vev_profile()

    print()
    print("=" * 60)
    print("All plots generated successfully!")
    print("Output directory: plots/")
    print("=" * 60)


if __name__ == "__main__":
    main()
