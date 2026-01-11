#!/usr/bin/env python3
"""
Unified Geometry Triple Build-Up: 3x3 Panel Figure

Shows parallel construction of three views:

ROW 1: Singlet Axis View (looking from W toward R-G-B plane)
  1a. T+ Energy Field (color sources)
  1b. Geometric Structure (T+ and T- triangles)
  1c. Complete with Observation Region

ROW 2: Diagonal Slice View (x=y plane cross-section)
  2a. Basic Energy Density
  2b. Add Vertices and Structure
  2c. Complete with Time Emergence

ROW 3: Quark Emergence View (z=0 slice)
  3a. Color Neutrality Field
  3b. Add Confinement Structure
  3c. Complete with Baryon/Mass

References:
- Theorem 0.2.2: Internal time emergence
- Theorem 0.2.3: Observation region
- Theorem 1.1.1-1.1.3: Color structure
- Theorem 4.1.1-4.1.2: Skyrmion/baryon mass
- Theorem 5.1.1: Energy density
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Circle
import matplotlib.patheffects as path_effects

# ============================================================================
# CONSTANTS AND SETUP (matching unified_geometry_fundamental_singlet.py)
# ============================================================================

ALPHA = 2 * np.pi / 3  # 120°

# Constants for energy density calculation
EPSILON = 0.5
A0 = 1.0
R_STELLA = 1.0
OMEGA_0 = 200.0
LAMBDA_CHI = 0.1
V0 = 1.0

# From Theorem 4.1.2 - Skyrme model parameters (QCD scale)
F_PI = 93  # MeV - pion decay constant
E_SKYRME = 5.45  # Dimensionless Skyrme parameter (Adkins et al. 1983)
M_NUCLEON = 6 * np.pi**2 * F_PI / E_SKYRME  # ≈ 940 MeV

# Stella octangula vertices - for DIAGONAL SLICE (theorem_5_1_1 coordinates)
STELLA_VERTICES = {
    'R': np.array([1, 1, 1]) / np.sqrt(3) * R_STELLA,
    'G': np.array([1, -1, -1]) / np.sqrt(3) * R_STELLA,
    'B': np.array([-1, 1, -1]) / np.sqrt(3) * R_STELLA,
    'W': np.array([-1, -1, 1]) / np.sqrt(3) * R_STELLA
}

PHASES = {
    'R': 0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3
}

def get_fundamental_tetrahedron():
    """
    Return vertices of fundamental tetrahedron T₊ for WEIGHT PLANE view.
    W (apex/singlet) at top, R, G, B in base plane.
    """
    scale = 1.0
    w_R = scale * np.array([1, 0, 0])
    w_G = scale * np.array([np.cos(2*np.pi/3), np.sin(2*np.pi/3), 0])
    w_B = scale * np.array([np.cos(4*np.pi/3), np.sin(4*np.pi/3), 0])
    h = scale * np.sqrt(2)
    w_W = np.array([0, 0, h])
    return w_R, w_G, w_B, w_W

def compute_energy_fundamental(x, y, vertices_2d, sigma=0.4):
    """Energy for weight plane view (Row 1)."""
    rho = 0
    for v in vertices_2d:
        r2 = (x - v[0])**2 + (y - v[1])**2
        amplitude = np.exp(-r2 / (2 * sigma**2))
        rho += amplitude**2
    return rho

# ============================================================================
# THEOREM 5.1.1 FIELD FUNCTIONS (for diagonal slice - Row 2)
# ============================================================================

def pressure_function(x, vertex):
    """Pressure function from theorem 5.1.1."""
    r_sq = np.sum((x - vertex)**2)
    return 1.0 / (r_sq + EPSILON**2)

def chi_total(x):
    """Total color field χ = χ_R + χ_G + χ_B."""
    result = 0j
    for c in ['R', 'G', 'B']:
        P_c = pressure_function(x, STELLA_VERTICES[c])
        a_c = A0 * P_c
        result += a_c * np.exp(1j * PHASES[c])
    return result

def v_chi(x):
    """VEV magnitude |χ|."""
    return np.abs(chi_total(x))

def mexican_hat_potential(x):
    """Mexican hat potential V(|χ|)."""
    v = v_chi(x)
    return LAMBDA_CHI * (v**2 - V0**2)**2

def gradient_chi_numerical(x, h=1e-6):
    """Numerical gradient of χ."""
    grad = np.zeros(3, dtype=complex)
    for i in range(3):
        x_plus = x.copy()
        x_minus = x.copy()
        x_plus[i] += h
        x_minus[i] -= h
        grad[i] = (chi_total(x_plus) - chi_total(x_minus)) / (2 * h)
    return grad

def grad_chi_squared(x):
    """|∇χ|²."""
    grad = gradient_chi_numerical(x)
    return np.sum(np.abs(grad)**2)

def energy_density_5_1_1(x, omega=OMEGA_0):
    """Energy density T₀₀ from theorem 5.1.1."""
    v = v_chi(x)
    grad_sq = grad_chi_squared(x)
    V = mexican_hat_potential(x)
    return omega**2 * v**2 + grad_sq + V

def color_neutrality_measure(x):
    """
    Measure of color neutrality: |χ_total|.

    From Theorem 1.1.3:
    - |χ_total| = 0 implies color singlet (confined)
    - |χ_total| > 0 implies color charge (unconfined)
    """
    return np.abs(chi_total(x))

def compute_color_neutrality_grid(n_points=150, extent=1.5):
    """Compute color neutrality on z=0 slice (for Row 3)."""
    p_range = np.linspace(-extent, extent, n_points)
    q_range = np.linspace(-extent, extent, n_points)

    color_neutral = np.zeros((n_points, n_points))
    for i, p in enumerate(p_range):
        for j, q in enumerate(q_range):
            x_3d = np.array([p, q, 0])
            color_neutral[j, i] = color_neutrality_measure(x_3d)

    return p_range, q_range, color_neutral

# ============================================================================
# SHARED SETUP
# ============================================================================

def setup_panel_weight(ax, title):
    """Setup for weight space panels (Row 1)."""
    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1.1)
    ax.set_aspect('equal')
    ax.set_facecolor('#1a1a2e')
    # Grid and axis lines removed for consistency with other rows
    # ax.grid(True, alpha=0.2, color='white', linestyle='-', linewidth=0.5)
    # ax.axhline(y=0, color='white', linewidth=0.8, alpha=0.4)
    # ax.axvline(x=0, color='white', linewidth=0.8, alpha=0.4)
    ax.set_title(title, fontsize=11, fontweight='bold', pad=8, color='black')
    ax.set_xlabel('x', fontsize=9)
    ax.set_ylabel('y', fontsize=9)

def setup_panel_slice(ax, title, extent=1.5):
    """Setup for diagonal slice panels (Row 2)."""
    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)
    ax.set_facecolor('#1a1a2e')
    ax.set_title(title, fontsize=11, fontweight='bold', pad=8, color='black')
    ax.set_xlabel('x / R_stella', fontsize=9)
    ax.set_ylabel('z / R_stella', fontsize=9)
    ax.set_aspect('equal')

def setup_panel_quark(ax, title, extent=1.5):
    """Setup for quark emergence panels (Row 3)."""
    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)
    ax.set_facecolor('black')
    ax.set_title(title, fontsize=11, fontweight='bold', pad=8, color='black')
    ax.set_xlabel('x / R_stella', fontsize=9)
    ax.set_ylabel('y / R_stella', fontsize=9)
    ax.set_aspect('equal')

def get_vertices_and_grids():
    w_R, w_G, w_B, w_W = get_fundamental_tetrahedron()
    v_R, v_G, v_B = w_R[:2], w_G[:2], w_B[:2]
    scale = 0.8
    v_R, v_G, v_B = scale * v_R, scale * v_G, scale * v_B
    vertices_scaled = [v_R, v_G, v_B]
    anti_vertices_scaled = [-v for v in vertices_scaled]

    x_grid = np.linspace(-1.2, 1.2, 200)
    y_grid = np.linspace(-1.2, 1.2, 200)
    X, Y = np.meshgrid(x_grid, y_grid)

    rho_energy_plus = np.zeros_like(X)
    rho_energy_minus = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy_plus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], vertices_scaled, sigma=0.4)
            rho_energy_minus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], anti_vertices_scaled, sigma=0.4)

    return vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale

def compute_diagonal_slice_energy(n_points=100, extent=1.5):
    """Compute energy density for diagonal slice."""
    x_range = np.linspace(-extent, extent, n_points)
    z_range = np.linspace(-extent, extent, n_points)

    rho_grid = np.zeros((n_points, n_points))
    for i, x_val in enumerate(x_range):
        for j, z_val in enumerate(z_range):
            pos = np.array([x_val, x_val, z_val])
            rho_grid[j, i] = energy_density_5_1_1(pos)

    return x_range, z_range, rho_grid

# ============================================================================
# ROW 1: SINGLET AXIS VIEW BUILD-UP
# ============================================================================

def row1_panel1_energy(ax):
    """Row 1, Panel 1: T+ Energy Field only."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()
    setup_panel_weight(ax, "1a. T+ Energy Field\n(Color Field Sources)")

    # Plot T+ energy only
    im = ax.contourf(X, Y, rho_energy_plus, levels=50, cmap='hot', alpha=0.85, zorder=0)
    # Contour lines removed for consistency with other rows
    # ax.contour(X, Y, rho_energy_plus, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # R, G, B vertex markers
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=350, zorder=25, edgecolor='white', linewidth=2.5)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=16, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='black')])

    # Explanation
    ax.annotate('R, G, B = color\nfield sources\n(Thm 1.1.1)',
                (0.0, -0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='orange', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='orange', linewidth=1))

def row1_panel2_geometry(ax):
    """Row 1, Panel 2: Geometric Structure (T+ and T- triangles)."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()
    setup_panel_weight(ax, "1b. Geometric Structure\n(T+ and T- Triangles)")

    # Combined energy
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    # Contour lines removed for consistency with other rows
    # ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # T+ triangle (solid cyan)
    fund_tri = Polygon(vertices_scaled, fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)

    # T- triangle (dashed gray)
    anti_triangle = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666',
                           linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_triangle)

    # T+ vertices
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=350, zorder=25, edgecolor='white', linewidth=2.5)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=16, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='black')])

    # T- vertices
    anti_colors = ['#AA2222', '#22AA22', '#2222AA']
    anti_labels = ['R̄', 'Ḡ', 'B̄']
    for v, c, l in zip(anti_vertices_scaled, anti_colors, anti_labels):
        ax.scatter(*v, c=c, s=250, zorder=24, edgecolor='white', linewidth=1.5, alpha=0.8)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=12, fontweight='bold',
                   color='#AAAAAA', ha='center', va='center', zorder=24,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Explanation
    ax.annotate('Stella octangula:\n2 interpenetrating\ntetrahedra (Thm 1.1.2)',
                (0.0, -0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='cyan', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='cyan', linewidth=1))

def row1_panel3_complete(ax):
    """Row 1, Panel 3: Complete with Observation Region."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()
    setup_panel_weight(ax, "1c. Complete View\n(Observation Region)")

    # Combined energy
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    # Contour lines removed for consistency with other rows
    # ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # Triangles
    fund_tri = Polygon(vertices_scaled, fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)
    anti_triangle = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666',
                           linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_triangle)

    # Observation region
    R_obs = EPSILON * 0.8
    obs_region = Circle((0, 0), R_obs, fill=True, facecolor='white',
                        edgecolor='cyan', linewidth=2.5, alpha=0.25, zorder=18)
    ax.add_patch(obs_region)
    obs_boundary = Circle((0, 0), R_obs, fill=False, edgecolor='cyan',
                         linewidth=2.5, alpha=0.9, zorder=19)
    ax.add_patch(obs_boundary)

    # Central marker
    ax.scatter(0, 0, s=150, c='white', marker='o', zorder=20,
              edgecolor='cyan', linewidth=2)
    ax.annotate('⊙', (0, 0), fontsize=14, ha='center', va='center',
               color='cyan', fontweight='bold', zorder=21)

    # Baryon region
    R_baryon = R_obs * 1.5
    baryon_ring = Circle((0, 0), R_baryon, fill=False, edgecolor='yellow',
                         linewidth=2, linestyle='--', alpha=0.8, zorder=17)
    ax.add_patch(baryon_ring)

    # Meson lines
    meson_colors = ['#FF6666', '#66FF66', '#6666FF']
    for v_q, v_anti, mc in zip(vertices_scaled, anti_vertices_scaled, meson_colors):
        ax.plot([v_q[0], v_anti[0]], [v_q[1], v_anti[1]],
               color=mc, linewidth=2.5, linestyle=':', alpha=0.7, zorder=12)

    # Gluon paths
    edge_colors = ['#FF00FF', '#00FFFF', '#FFFF00']
    for i in range(3):
        v1 = vertices_scaled[i]
        v2 = vertices_scaled[(i + 1) % 3]
        ax.plot([v1[0], v2[0]], [v1[1], v2[1]],
               color=edge_colors[i], linewidth=4, alpha=0.4, zorder=8,
               solid_capstyle='round')

    # Vertices
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=350, zorder=25, edgecolor='white', linewidth=2.5)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=16, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='black')])

    anti_colors = ['#AA2222', '#22AA22', '#2222AA']
    anti_labels = ['R̄', 'Ḡ', 'B̄']
    for v, c, l in zip(anti_vertices_scaled, anti_colors, anti_labels):
        ax.scatter(*v, c=c, s=250, zorder=24, edgecolor='white', linewidth=1.5, alpha=0.8)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=12, fontweight='bold',
                   color='#AAAAAA', ha='center', va='center', zorder=24,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Labels
    ax.annotate('Observation\nRegion\n(Thm 0.2.3)',
                (0.5, 0.5), fontsize=8, fontweight='bold',
                ha='center', va='center', color='cyan', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='cyan', linewidth=1))

    ax.annotate('Baryons\n(quarks)',
                (-0.75, -0.45), fontsize=7, fontweight='bold',
                ha='left', va='top', color='yellow', zorder=25,
                bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.85,
                         edgecolor='yellow', linewidth=1))

# ============================================================================
# ROW 2: DIAGONAL SLICE VIEW BUILD-UP
# ============================================================================

def row2_panel1_energy(ax):
    """Row 2, Panel 1: Basic Energy Density on diagonal slice."""
    setup_panel_slice(ax, "2a. Energy Density T₀₀\n(Diagonal Slice x=y)")

    n_points = 100
    extent = 1.5
    x_range, z_range, rho_grid = compute_diagonal_slice_energy(n_points, extent)

    rho_log = np.log10(rho_grid + 1)
    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='hot')

    # Simple annotation
    ax.annotate('Energy density\nT₀₀ = κχ²\n(Thm 5.1.1)',
                (-1.3, -1.2), fontsize=8, fontweight='bold',
                ha='left', va='top', color='white', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85))

def row2_panel2_vertices(ax):
    """Row 2, Panel 2: Add vertices and structure."""
    setup_panel_slice(ax, "2b. Add Vertex Structure\n(R, G, B, W positions)")

    n_points = 100
    extent = 1.5
    x_range, z_range, rho_grid = compute_diagonal_slice_energy(n_points, extent)

    rho_log = np.log10(rho_grid + 1)
    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='hot')

    # Mark vertices
    for name, vertex in STELLA_VERTICES.items():
        on_diagonal = abs(vertex[0] - vertex[1]) < 0.01

        if on_diagonal:
            ax.plot(vertex[0], vertex[2], 'wo', markersize=14,
                   markeredgecolor='black', markeredgewidth=2, zorder=10)
        else:
            ax.plot(vertex[0], vertex[2], 'o', markersize=12, markerfacecolor='none',
                   markeredgecolor='white', markeredgewidth=2.5, zorder=10)

        if name == 'R':
            color = '#FF6666'
        elif name == 'G':
            color = '#66FF66'
        elif name == 'B':
            color = '#6666FF'
        else:
            color = 'gold'

        ax.annotate(name, (vertex[0] + 0.12, vertex[2] + 0.12), fontsize=14, color=color,
                   fontweight='bold', zorder=11,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Mark center
    ax.scatter(0, 0, c='white', s=150, marker='*', edgecolors='black',
              linewidths=1.5, zorder=12)

    # Dark band annotation
    ax.annotate('Dark band:\nχ = 0\n(color neutral)',
                (0.03, 1.35), fontsize=8, fontweight='bold',
                ha='left', va='top', color='cyan', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='cyan'))

def row2_panel3_complete(ax):
    """Row 2, Panel 3: Complete with time emergence."""
    setup_panel_slice(ax, "2c. Complete View\n(Time Emergence λ)")

    n_points = 100
    extent = 1.5
    x_range, z_range, rho_grid = compute_diagonal_slice_energy(n_points, extent)

    rho_log = np.log10(rho_grid + 1)
    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='hot')

    # Singlet axis (from center to W)
    W = STELLA_VERTICES['W']
    ax.plot([0, W[0]], [0, W[2]], color='gold', linewidth=3, linestyle='-',
           alpha=0.9, zorder=8, label='Singlet axis')
    ax.annotate('', xy=(W[0]*0.7, W[2]*0.7), xytext=(0, 0),
               arrowprops=dict(arrowstyle='->', color='gold', lw=2.5),
               zorder=9)

    # Mark vertices
    for name, vertex in STELLA_VERTICES.items():
        on_diagonal = abs(vertex[0] - vertex[1]) < 0.01

        if on_diagonal:
            ax.plot(vertex[0], vertex[2], 'wo', markersize=14,
                   markeredgecolor='black', markeredgewidth=2, zorder=10)
        else:
            ax.plot(vertex[0], vertex[2], 'o', markersize=12, markerfacecolor='none',
                   markeredgecolor='white', markeredgewidth=2.5, zorder=10)

        if name == 'R':
            color = '#FF6666'
        elif name == 'G':
            color = '#66FF66'
        elif name == 'B':
            color = '#6666FF'
        else:
            color = 'gold'

        ax.annotate(name, (vertex[0] + 0.12, vertex[2] + 0.12), fontsize=14, color=color,
                   fontweight='bold', zorder=11,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Mark center
    ax.scatter(0, 0, c='white', s=150, marker='*', edgecolors='black',
              linewidths=1.5, zorder=12)

    # Dark band annotation
    ax.annotate('Dark band: χ = 0\n(Thm 0.2.3)',
                xy=(0.03, 0.97), xycoords='axes fraction',
                fontsize=8, fontweight='bold', ha='left', va='top', color='cyan',
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='cyan'))

    # Singlet axis annotation
    ax.annotate('λ →\n(time)\n(Thm 0.2.2)',
                xy=(W[0]*0.5 + 0.15, W[2]*0.5), fontsize=9, color='gold',
                fontweight='bold', ha='left', va='center',
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='gold'),
                path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Energy density annotation
    ax.annotate('T₀₀ from\nThm 5.1.1',
                xy=(0.97, 0.03), xycoords='axes fraction',
                fontsize=8, fontweight='bold', ha='right', va='bottom', color='white',
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85))

# ============================================================================
# ROW 3: QUARK EMERGENCE VIEW BUILD-UP
# ============================================================================

def row3_panel1_neutrality(ax):
    """Row 3, Panel 1: Color Neutrality Field."""
    setup_panel_quark(ax, "3a. Color Neutrality Field\n(z=0 slice)")

    n_points = 150
    extent = 1.5
    p_range, q_range, color_neutral = compute_color_neutrality_grid(n_points, extent)

    # Dark regions = color neutral (|χ| ≈ 0) = confinement
    im = ax.imshow(1 / (color_neutral + 0.1), extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='inferno', alpha=0.85)

    # Annotation
    ax.annotate('Dark = |χ| ≈ 0\n(color neutral)\n(Thm 0.2.3)',
                xy=(0.03, 0.03), xycoords='axes fraction',
                fontsize=8, fontweight='bold', ha='left', va='bottom', color='yellow',
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='yellow'))

def row3_panel2_confinement(ax):
    """Row 3, Panel 2: Add Confinement Structure."""
    setup_panel_quark(ax, "3b. Add Confinement Structure\n(Bag boundary, R/G/B)")

    n_points = 150
    extent = 1.5
    p_range, q_range, color_neutral = compute_color_neutrality_grid(n_points, extent)

    im = ax.imshow(1 / (color_neutral + 0.1), extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='inferno', alpha=0.85)

    # Pressure contours around each vertex
    for c, color in [('R', '#FF4444'), ('G', '#44FF44'), ('B', '#4444FF')]:
        vertex = STELLA_VERTICES[c]
        for r in [0.2, 0.4, 0.6, 0.8]:
            circle = Circle((vertex[0], vertex[1]), r, fill=False,
                           color=color, alpha=0.25, linewidth=1.5, linestyle='--')
            ax.add_patch(circle)

    # Vertex markers (R, G, B quarks)
    for name, color in [('R', '#FF0000'), ('G', '#00FF00'), ('B', '#0000FF')]:
        v = STELLA_VERTICES[name]
        ax.plot(v[0], v[1], 'o', markersize=20, color=color,
               markeredgecolor='white', markeredgewidth=2.5, zorder=20)
        ax.annotate(name, (v[0], v[1]), fontsize=14, fontweight='bold',
                   ha='center', va='center', color='white', zorder=21)

    # W vertex (singlet - into the page)
    ax.plot(0, 0, 'o', markersize=10, color='gold',
           markeredgecolor='black', markeredgewidth=2, zorder=20)
    ax.annotate('⊙', (0, 0), fontsize=12, ha='center', va='center',
               color='black', zorder=21)

    # Confinement boundary (bag)
    R_bag = 1.2
    bag_circle = Circle((0, 0), R_bag, fill=False, color='cyan',
                        linewidth=3, linestyle='-', zorder=15)
    ax.add_patch(bag_circle)

    # Annotations
    ax.annotate('Bag boundary\n(Thm 1.1.3)',
               xy=(0.97, 0.97), xycoords='axes fraction',
               fontsize=8, color='cyan', fontweight='bold',
               ha='right', va='top',
               bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                        edgecolor='cyan'))

def row3_panel3_complete(ax):
    """Row 3, Panel 3: Complete with Baryon/Mass."""
    setup_panel_quark(ax, "3c. Quark Emergence\n(Theorems 1.1.1, 4.1.1, 4.1.2)")

    n_points = 150
    extent = 1.5
    p_range, q_range, color_neutral = compute_color_neutrality_grid(n_points, extent)

    im = ax.imshow(1 / (color_neutral + 0.1), extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='inferno', alpha=0.85)

    # Pressure contours around each vertex
    for c, color in [('R', '#FF4444'), ('G', '#44FF44'), ('B', '#4444FF')]:
        vertex = STELLA_VERTICES[c]
        for r in [0.2, 0.4, 0.6, 0.8]:
            circle = Circle((vertex[0], vertex[1]), r, fill=False,
                           color=color, alpha=0.25, linewidth=1.5, linestyle='--')
            ax.add_patch(circle)

    # Vertex markers (R, G, B quarks)
    for name, color in [('R', '#FF0000'), ('G', '#00FF00'), ('B', '#0000FF')]:
        v = STELLA_VERTICES[name]
        ax.plot(v[0], v[1], 'o', markersize=20, color=color,
               markeredgecolor='white', markeredgewidth=2.5, zorder=20)
        ax.annotate(name, (v[0], v[1]), fontsize=14, fontweight='bold',
                   ha='center', va='center', color='white', zorder=21)

    # W vertex (singlet - into the page)
    ax.plot(0, 0, 'o', markersize=10, color='gold',
           markeredgecolor='black', markeredgewidth=2, zorder=20)
    ax.annotate('⊙', (0, 0), fontsize=12, ha='center', va='center',
               color='black', zorder=21)

    # Confinement boundary (bag)
    R_bag = 1.2
    bag_circle = Circle((0, 0), R_bag, fill=False, color='cyan',
                        linewidth=3, linestyle='-', zorder=15)
    ax.add_patch(bag_circle)

    # Arrows showing phase gradient flow (toward center)
    for name in ['R', 'G', 'B']:
        v = STELLA_VERTICES[name]
        start = v[:2] * 0.65
        end = v[:2] * 0.25
        ax.annotate('', xy=end, xytext=start,
                   arrowprops=dict(arrowstyle='->', color='white', lw=2.5, alpha=0.8),
                   zorder=18)

    # Baryon triangle (RGB = color singlet)
    triangle_verts = [STELLA_VERTICES['R'][:2],
                     STELLA_VERTICES['G'][:2],
                     STELLA_VERTICES['B'][:2]]
    triangle = Polygon(triangle_verts, fill=False, edgecolor='white',
                      linewidth=2, linestyle='-', alpha=0.7, zorder=10)
    ax.add_patch(triangle)

    # Annotations with theorem references
    textbox_props = dict(boxstyle='round,pad=0.2', facecolor='black',
                        alpha=0.85, edgecolor='white')

    # Confinement annotation
    ax.annotate('Bag boundary\n(Thm 1.1.3)',
               xy=(0.97, 0.97), xycoords='axes fraction',
               fontsize=8, color='cyan', fontweight='bold',
               ha='right', va='top',
               bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                        edgecolor='cyan'))

    # Mass annotation
    ax.annotate(f'Nucleon: {M_NUCLEON:.0f} MeV\n(Thm 4.1.2)',
               xy=(0.03, 0.97), xycoords='axes fraction',
               fontsize=8, color='white', fontweight='bold',
               ha='left', va='top', bbox=textbox_props)

    # Color neutrality annotation
    ax.annotate('χ_R + χ_G + χ_B = 0\n(Thm 0.2.3)',
               xy=(0.03, 0.03), xycoords='axes fraction',
               fontsize=8, color='yellow', fontweight='bold',
               ha='left', va='bottom',
               bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                        edgecolor='yellow'))

# ============================================================================
# MAIN
# ============================================================================

def main():
    print("Generating triple build-up figure (3x3 panels)...")

    fig, axes = plt.subplots(3, 3, figsize=(18, 18))
    fig.suptitle('Building Three Views: Singlet Axis, Diagonal Slice & Quark Emergence',
                 fontsize=16, fontweight='bold', y=0.98)

    # Row 1: Singlet Axis View
    row1_panel1_energy(axes[0, 0])
    row1_panel2_geometry(axes[0, 1])
    row1_panel3_complete(axes[0, 2])

    # Row 2: Diagonal Slice View
    row2_panel1_energy(axes[1, 0])
    row2_panel2_vertices(axes[1, 1])
    row2_panel3_complete(axes[1, 2])

    # Row 3: Quark Emergence View
    row3_panel1_neutrality(axes[2, 0])
    row3_panel2_confinement(axes[2, 1])
    row3_panel3_complete(axes[2, 2])

    # Row labels
    fig.text(0.02, 0.82, 'Row 1:\nSinglet Axis\nView\n(from W)',
             fontsize=10, fontweight='bold', va='center', color='gray', style='italic')
    fig.text(0.02, 0.50, 'Row 2:\nDiagonal\nSlice\n(x=y plane)',
             fontsize=10, fontweight='bold', va='center', color='gray', style='italic')
    fig.text(0.02, 0.18, 'Row 3:\nQuark\nEmergence\n(z=0 slice)',
             fontsize=10, fontweight='bold', va='center', color='gray', style='italic')

    # Column labels
    fig.text(0.22, 0.02, 'Energy/Neutrality Fields', fontsize=11, fontweight='bold', ha='center', color='orange')
    fig.text(0.52, 0.02, 'Add Structure', fontsize=11, fontweight='bold', ha='center', color='cyan')
    fig.text(0.82, 0.02, 'Complete Picture', fontsize=11, fontweight='bold', ha='center', color='gold')

    plt.tight_layout(rect=[0.05, 0.04, 1, 0.96])

    output_path = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/unified_geometry_triple_buildup.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()

    print(f"  Saved: {output_path}")
    print("\nFigure structure:")
    print("  Row 1 - Singlet Axis View (looking from W toward R-G-B plane):")
    print("    1a. T+ Energy Field (color sources)")
    print("    1b. Geometric Structure (T+ and T- triangles)")
    print("    1c. Complete View (observation region, mesons, gluons)")
    print("  Row 2 - Diagonal Slice (x=y plane cross-section):")
    print("    2a. Energy Density T₀₀ (Theorem 5.1.1)")
    print("    2b. Add Vertex Structure (R, G, B, W positions)")
    print("    2c. Complete View (time emergence λ)")
    print("  Row 3 - Quark Emergence (z=0 slice):")
    print("    3a. Color Neutrality Field (|χ|)")
    print("    3b. Add Confinement Structure (bag boundary, R/G/B)")
    print("    3c. Complete View (baryon triangle, nucleon mass)")

if __name__ == "__main__":
    main()
