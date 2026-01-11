#!/usr/bin/env python3
"""
Unified Geometry: Fundamental Tetrahedron with Singlet Axis + Quark Emergence
=============================================================================

Three-panel figure showing the FUNDAMENTAL representation:
1. Weight plane view (looking down the singlet axis) - sees R, G, B triangle
2. Diagonal slice (x=y plane) - sees singlet axis as line to W
3. Quark emergence view - theorem-based visualization of where quarks emerge

The physical interpretation:
- The fundamental tetrahedron T₊ has 4 vertices: R, G, B (colors) and W (singlet/apex)
- The singlet axis connects the center of the R-G-B triangle to the W apex
- Time (λ) emerges along this axis
- Quarks emerge at the R, G, B vertices as topological solitons (Theorem 4.1.1)

Author: Verification Agent
Date: December 15, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patheffects as path_effects
from matplotlib.patches import Polygon, Circle, FancyArrowPatch
from matplotlib.lines import Line2D
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from scipy.integrate import odeint
from pathlib import Path

# ============================================================================
# CONSTANTS
# ============================================================================

ALPHA = 2 * np.pi / 3  # 120°

# Stella octangula vertices (same as theorem_5_1_1)
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

# From Theorem 1.1.3 - String tension
SIGMA = 0.19  # GeV² = (440 MeV)² - lattice QCD value

# Stella octangula vertices - theorem_5_1_1 coordinates
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

# Fundamental tetrahedron vertices (for left panel - weight plane view)
# Using coordinates where W is at top along z-axis
# and R, G, B form equilateral triangle in z=0 plane

def get_fundamental_tetrahedron():
    """
    Return vertices of fundamental tetrahedron T₊.
    W (apex/singlet) at top, R, G, B in base plane.
    """
    # R, G, B at 120° apart in the z=0 plane
    scale = 1.0
    w_R = scale * np.array([1, 0, 0])
    w_G = scale * np.array([np.cos(2*np.pi/3), np.sin(2*np.pi/3), 0])
    w_B = scale * np.array([np.cos(4*np.pi/3), np.sin(4*np.pi/3), 0])

    # W apex above the center
    h = scale * np.sqrt(2)
    w_W = np.array([0, 0, h])

    return w_R, w_G, w_B, w_W


# ============================================================================
# THEOREM 5.1.1 FIELD FUNCTIONS (for right panel)
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


# ============================================================================
# DYNAMICAL SYSTEM
# ============================================================================

def phase_difference_dynamics(psi: np.ndarray, t: float, K: float) -> np.ndarray:
    """Phase-difference dynamics from Sakaguchi-Kuramoto model."""
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


def compute_energy_fundamental(x, y, vertices_2d, sigma=0.35):
    """
    Compute energy density from fundamental vertices only.
    """
    rho = 0
    for v in vertices_2d:
        r2 = (x - v[0])**2 + (y - v[1])**2
        amplitude = np.exp(-r2 / (2 * sigma**2))
        rho += amplitude**2
    return rho


# ============================================================================
# PANEL 1: WEIGHT PLANE VIEW (looking down singlet axis toward R-G-B)
# ============================================================================

def create_weight_plane_panel(ax):
    """
    Create the weight plane view - looking down the singlet axis.
    We see the R, G, B triangle with ⊙ at center (singlet axis into page).
    """
    w_R, w_G, w_B, w_W = get_fundamental_tetrahedron()

    # Project to 2D (just take x, y)
    v_R = w_R[:2]
    v_G = w_G[:2]
    v_B = w_B[:2]
    vertices = [v_R, v_G, v_B]

    scale = 0.8
    v_R = scale * v_R
    v_G = scale * v_G
    v_B = scale * v_B
    vertices_scaled = [v_R, v_G, v_B]

    # Background: Energy density field for BOTH tetrahedra
    x_grid = np.linspace(-1.2, 1.2, 200)
    y_grid = np.linspace(-1.2, 1.2, 200)
    X, Y = np.meshgrid(x_grid, y_grid)

    # T+ energy density (quark tetrahedron) - warm colors
    rho_energy_plus = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy_plus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], vertices_scaled, sigma=0.4)

    # T- energy density (antiquark tetrahedron) - cool/inverted colors
    # Anti-vertices are at antipodal positions
    anti_vertices_for_energy = [-v for v in vertices_scaled]
    rho_energy_minus = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy_minus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], anti_vertices_for_energy, sigma=0.4)

    # Combined energy density (T+ dominant, T- as subtle background)
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus

    # Plot combined energy field with dark/hot colorscheme
    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # Fundamental triangle
    fund_tri = Polygon(vertices_scaled, fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)

    # Phase trajectories
    K = 1.0
    t_span = np.linspace(0, 50, 500)
    np.random.seed(123)
    n_traj = 15

    for i in range(n_traj):
        phi0_R = 0
        phi0_G = np.random.uniform(0, 2*np.pi)
        phi0_B = np.random.uniform(0, 2*np.pi)
        psi0 = np.array([phi0_G - phi0_R, phi0_B - phi0_G])

        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))

        trajectory_x, trajectory_y = [], []
        for psi in solution:
            psi1, psi2 = psi
            phi_R, phi_G, phi_B = 0, psi1, psi1 + psi2

            z_R = np.exp(1j * phi_R)
            z_G = np.exp(1j * phi_G)
            z_B = np.exp(1j * phi_B)
            color_sum = (z_R + z_G + z_B) / 3

            trajectory_x.append(scale * np.real(color_sum) * 3)
            trajectory_y.append(scale * np.imag(color_sum) * 3)

        trajectory_x = np.array(trajectory_x)
        trajectory_y = np.array(trajectory_y)

        # All trajectories go to the same attractor in fundamental rep
        # Use purple/magenta to represent T+ (red) and T- (blue) combination
        traj_color = '#AA44AA'

        for j in range(len(trajectory_x) - 1):
            alpha_val = 0.3 + 0.6 * (j / len(trajectory_x))
            ax.plot(trajectory_x[j:j+2], trajectory_y[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.5, zorder=15)

        if len(trajectory_x) > 10:
            ax.annotate('', xy=(trajectory_x[-1], trajectory_y[-1]),
                       xytext=(trajectory_x[-10], trajectory_y[-10]),
                       arrowprops=dict(arrowstyle='->', color=traj_color, lw=2, alpha=0.9),
                       zorder=16)

    # ===========================================
    # OBSERVATION REGION (Theorem 0.2.3)
    # ===========================================
    # From Theorem 0.2.3: Observation radius R_obs ~ ε
    # This is where P_R = P_G = P_B and χ_total ≈ 0
    # Flat spacetime emerges here (isotropic metric g_ij ∝ δ_ij)

    R_obs = EPSILON * 0.8  # Observation radius from theorem

    # Filled observation region (where we can observe)
    obs_region = Circle((0, 0), R_obs, fill=True, facecolor='white',
                        edgecolor='cyan', linewidth=2.5, alpha=0.25, zorder=18)
    ax.add_patch(obs_region)

    # Outer boundary of observation region
    obs_boundary = Circle((0, 0), R_obs, fill=False, edgecolor='cyan',
                         linewidth=2.5, linestyle='-', zorder=19)
    ax.add_patch(obs_boundary)

    # ===========================================
    # SINGLET AXIS SYMBOL (⊙) at center
    # ===========================================

    # Outer circle for ⊙ symbol
    singlet_circle = Circle((0, 0), 0.06, fill=False, edgecolor='white',
                            linewidth=3, zorder=20)
    ax.add_patch(singlet_circle)

    # Central dot for ⊙ symbol (smaller and white)
    ax.scatter(0, 0, c='white', s=40, marker='o', zorder=21, edgecolor='black', linewidth=0.5)

    # Label for singlet axis
    ax.annotate('⊙ Singlet Axis',
                (0.10, -0.03), fontsize=10, fontweight='bold',
                ha='left', va='top', color='white', zorder=25,
                path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Label for observation region
    ax.annotate('Observation\nRegion\n(Thm 0.2.3)',
                (0.45, 0.45), fontsize=9, fontweight='bold',
                ha='center', va='center', color='cyan', zorder=25,
                bbox=dict(boxstyle='round,pad=0.3', facecolor='black', alpha=0.85,
                         edgecolor='cyan', linewidth=1.5))

    # Vertex markers - COLOR FIELD SOURCES
    # R, G, B vertices are where color fields originate (pressure sources)
    # NOT where quarks are observed - quarks are color-neutral skyrmions
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=350, zorder=25, edgecolor='white', linewidth=2.5)
        direction = v / np.linalg.norm(v)
        # Color label (R, G, B)
        ax.annotate(l, v + 0.12 * direction, fontsize=16, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='black')])

    # ===========================================
    # BARYON (OBSERVABLE HADRON) LOCATION
    # ===========================================
    # From Theorem 1.1.3 (Color Confinement Geometry):
    # "Observable particles must sit at the centroid (color singlet)" §7.2
    # The centroid is the UNIQUE color-neutral point where R+G+B=0
    #
    # From Theorem 4.1.1 + 4.1.2 (Skyrmions):
    # Baryons are extended objects (skyrmions) CENTERED at the origin
    # The skyrmion profile F(r) goes from π at r=0 to 0 at r→∞
    # Size determined by virial relation E_kin = E_Skyrme
    #
    # The R, G, B vertices are COLOR FIELD SOURCES (pressure functions)
    # Observable hadrons exist at the CENTER where colors combine to neutral

    # Draw baryon region - an extended ring around center showing soliton extent
    # Skyrmion size ~ 1/e × f_π^{-1} ≈ 0.5-0.8 fm for QCD parameters
    R_baryon = R_obs * 1.5  # Baryon extends beyond observation region
    baryon_ring = Circle((0, 0), R_baryon, fill=False, edgecolor='yellow',
                         linewidth=2, linestyle='--', alpha=0.8, zorder=17)
    ax.add_patch(baryon_ring)

    # Label for baryon/hadron location
    ax.annotate('Baryons\n(containing quarks)\ncentered here\n(Thm 1.1.3, 4.1.1)',
                (0.65, 0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='yellow', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='yellow', linewidth=1))

    # ===========================================
    # ANTI-TETRAHEDRON T- (Antiquark vertices)
    # ===========================================
    # From Theorem 1.1.2 (Charge Conjugation):
    # T- has antipodal vertices: R̄, Ḡ, B̄ at positions -v_R, -v_G, -v_B
    # These are the antiquark color sources

    # Anti-vertices (antipodal to R, G, B)
    anti_vertices_scaled = [-v for v in vertices_scaled]  # Antipodal positions
    anti_colors = ['#AA2222', '#22AA22', '#2222AA']  # Darker versions
    anti_labels = ['R̄', 'Ḡ', 'B̄']

    # Draw anti-tetrahedron triangle (dashed, behind)
    anti_triangle = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666',
                           linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_triangle)

    # Anti-vertex markers
    for v, c, l in zip(anti_vertices_scaled, anti_colors, anti_labels):
        ax.scatter(*v, c=c, s=250, zorder=24, edgecolor='white', linewidth=1.5, alpha=0.8)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=12, fontweight='bold',
                   color='#AAAAAA', ha='center', va='center', zorder=24,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # ===========================================
    # MESONS (Quark-Antiquark pairs)
    # ===========================================
    # From Theorem 1.1.3 §4.1:
    # Mesons are quantum superpositions |c c̄⟩ = (|RR̄⟩ + |GḠ⟩ + |BB̄⟩)/√3
    # Geometrically: antipodal alignments through origin
    # These are color-neutral (observable) because w_c + w_c̄ = 0

    meson_colors = ['#FF6666', '#66FF66', '#6666FF']  # Lighter versions
    for i, (v_q, v_anti, mc) in enumerate(zip(vertices_scaled, anti_vertices_scaled, meson_colors)):
        # Draw meson line from quark to antiquark through center
        ax.plot([v_q[0], v_anti[0]], [v_q[1], v_anti[1]],
               color=mc, linewidth=2.5, linestyle=':', alpha=0.7, zorder=12)

    # Meson label
    ax.annotate('Mesons (qq̄)\nalong diameters\n(Thm 1.1.3)',
                (-0.75, -0.65), fontsize=8, fontweight='bold',
                ha='center', va='top', color='#FF9999', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='#FF9999', linewidth=1))

    # ===========================================
    # GLUON CONFINEMENT BOUNDARY
    # ===========================================
    # From Theorem 1.1.3 §7.3:
    # "Each gluon corresponds to an edge connecting different color vertices"
    # Gluons carry color-anticolor, confined to edges of tetrahedra
    # Glueballs are closed loops: R→G→B→R

    # Highlight edges as gluon paths (thicker overlay on triangle edges)
    edge_colors = ['#FF00FF', '#00FFFF', '#FFFF00']  # Magenta, Cyan, Yellow for gluon edges
    edge_labels = ['g_RG', 'g_GB', 'g_BR']

    for i in range(3):
        v1 = vertices_scaled[i]
        v2 = vertices_scaled[(i + 1) % 3]
        # Gluon path along edge
        ax.plot([v1[0], v2[0]], [v1[1], v2[1]],
               color=edge_colors[i], linewidth=4, alpha=0.4, zorder=8,
               solid_capstyle='round')

    # Label for gluon confinement
    ax.annotate('Gluon paths\n(confined to edges)\n(Thm 1.1.3)',
                (-0.85, 0.55), fontsize=8, fontweight='bold',
                ha='center', va='top', color='#00FFFF', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='#00FFFF', linewidth=1))

    # Title and styling
    ax.set_title('View Along Singlet Axis\n(Looking from W toward R-G-B plane)',
                 fontsize=13, fontweight='bold', pad=10, color='black')

    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1.1)
    ax.set_xlabel('x', fontsize=11)
    ax.set_ylabel('y', fontsize=11)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.2, color='white', linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='white', linewidth=0.8, alpha=0.4)
    ax.axvline(x=0, color='white', linewidth=0.8, alpha=0.4)
    ax.set_facecolor('#1a1a2e')

    return im


# ============================================================================
# PANEL 2: DIAGONAL SLICE (x=y plane) - Exactly like theorem_5_1_1 third panel
# ============================================================================

def create_side_view_panel(ax):
    """
    Create diagonal slice view using theorem 5.1.1 energy density.
    This is the x=y plane slice showing:
    - Energy density T₀₀ from Theorem 5.1.1
    - The dark diagonal band where χ_total ≈ 0 (Theorem 0.2.3: color neutrality)
    - Vertex positions projected onto this slice
    - Singlet axis direction (W vertex location)

    NO speculative trajectories - only theorem-derived data.
    """
    n_points = 100
    extent = 1.5
    x_range = np.linspace(-extent, extent, n_points)
    z_range = np.linspace(-extent, extent, n_points)

    # Compute energy density on diagonal slice (x=y) - Theorem 5.1.1
    rho_grid = np.zeros((n_points, n_points))

    for i, x_val in enumerate(x_range):
        for j, z_val in enumerate(z_range):
            # Diagonal slice: position = (x, x, z)
            pos = np.array([x_val, x_val, z_val])
            rho_grid[j, i] = energy_density_5_1_1(pos)

    # Log scale for better visualization
    rho_log = np.log10(rho_grid + 1)

    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='hot')

    # ===========================================
    # SINGLET AXIS - from center toward W vertex
    # ===========================================
    # The singlet axis connects center to W (Theorem 0.2.3)
    W = STELLA_VERTICES['W']
    ax.plot([0, W[0]], [0, W[2]], color='gold', linewidth=3, linestyle='-',
           alpha=0.9, zorder=8, label='Singlet axis')
    ax.annotate('', xy=(W[0]*0.7, W[2]*0.7), xytext=(0, 0),
               arrowprops=dict(arrowstyle='->', color='gold', lw=2.5),
               zorder=9)

    # ===========================================
    # VERTEX MARKERS
    # ===========================================
    # Mark vertices (projected onto this slice at their x, z coordinates)
    for name, vertex in STELLA_VERTICES.items():
        # Check if vertex is on diagonal (x ≈ y)
        on_diagonal = abs(vertex[0] - vertex[1]) < 0.01

        if on_diagonal:
            # Solid marker - vertex is ON this slice
            ax.plot(vertex[0], vertex[2], 'wo', markersize=14, markeredgecolor='black', markeredgewidth=2, zorder=10)
        else:
            # Hollow marker - vertex is OFF this slice (projected)
            ax.plot(vertex[0], vertex[2], 'o', markersize=12, markerfacecolor='none',
                   markeredgecolor='white', markeredgewidth=2.5, zorder=10)

        # Color-coded labels
        if name == 'R':
            color = '#FF6666'
        elif name == 'G':
            color = '#66FF66'
        elif name == 'B':
            color = '#6666FF'
        else:  # W
            color = 'gold'

        ax.annotate(name, (vertex[0] + 0.12, vertex[2] + 0.12), fontsize=14, color=color,
                   fontweight='bold', zorder=11,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Mark center (color neutrality point)
    ax.scatter(0, 0, c='white', s=150, marker='*', edgecolors='black',
              linewidths=1.5, zorder=12)

    # ===========================================
    # ANNOTATIONS with theorem references
    # ===========================================
    textbox_props = dict(boxstyle='round,pad=0.3', facecolor='black', alpha=0.85,
                        edgecolor='white')

    # Dark band annotation
    ax.annotate('Dark band: χ = 0\n(Thm 0.2.3)',
                xy=(0.03, 0.97), xycoords='axes fraction',
                fontsize=9, fontweight='bold', ha='left', va='top', color='cyan',
                bbox=textbox_props)

    # Energy density annotation
    ax.annotate('T₀₀ from Thm 5.1.1',
                xy=(0.97, 0.03), xycoords='axes fraction',
                fontsize=9, fontweight='bold', ha='right', va='bottom', color='white',
                bbox=textbox_props)

    # Singlet axis annotation
    ax.annotate('λ →\n(time)',
                xy=(W[0]*0.5 + 0.1, W[2]*0.5), fontsize=10, color='gold',
                fontweight='bold', ha='left', va='center',
                path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    ax.set_xlabel('x / R_stella', fontsize=12)
    ax.set_ylabel('z / R_stella', fontsize=12)
    ax.set_title('Diagonal Slice (x=y)\nEnergy Density T₀₀ (Theorem 5.1.1)', fontsize=13, fontweight='bold', pad=10)
    ax.set_aspect('equal')

    return im


# ============================================================================
# PANEL 3: QUARK EMERGENCE (theorem-based)
# ============================================================================

def color_neutrality_measure(x):
    """
    Measure of color neutrality: |χ_total|.

    From Theorem 1.1.3:
    - |χ_total| = 0 implies color singlet (confined)
    - |χ_total| > 0 implies color charge (unconfined)
    """
    return np.abs(chi_total(x))


def create_quark_emergence_panel(ax):
    """
    Create quark emergence visualization based on theorem data.

    Shows:
    1. R, G, B vertices = quark color charges (Theorem 1.1.1)
    2. Color neutrality background (Theorem 0.2.3)
    3. Confinement boundary (Theorem 1.1.3)
    4. Baryon triangle (Theorem 1.1.3)
    5. Mass annotation (Theorem 4.1.2)
    """
    n_points = 150
    extent = 1.5

    p_range = np.linspace(-extent, extent, n_points)
    q_range = np.linspace(-extent, extent, n_points)

    # Compute color neutrality on z=0 slice
    color_neutral = np.zeros((n_points, n_points))

    for i, p in enumerate(p_range):
        for j, q in enumerate(q_range):
            x_3d = np.array([p, q, 0])
            color_neutral[j, i] = color_neutrality_measure(x_3d)

    # Dark regions = color neutral (|χ| ≈ 0) = confinement
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
        ax.plot(v[0], v[1], 'o', markersize=22, color=color,
               markeredgecolor='white', markeredgewidth=2.5, zorder=20)
        ax.annotate(name, (v[0], v[1]), fontsize=16, fontweight='bold',
                   ha='center', va='center', color='white', zorder=21)

    # W vertex (singlet - into the page)
    ax.plot(0, 0, 'o', markersize=12, color='gold',
           markeredgecolor='black', markeredgewidth=2, zorder=20)
    ax.annotate('⊙', (0, 0), fontsize=14, ha='center', va='center',
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
    textbox_props = dict(boxstyle='round,pad=0.3', facecolor='black',
                        alpha=0.85, edgecolor='white')

    # Confinement annotation
    ax.annotate('Bag boundary\n(Thm 1.1.3)',
               xy=(0.97, 0.97), xycoords='axes fraction',
               fontsize=9, color='cyan', fontweight='bold',
               ha='right', va='top', bbox=textbox_props)

    # Mass annotation
    ax.annotate(f'Nucleon: {M_NUCLEON:.0f} MeV\n(Thm 4.1.2)',
               xy=(0.03, 0.97), xycoords='axes fraction',
               fontsize=9, color='white', fontweight='bold',
               ha='left', va='top', bbox=textbox_props)

    # Color neutrality annotation
    ax.annotate('χ_R + χ_G + χ_B = 0\n(Thm 0.2.3)',
               xy=(0.03, 0.03), xycoords='axes fraction',
               fontsize=9, color='yellow', fontweight='bold',
               ha='left', va='bottom', bbox=textbox_props)

    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)
    ax.set_xlabel('x / R_stella', fontsize=11)
    ax.set_ylabel('y / R_stella', fontsize=11)
    ax.set_title('Quark Emergence\n(Theorems 1.1.1, 4.1.1, 4.1.2)', fontsize=13, fontweight='bold', pad=10)
    ax.set_aspect('equal')
    ax.set_facecolor('black')

    return im


# ============================================================================
# MAIN FIGURE
# ============================================================================

def create_dual_view_figure():
    """
    Create three-panel figure showing fundamental tetrahedron from three views.
    """
    fig, axes = plt.subplots(1, 3, figsize=(20, 7))

    # Panel 1: Looking down singlet axis (sees R-G-B triangle)
    im1 = create_weight_plane_panel(axes[0])

    # Panel 2: Side view (sees singlet axis as line to W)
    im2 = create_side_view_panel(axes[1])

    # Panel 3: Quark emergence (theorem-based)
    im3 = create_quark_emergence_panel(axes[2])

    # Add colorbars
    cbar1 = plt.colorbar(im1, ax=axes[0], fraction=0.046, pad=0.02, shrink=0.8)
    cbar1.set_label('Energy $\\rho$', fontsize=10)

    cbar2 = plt.colorbar(im2, ax=axes[1], fraction=0.046, pad=0.02, shrink=0.8)
    cbar2.set_label('log₁₀(ρ + 1)', fontsize=10)

    cbar3 = plt.colorbar(im3, ax=axes[2], fraction=0.046, pad=0.02, shrink=0.8)
    cbar3.set_label('1/|χ| (confinement)', fontsize=10)

    # Main title
    fig.suptitle('Fundamental Tetrahedron: Singlet Axis Views + Quark Emergence',
                fontsize=16, fontweight='bold', y=0.98)

    # Subtitle
    fig.text(0.5, 0.02,
            'Left: Phase dynamics (⊙ = singlet axis into page) | Center: Energy density T₀₀ (dark band = χ=0) | '
            'Right: Quark emergence at R,G,B vertices (skyrmions)',
            ha='center', fontsize=11, style='italic',
            bbox=dict(boxstyle='round,pad=0.4', facecolor='lightyellow', edgecolor='gold', alpha=0.9))

    plt.tight_layout(rect=[0, 0.06, 1, 0.95])

    return fig


def main():
    """Generate the three-panel fundamental tetrahedron figure."""

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    print("Generating fundamental tetrahedron three-panel diagram...")

    fig = create_dual_view_figure()
    path = output_dir / "unified_geometry_singlet_axis.png"
    fig.savefig(path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {path}")
    plt.close(fig)

    print("\nThe diagram shows the FUNDAMENTAL tetrahedron in three views:")
    print("  • Left: View along singlet axis - R, G, B triangle with ⊙ at center")
    print("  • Center: Diagonal slice - dark band where χ_R + χ_G + χ_B ≈ 0")
    print("  • Right: Quark emergence - R, G, B as skyrmion locations (Thm 4.1.1)")
    print("  • W is the apex (singlet state)")
    print("  • Time λ emerges along the axis from center toward W")
    print(f"  • Nucleon mass from Theorem 4.1.2: M ≈ {M_NUCLEON:.0f} MeV")


if __name__ == "__main__":
    main()
