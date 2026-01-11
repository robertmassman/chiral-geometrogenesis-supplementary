#!/usr/bin/env python3
"""
Unified Geometry Build-Up: 6-Panel Pedagogical Figure

Shows how the "View Along Singlet Axis" panel is constructed step by step,
building from the basic energy fields to the complete picture with all
observables (baryons, mesons, gluons).

Panels:
1. T+ Energy Field - R, G, B color field sources
2. T+ and T- Energy Fields - Stella octangula duality
3. Geometric Structure - T+ and T- triangles
4. Phase Dynamics - Trajectories converging to center
5. Observation Region - Where physics emerges (Thm 0.2.3)
6. Complete Picture - Mesons, gluons, baryons

References:
- Theorem 0.2.3: Observation region emergence
- Theorem 1.1.2: Charge conjugation (T- antipodal to T+)
- Theorem 1.1.3: Color confinement geometry
- Theorem 4.1.1, 4.1.2: Skyrmion structure
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Circle
import matplotlib.patheffects as path_effects
from scipy.integrate import odeint

# ============================================================================
# CONSTANTS AND SETUP
# ============================================================================

EPSILON = 0.3  # Observation scale parameter

def get_fundamental_tetrahedron():
    """
    Get the fundamental tetrahedron vertices in weight space.
    """
    w_R = np.array([1.0, 0.0, 0.0])
    w_G = np.array([-0.5, np.sqrt(3)/2, 0.0])
    w_B = np.array([-0.5, -np.sqrt(3)/2, 0.0])
    w_W = np.array([0.0, 0.0, np.sqrt(2)])
    return w_R, w_G, w_B, w_W

def compute_energy_fundamental(x, y, vertices_2d, sigma=0.4):
    """
    Compute energy density from fundamental vertices.
    """
    rho = 0
    for v in vertices_2d:
        r2 = (x - v[0])**2 + (y - v[1])**2
        amplitude = np.exp(-r2 / (2 * sigma**2))
        rho += amplitude**2
    return rho

def phase_difference_dynamics(psi, t, K):
    """
    Phase dynamics for trajectories.
    """
    psi1, psi2 = psi
    dpsi1 = -K * (np.sin(psi1) + np.sin(psi1 - psi2))
    dpsi2 = -K * (np.sin(psi2) + np.sin(psi2 - psi1))
    return [dpsi1, dpsi2]

# ============================================================================
# PANEL CREATION FUNCTIONS
# ============================================================================

def setup_panel(ax, title):
    """Common panel setup."""
    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1.1)
    ax.set_aspect('equal')
    ax.set_facecolor('#1a1a2e')
    ax.grid(True, alpha=0.2, color='white', linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='white', linewidth=0.8, alpha=0.4)
    ax.axvline(x=0, color='white', linewidth=0.8, alpha=0.4)
    ax.set_title(title, fontsize=11, fontweight='bold', pad=8, color='black')
    ax.set_xlabel('x', fontsize=9)
    ax.set_ylabel('y', fontsize=9)

def get_vertices_and_grids():
    """Get common vertices and grid data."""
    w_R, w_G, w_B, w_W = get_fundamental_tetrahedron()

    v_R = w_R[:2]
    v_G = w_G[:2]
    v_B = w_B[:2]

    scale = 0.8
    v_R = scale * v_R
    v_G = scale * v_G
    v_B = scale * v_B
    vertices_scaled = [v_R, v_G, v_B]
    anti_vertices_scaled = [-v for v in vertices_scaled]

    x_grid = np.linspace(-1.2, 1.2, 200)
    y_grid = np.linspace(-1.2, 1.2, 200)
    X, Y = np.meshgrid(x_grid, y_grid)

    # Compute energy fields
    rho_energy_plus = np.zeros_like(X)
    rho_energy_minus = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy_plus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], vertices_scaled, sigma=0.4)
            rho_energy_minus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], anti_vertices_scaled, sigma=0.4)

    return vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale

def panel_1_t_plus_energy(ax):
    """Panel 1: T+ Energy Field only."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()

    setup_panel(ax, "1. T+ Energy Field\n(Color Field Sources)")

    # Plot T+ energy only
    im = ax.contourf(X, Y, rho_energy_plus, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_plus, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

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
    ax.annotate('T+ tetrahedron\nR, G, B vertices\n(quark colors)',
                (0.0, -0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='orange', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='orange', linewidth=1))

def panel_2_both_energies(ax):
    """Panel 2: T+ and T- Energy Fields."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()

    setup_panel(ax, "2. T+ and T- Energy\n(Stella Octangula)")

    # Combined energy (T+ dominant, T- subtle)
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus

    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # T+ vertices
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=350, zorder=25, edgecolor='white', linewidth=2.5)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=16, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=3, foreground='black')])

    # T- vertices (antipodal)
    anti_colors = ['#AA2222', '#22AA22', '#2222AA']
    anti_labels = ['R̄', 'Ḡ', 'B̄']
    for v, c, l in zip(anti_vertices_scaled, anti_colors, anti_labels):
        ax.scatter(*v, c=c, s=250, zorder=24, edgecolor='white', linewidth=1.5, alpha=0.8)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.12 * direction, fontsize=12, fontweight='bold',
                   color='#AAAAAA', ha='center', va='center', zorder=24,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Explanation
    ax.annotate('T- antipodal\n(antiquark colors)\nThm 1.1.2',
                (0.0, -0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='#AAAAAA', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='#AAAAAA', linewidth=1))

def panel_3_geometry(ax):
    """Panel 3: Add geometric structure (triangles)."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()

    setup_panel(ax, "3. Geometric Structure\n(T+ and T- Triangles)")

    # Combined energy
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # T+ triangle (solid cyan)
    fund_tri = Polygon(vertices_scaled, fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)

    # T- triangle (dashed gray)
    anti_triangle = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666',
                           linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_triangle)

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

    # Explanation
    ax.annotate('Stella octangula\n2 interpenetrating\ntetrahedra',
                (0.0, -0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='cyan', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='cyan', linewidth=1))

def panel_4_trajectories(ax):
    """Panel 4: Add phase trajectories."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()

    setup_panel(ax, "4. Phase Dynamics\n(Convergence to Center)")

    # Combined energy
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # Triangles
    fund_tri = Polygon(vertices_scaled, fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)
    anti_triangle = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666',
                           linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_triangle)

    # Phase trajectories
    K = 1.0
    t_span = np.linspace(0, 50, 500)
    np.random.seed(123)
    n_traj = 15
    traj_color = '#AA44AA'

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

        for j in range(len(trajectory_x) - 1):
            alpha_val = 0.3 + 0.6 * (j / len(trajectory_x))
            ax.plot(trajectory_x[j:j+2], trajectory_y[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.5, zorder=15)

        if len(trajectory_x) > 10:
            ax.annotate('', xy=(trajectory_x[-1], trajectory_y[-1]),
                       xytext=(trajectory_x[-10], trajectory_y[-10]),
                       arrowprops=dict(arrowstyle='->', color=traj_color, lw=2, alpha=0.9),
                       zorder=16)

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

    # Explanation
    ax.annotate('All phases\nconverge to\ncolor-neutral center',
                (0.0, -0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='#AA44AA', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='#AA44AA', linewidth=1))

def panel_5_observation(ax):
    """Panel 5: Add observation region and baryon location."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()

    setup_panel(ax, "5. Observation Region\n(Where Physics Emerges)")

    # Combined energy
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # Triangles
    fund_tri = Polygon(vertices_scaled, fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)
    anti_triangle = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666',
                           linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_triangle)

    # Phase trajectories (fewer for clarity)
    K = 1.0
    t_span = np.linspace(0, 50, 500)
    np.random.seed(123)
    n_traj = 10
    traj_color = '#AA44AA'

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

        for j in range(len(trajectory_x) - 1):
            alpha_val = 0.2 + 0.4 * (j / len(trajectory_x))
            ax.plot(trajectory_x[j:j+2], trajectory_y[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.0, zorder=15)

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
                (0.45, 0.45), fontsize=8, fontweight='bold',
                ha='center', va='center', color='cyan', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='cyan', linewidth=1))

    ax.annotate('Baryons\ncentered here',
                (0.65, 0.85), fontsize=8, fontweight='bold',
                ha='center', va='top', color='yellow', zorder=25,
                bbox=dict(boxstyle='round,pad=0.2', facecolor='black', alpha=0.85,
                         edgecolor='yellow', linewidth=1))

def panel_6_complete(ax):
    """Panel 6: Complete picture with mesons and gluons."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()

    setup_panel(ax, "6. Complete Picture\n(Mesons & Gluon Paths)")

    # Combined energy
    rho_energy_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_energy_total, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_total, levels=6, colors='orange', alpha=0.6, linewidths=1.5, zorder=1)

    # Triangles
    fund_tri = Polygon(vertices_scaled, fill=False,
                       edgecolor='cyan', linewidth=3, linestyle='-', zorder=10)
    ax.add_patch(fund_tri)
    anti_triangle = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666',
                           linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_triangle)

    # Phase trajectories (subtle)
    K = 1.0
    t_span = np.linspace(0, 50, 500)
    np.random.seed(123)
    n_traj = 10
    traj_color = '#AA44AA'

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

        for j in range(len(trajectory_x) - 1):
            alpha_val = 0.15 + 0.3 * (j / len(trajectory_x))
            ax.plot(trajectory_x[j:j+2], trajectory_y[j:j+2],
                   color=traj_color, alpha=alpha_val, linewidth=1.0, zorder=15)

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
    ax.annotate('Mesons (qq̄)',
                (-0.75, -0.75), fontsize=7, fontweight='bold',
                ha='center', va='top', color='#FF9999', zorder=25,
                bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.85,
                         edgecolor='#FF9999', linewidth=1))

    ax.annotate('Gluon paths',
                (-0.85, 0.6), fontsize=7, fontweight='bold',
                ha='center', va='top', color='#00FFFF', zorder=25,
                bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.85,
                         edgecolor='#00FFFF', linewidth=1))

# ============================================================================
# MAIN
# ============================================================================

def main():
    print("Generating 6-panel build-up figure...")

    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    fig.suptitle('Building the Singlet Axis View: From Energy Fields to Observables',
                 fontsize=16, fontweight='bold', y=0.98)

    # Create each panel
    panel_1_t_plus_energy(axes[0, 0])
    panel_2_both_energies(axes[0, 1])
    panel_3_geometry(axes[0, 2])
    panel_4_trajectories(axes[1, 0])
    panel_5_observation(axes[1, 1])
    panel_6_complete(axes[1, 2])

    plt.tight_layout(rect=[0, 0.02, 1, 0.96])

    # Add footer with theorem references
    fig.text(0.5, 0.01,
             'References: Thm 0.2.3 (Observation Region) • Thm 1.1.2 (Charge Conjugation) • '
             'Thm 1.1.3 (Color Confinement) • Thm 4.1.1-4.1.2 (Skyrmions)',
             ha='center', va='bottom', fontsize=10, style='italic', color='gray')

    output_path = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/unified_geometry_buildup.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()

    print(f"  Saved: {output_path}")
    print("\nPanel descriptions:")
    print("  1. T+ Energy Field - R, G, B color field sources (quarks)")
    print("  2. T+ and T- Energy - Stella octangula duality (matter + antimatter)")
    print("  3. Geometric Structure - Interpenetrating tetrahedra")
    print("  4. Phase Dynamics - All trajectories converge to color-neutral center")
    print("  5. Observation Region - Where flat spacetime and physics emerge")
    print("  6. Complete Picture - Mesons (qq̄ pairs) and gluon confinement paths")

if __name__ == "__main__":
    main()
