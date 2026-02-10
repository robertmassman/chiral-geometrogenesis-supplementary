#!/usr/bin/env python3
"""
Unified Geometry Complete Story: 9-Panel Pedagogical Figure

Tells the complete story of Chiral Geometrogenesis in 9 panels (3x3 grid):

ROW 1: Building the Weight Space View
  1. T+ Energy Field - R, G, B color sources
  2. Stella Octangula - T+ and T- together
  3. Complete Weight View - All elements combined

ROW 2: From 2D to 3D Structure
  4. Diagonal Slice - Cross-section showing z-axis
  5. Time Emergence - The singlet axis λ
  6. Energy Density - Theorem 5.1.1

ROW 3: Physical Observables
  7. Color Neutrality - Where χ=0
  8. Quark Emergence - Confinement boundary
  9. Summary - Key physics

References:
- Theorem 0.2.3: Observation region emergence
- Theorem 1.1.1-1.1.3: Color structure and confinement
- Theorem 4.1.1-4.1.2: Skyrmion structure and mass
- Theorem 5.1.1: Energy density
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Circle
import matplotlib.patheffects as path_effects
from scipy.integrate import odeint

# ============================================================================
# CONSTANTS AND SETUP
# ============================================================================

EPSILON = 0.3

# Stella octangula vertices (same as main script)
STELLA_VERTICES = {
    'R': np.array([1.0, 0.0, 0.0]),
    'G': np.array([-0.5, np.sqrt(3)/2, 0.0]),
    'B': np.array([-0.5, -np.sqrt(3)/2, 0.0]),
    'W': np.array([0.0, 0.0, np.sqrt(2)])
}

def get_fundamental_tetrahedron():
    w_R = np.array([1.0, 0.0, 0.0])
    w_G = np.array([-0.5, np.sqrt(3)/2, 0.0])
    w_B = np.array([-0.5, -np.sqrt(3)/2, 0.0])
    w_W = np.array([0.0, 0.0, np.sqrt(2)])
    return w_R, w_G, w_B, w_W

def compute_energy_fundamental(x, y, vertices_2d, sigma=0.4):
    rho = 0
    for v in vertices_2d:
        r2 = (x - v[0])**2 + (y - v[1])**2
        amplitude = np.exp(-r2 / (2 * sigma**2))
        rho += amplitude**2
    return rho

def phase_difference_dynamics(psi, t, K):
    psi1, psi2 = psi
    dpsi1 = -K * (np.sin(psi1) + np.sin(psi1 - psi2))
    dpsi2 = -K * (np.sin(psi2) + np.sin(psi2 - psi1))
    return [dpsi1, dpsi2]

def chi_field(x, c):
    """Single color field χ_c at position x."""
    vertex = STELLA_VERTICES[c]
    r = np.linalg.norm(x - vertex)
    sigma = 0.5
    return np.exp(-r**2 / (2 * sigma**2))

def chi_total(x):
    """Total color field χ_R + χ_G + χ_B."""
    return chi_field(x, 'R') + chi_field(x, 'G') + chi_field(x, 'B')

def energy_density_5_1_1(x, kappa=1.0, sigma=0.5):
    """Energy density from Theorem 5.1.1."""
    chi_t = chi_total(x)
    rho = kappa * chi_t**2
    for c in ['R', 'G', 'B']:
        vertex = STELLA_VERTICES[c]
        r = np.linalg.norm(x - vertex)
        rho += 0.3 * np.exp(-r**2 / (2 * sigma**2))
    return rho

def color_neutrality_measure(x):
    return np.abs(chi_total(x))

# ============================================================================
# SHARED SETUP
# ============================================================================

def setup_panel(ax, title, fontsize=10):
    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1.1)
    ax.set_aspect('equal')
    ax.set_facecolor('#1a1a2e')
    ax.grid(True, alpha=0.2, color='white', linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='white', linewidth=0.8, alpha=0.4)
    ax.axvline(x=0, color='white', linewidth=0.8, alpha=0.4)
    ax.set_title(title, fontsize=fontsize, fontweight='bold', pad=6, color='black')
    ax.tick_params(labelsize=7)

def get_vertices_and_grids():
    w_R, w_G, w_B, w_W = get_fundamental_tetrahedron()
    v_R, v_G, v_B = w_R[:2], w_G[:2], w_B[:2]
    scale = 0.8
    v_R, v_G, v_B = scale * v_R, scale * v_G, scale * v_B
    vertices_scaled = [v_R, v_G, v_B]
    anti_vertices_scaled = [-v for v in vertices_scaled]

    x_grid = np.linspace(-1.2, 1.2, 150)
    y_grid = np.linspace(-1.2, 1.2, 150)
    X, Y = np.meshgrid(x_grid, y_grid)

    rho_energy_plus = np.zeros_like(X)
    rho_energy_minus = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(X.shape[1]):
            rho_energy_plus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], vertices_scaled, sigma=0.4)
            rho_energy_minus[i, j] = compute_energy_fundamental(X[i, j], Y[i, j], anti_vertices_scaled, sigma=0.4)

    return vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale

# ============================================================================
# ROW 1: Building the Weight Space View
# ============================================================================

def panel_1_t_plus(ax):
    """Panel 1: T+ Energy Field only."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()
    setup_panel(ax, "1. T+ Energy Field\n(Quark Colors)")

    im = ax.contourf(X, Y, rho_energy_plus, levels=50, cmap='hot', alpha=0.85, zorder=0)
    ax.contour(X, Y, rho_energy_plus, levels=5, colors='orange', alpha=0.5, linewidths=1.0, zorder=1)

    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=250, zorder=25, edgecolor='white', linewidth=2)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.1 * direction, fontsize=14, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    ax.annotate('Color field\nsources\n(Thm 1.1.1)', (0, -0.8), fontsize=7, ha='center',
               color='orange', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8, edgecolor='orange'))

def panel_2_stella(ax):
    """Panel 2: Stella Octangula - T+ and T- together."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()
    setup_panel(ax, "2. Stella Octangula\n(T+ and T-)")

    rho_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_total, levels=50, cmap='hot', alpha=0.85, zorder=0)

    # Triangles
    fund_tri = Polygon(vertices_scaled, fill=False, edgecolor='cyan', linewidth=2.5, zorder=10)
    ax.add_patch(fund_tri)
    anti_tri = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666', linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_tri)

    # T+ vertices
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=250, zorder=25, edgecolor='white', linewidth=2)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.1 * direction, fontsize=14, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # T- vertices
    anti_colors = ['#AA2222', '#22AA22', '#2222AA']
    anti_labels = ['R̄', 'Ḡ', 'B̄']
    for v, c, l in zip(anti_vertices_scaled, anti_colors, anti_labels):
        ax.scatter(*v, c=c, s=180, zorder=24, edgecolor='white', linewidth=1.5, alpha=0.8)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.1 * direction, fontsize=10, fontweight='bold',
                   color='#AAAAAA', ha='center', va='center', zorder=24,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    ax.annotate('Interpenetrating\ntetrahedra\n(Thm 1.1.2)', (0, -0.8), fontsize=7, ha='center',
               color='cyan', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8, edgecolor='cyan'))

def panel_3_complete_weight(ax):
    """Panel 3: Complete Weight Space View."""
    vertices_scaled, anti_vertices_scaled, X, Y, rho_energy_plus, rho_energy_minus, scale = get_vertices_and_grids()
    setup_panel(ax, "3. Weight Space View\n(Complete)")

    rho_total = rho_energy_plus + 0.3 * rho_energy_minus
    im = ax.contourf(X, Y, rho_total, levels=50, cmap='hot', alpha=0.85, zorder=0)

    # Triangles
    fund_tri = Polygon(vertices_scaled, fill=False, edgecolor='cyan', linewidth=2.5, zorder=10)
    ax.add_patch(fund_tri)
    anti_tri = Polygon(anti_vertices_scaled, fill=False, edgecolor='#666666', linewidth=2, linestyle='--', alpha=0.6, zorder=5)
    ax.add_patch(anti_tri)

    # Trajectories (simplified)
    K, t_span = 1.0, np.linspace(0, 50, 300)
    np.random.seed(123)
    traj_color = '#AA44AA'
    for i in range(8):
        phi0_G = np.random.uniform(0, 2*np.pi)
        phi0_B = np.random.uniform(0, 2*np.pi)
        psi0 = np.array([phi0_G, phi0_B - phi0_G])
        solution = odeint(phase_difference_dynamics, psi0, t_span, args=(K,))
        traj_x, traj_y = [], []
        for psi in solution:
            psi1, psi2 = psi
            z_R, z_G, z_B = np.exp(0j), np.exp(1j * psi1), np.exp(1j * (psi1 + psi2))
            color_sum = (z_R + z_G + z_B) / 3
            traj_x.append(scale * np.real(color_sum) * 3)
            traj_y.append(scale * np.imag(color_sum) * 3)
        ax.plot(traj_x, traj_y, color=traj_color, alpha=0.4, linewidth=1, zorder=15)

    # Observation region
    R_obs = EPSILON * 0.8
    obs_region = Circle((0, 0), R_obs, fill=True, facecolor='white', edgecolor='cyan', linewidth=2, alpha=0.25, zorder=18)
    ax.add_patch(obs_region)
    ax.scatter(0, 0, s=100, c='white', marker='o', zorder=20, edgecolor='cyan', linewidth=1.5)

    # Mesons
    meson_colors = ['#FF6666', '#66FF66', '#6666FF']
    for v_q, v_anti, mc in zip(vertices_scaled, anti_vertices_scaled, meson_colors):
        ax.plot([v_q[0], v_anti[0]], [v_q[1], v_anti[1]], color=mc, linewidth=2, linestyle=':', alpha=0.6, zorder=12)

    # Gluon paths
    edge_colors = ['#FF00FF', '#00FFFF', '#FFFF00']
    for i in range(3):
        v1, v2 = vertices_scaled[i], vertices_scaled[(i + 1) % 3]
        ax.plot([v1[0], v2[0]], [v1[1], v2[1]], color=edge_colors[i], linewidth=3, alpha=0.35, zorder=8)

    # Vertices
    colors_fund = ['#FF4444', '#44FF44', '#4444FF']
    labels_fund = ['R', 'G', 'B']
    for v, c, l in zip(vertices_scaled, colors_fund, labels_fund):
        ax.scatter(*v, c=c, s=250, zorder=25, edgecolor='white', linewidth=2)
        direction = v / np.linalg.norm(v)
        ax.annotate(l, v + 0.1 * direction, fontsize=14, fontweight='bold',
                   color='white', ha='center', va='center', zorder=25,
                   path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    anti_colors = ['#AA2222', '#22AA22', '#2222AA']
    anti_labels = ['R̄', 'Ḡ', 'B̄']
    for v, c, l in zip(anti_vertices_scaled, anti_colors, anti_labels):
        ax.scatter(*v, c=c, s=180, zorder=24, edgecolor='white', linewidth=1.5, alpha=0.8)

    ax.annotate('View from W\n(singlet axis)', (0.6, 0.8), fontsize=7, ha='center',
               color='gold', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8, edgecolor='gold'))

# ============================================================================
# ROW 2: From 2D to 3D Structure
# ============================================================================

def panel_4_diagonal_slice(ax):
    """Panel 4: Diagonal Slice showing z-axis."""
    setup_panel(ax, "4. Diagonal Slice\n(x=y plane)")
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)

    n_points = 80
    extent = 1.5
    x_range = np.linspace(-extent, extent, n_points)
    z_range = np.linspace(-extent, extent, n_points)

    rho_grid = np.zeros((n_points, n_points))
    for i, x_val in enumerate(x_range):
        for j, z_val in enumerate(z_range):
            pos = np.array([x_val, x_val, z_val])
            rho_grid[j, i] = energy_density_5_1_1(pos)

    rho_log = np.log10(rho_grid + 1)
    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent], origin='lower', cmap='hot')

    # Mark vertices
    for name, vertex in STELLA_VERTICES.items():
        on_diagonal = abs(vertex[0] - vertex[1]) < 0.01
        if on_diagonal:
            ax.plot(vertex[0], vertex[2], 'wo', markersize=10, markeredgecolor='black', markeredgewidth=1.5, zorder=10)
        else:
            ax.plot(vertex[0], vertex[2], 'o', markersize=8, markerfacecolor='none',
                   markeredgecolor='white', markeredgewidth=2, zorder=10)

        if name == 'W':
            color = 'gold'
        elif name == 'R':
            color = '#FF6666'
        elif name == 'G':
            color = '#66FF66'
        else:
            color = '#6666FF'
        ax.annotate(name, (vertex[0] + 0.1, vertex[2] + 0.1), fontsize=10, color=color,
                   fontweight='bold', path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    ax.scatter(0, 0, c='white', s=80, marker='*', edgecolors='black', linewidths=1, zorder=12)

    ax.annotate('Cross-section\nthrough tetrahedra', (-1.3, -1.3), fontsize=7, ha='left',
               color='white', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8))

def panel_5_time_emergence(ax):
    """Panel 5: Singlet axis and time emergence."""
    setup_panel(ax, "5. Time Emergence\n(Singlet Axis λ)")
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)

    n_points = 80
    extent = 1.5
    x_range = np.linspace(-extent, extent, n_points)
    z_range = np.linspace(-extent, extent, n_points)

    rho_grid = np.zeros((n_points, n_points))
    for i, x_val in enumerate(x_range):
        for j, z_val in enumerate(z_range):
            pos = np.array([x_val, x_val, z_val])
            rho_grid[j, i] = energy_density_5_1_1(pos)

    rho_log = np.log10(rho_grid + 1)
    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent], origin='lower', cmap='hot', alpha=0.7)

    # Singlet axis (from center to W)
    W = STELLA_VERTICES['W']
    ax.plot([0, W[0]], [0, W[2]], color='gold', linewidth=4, linestyle='-', alpha=0.9, zorder=8)
    ax.annotate('', xy=(W[0]*0.8, W[2]*0.8), xytext=(0, 0),
               arrowprops=dict(arrowstyle='->', color='gold', lw=3), zorder=9)

    # Time label
    ax.annotate('λ → (time)', (W[0]*0.4 + 0.15, W[2]*0.4 + 0.1), fontsize=11, color='gold',
               fontweight='bold', path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Mark center
    ax.scatter(0, 0, c='cyan', s=150, marker='o', edgecolors='white', linewidths=2, zorder=12)
    ax.annotate('Origin\n(χ=0)', (0.15, -0.3), fontsize=8, color='cyan',
               path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    # Mark W
    ax.plot(W[0], W[2], 'o', markersize=12, color='gold', markeredgecolor='white', markeredgewidth=2, zorder=10)
    ax.annotate('W', (W[0] + 0.1, W[2] + 0.1), fontsize=12, color='gold', fontweight='bold',
               path_effects=[path_effects.withStroke(linewidth=2, foreground='black')])

    ax.annotate('Internal time\nemerges along\nsinglet axis\n(Thm 0.2.2)', (-1.3, -1.0), fontsize=7, ha='left',
               color='gold', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8, edgecolor='gold'))

def panel_6_energy_density(ax):
    """Panel 6: Energy density T_00 from Theorem 5.1.1."""
    setup_panel(ax, "6. Energy Density T₀₀\n(Theorem 5.1.1)")
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)

    n_points = 80
    extent = 1.5
    x_range = np.linspace(-extent, extent, n_points)
    z_range = np.linspace(-extent, extent, n_points)

    rho_grid = np.zeros((n_points, n_points))
    for i, x_val in enumerate(x_range):
        for j, z_val in enumerate(z_range):
            pos = np.array([x_val, x_val, z_val])
            rho_grid[j, i] = energy_density_5_1_1(pos)

    rho_log = np.log10(rho_grid + 1)
    im = ax.imshow(rho_log, extent=[-extent, extent, -extent, extent], origin='lower', cmap='hot')

    # Dark band annotation
    ax.annotate('Dark band:\nχ = 0\n(color neutral)', (0.05, 1.3), fontsize=7, ha='left',
               color='cyan', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8, edgecolor='cyan'))

    # Energy formula
    ax.annotate('T₀₀ = κχ²', (1.3, -1.3), fontsize=9, ha='right',
               color='white', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8))

# ============================================================================
# ROW 3: Physical Observables
# ============================================================================

def panel_7_color_neutrality(ax):
    """Panel 7: Color neutrality - where χ=0."""
    setup_panel(ax, "7. Color Neutrality\n(χ_total = 0)")
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)

    n_points = 100
    extent = 1.5
    p_range = np.linspace(-extent, extent, n_points)
    q_range = np.linspace(-extent, extent, n_points)

    color_neutral = np.zeros((n_points, n_points))
    for i, p in enumerate(p_range):
        for j, q in enumerate(q_range):
            x_3d = np.array([p, q, 0])
            color_neutral[j, i] = color_neutrality_measure(x_3d)

    im = ax.imshow(1 / (color_neutral + 0.1), extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='inferno', alpha=0.85)

    # Vertex markers
    for name, color in [('R', '#FF0000'), ('G', '#00FF00'), ('B', '#0000FF')]:
        v = STELLA_VERTICES[name]
        ax.plot(v[0], v[1], 'o', markersize=16, color=color, markeredgecolor='white', markeredgewidth=2, zorder=20)
        ax.annotate(name, (v[0], v[1]), fontsize=12, fontweight='bold', ha='center', va='center', color='white', zorder=21)

    # Center
    ax.scatter(0, 0, c='cyan', s=100, marker='*', edgecolors='white', linewidths=1.5, zorder=12)

    ax.annotate('Bright = color\nneutral (confined)\n(Thm 1.1.3)', (-1.3, -1.0), fontsize=7, ha='left',
               color='yellow', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8, edgecolor='yellow'))

def panel_8_quark_emergence(ax):
    """Panel 8: Quark emergence and confinement."""
    setup_panel(ax, "8. Quark Emergence\n(Confinement)")
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)

    n_points = 100
    extent = 1.5
    p_range = np.linspace(-extent, extent, n_points)
    q_range = np.linspace(-extent, extent, n_points)

    color_neutral = np.zeros((n_points, n_points))
    for i, p in enumerate(p_range):
        for j, q in enumerate(q_range):
            x_3d = np.array([p, q, 0])
            color_neutral[j, i] = color_neutrality_measure(x_3d)

    im = ax.imshow(1 / (color_neutral + 0.1), extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='inferno', alpha=0.85)

    # Pressure contours
    for c, color in [('R', '#FF4444'), ('G', '#44FF44'), ('B', '#4444FF')]:
        vertex = STELLA_VERTICES[c]
        for r in [0.3, 0.5, 0.7]:
            circle = Circle((vertex[0], vertex[1]), r, fill=False, color=color, alpha=0.3, linewidth=1.5, linestyle='--')
            ax.add_patch(circle)

    # Vertex markers
    for name, color in [('R', '#FF0000'), ('G', '#00FF00'), ('B', '#0000FF')]:
        v = STELLA_VERTICES[name]
        ax.plot(v[0], v[1], 'o', markersize=18, color=color, markeredgecolor='white', markeredgewidth=2, zorder=20)
        ax.annotate(name, (v[0], v[1]), fontsize=14, fontweight='bold', ha='center', va='center', color='white', zorder=21)

    # Confinement bag
    R_bag = 1.2
    bag_circle = Circle((0, 0), R_bag, fill=False, color='cyan', linewidth=3, linestyle='-', zorder=15)
    ax.add_patch(bag_circle)

    # Baryon triangle
    baryon_triangle = Polygon([STELLA_VERTICES['R'][:2], STELLA_VERTICES['G'][:2], STELLA_VERTICES['B'][:2]],
                              fill=False, edgecolor='yellow', linewidth=2.5, linestyle='-', zorder=18)
    ax.add_patch(baryon_triangle)

    ax.annotate('Confinement\nboundary\n(bag)', (0.9, -1.2), fontsize=7, ha='center',
               color='cyan', bbox=dict(boxstyle='round,pad=0.15', facecolor='black', alpha=0.8, edgecolor='cyan'))

def panel_9_summary(ax):
    """Panel 9: Summary of key physics."""
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_facecolor('#1a1a2e')
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_title("9. Key Physics\n(Summary)", fontsize=10, fontweight='bold', pad=6, color='black')

    # Summary text
    summary_text = """
CHIRAL GEOMETROGENESIS

Structure:
• Stella octangula (T+ ∪ T-)
• R, G, B = color sources
• R̄, Ḡ, B̄ = anti-colors

Emergence:
• Time λ along singlet axis
• Observation at χ=0 center
• Flat spacetime emerges

Observables:
• Baryons at centroid
• Mesons: qq̄ pairs
• Gluons: edge-confined

Mass (Thm 4.1.2):
• M_nucleon ≈ 938 MeV
• From topological winding
"""

    ax.text(0.5, 0.5, summary_text, fontsize=8, ha='center', va='center',
           color='white', family='monospace',
           bbox=dict(boxstyle='round,pad=0.5', facecolor='#2a2a4e', alpha=0.9, edgecolor='gold', linewidth=2))

# ============================================================================
# MAIN
# ============================================================================

def main():
    print("Generating 9-panel complete story figure...")

    fig, axes = plt.subplots(3, 3, figsize=(15, 15))
    fig.suptitle('Chiral Geometrogenesis: The Complete Picture',
                 fontsize=16, fontweight='bold', y=0.98)

    # Row 1: Building Weight Space
    panel_1_t_plus(axes[0, 0])
    panel_2_stella(axes[0, 1])
    panel_3_complete_weight(axes[0, 2])

    # Row 2: 2D to 3D
    panel_4_diagonal_slice(axes[1, 0])
    panel_5_time_emergence(axes[1, 1])
    panel_6_energy_density(axes[1, 2])

    # Row 3: Observables
    panel_7_color_neutrality(axes[2, 0])
    panel_8_quark_emergence(axes[2, 1])
    panel_9_summary(axes[2, 2])

    # Row labels
    fig.text(0.02, 0.83, 'Row 1:\nWeight\nSpace', fontsize=9, fontweight='bold', va='center', color='gray')
    fig.text(0.02, 0.5, 'Row 2:\n3D\nStructure', fontsize=9, fontweight='bold', va='center', color='gray')
    fig.text(0.02, 0.17, 'Row 3:\nPhysical\nObservables', fontsize=9, fontweight='bold', va='center', color='gray')

    plt.tight_layout(rect=[0.04, 0.02, 1, 0.96])

    output_path = '/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/unified_geometry_complete_story.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white', edgecolor='none')
    plt.close()

    print(f"  Saved: {output_path}")
    print("\nStory structure:")
    print("  Row 1: Building the Weight Space View")
    print("    1. T+ Energy Field (quark colors)")
    print("    2. Stella Octangula (T+ and T-)")
    print("    3. Complete Weight View (all elements)")
    print("  Row 2: From 2D to 3D Structure")
    print("    4. Diagonal Slice (cross-section)")
    print("    5. Time Emergence (singlet axis λ)")
    print("    6. Energy Density T₀₀ (Thm 5.1.1)")
    print("  Row 3: Physical Observables")
    print("    7. Color Neutrality (χ=0)")
    print("    8. Quark Emergence (confinement)")
    print("    9. Summary (key physics)")

if __name__ == "__main__":
    main()
