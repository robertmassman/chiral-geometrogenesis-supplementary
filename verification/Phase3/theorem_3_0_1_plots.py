"""
Theorem 3.0.1 Visualization: Pressure-Modulated Superposition
=============================================================

This script creates visualizations for the key results in Theorem 3.0.1,
particularly the nodal line discovery (Version 2.1).

Key concepts:
- VEV vanishes along the W-axis (nodal line), not just at center
- W-axis: points where x₁ = x₂ = -x₃ (equidistant from R, G, B vertices)
- Pressure functions P_c(x) = 1/(|x - x_c|² + ε²)
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Line3DCollection
from matplotlib import cm
from matplotlib.colors import Normalize
from matplotlib.patches import FancyArrowPatch
from mpl_toolkits.mplot3d.proj3d import proj_transform

# Custom 3D arrow class for matplotlib
class Arrow3D(FancyArrowPatch):
    """Draw a 3D arrow in matplotlib."""
    def __init__(self, xs, ys, zs, *args, **kwargs):
        super().__init__((0, 0), (0, 0), *args, **kwargs)
        self._verts3d = xs, ys, zs

    def do_3d_projection(self, renderer=None):
        xs3d, ys3d, zs3d = self._verts3d
        xs, ys, zs = proj_transform(xs3d, ys3d, zs3d, self.axes.M)
        self.set_positions((xs[0], ys[0]), (xs[1], ys[1]))
        return np.min(zs)

# Tetrahedron vertices (from Definition 0.1.3)
# R, G, B are color vertices, W is the color-singlet vertex
vertices = {
    'R': np.array([1, 1, -1]) / np.sqrt(3),
    'G': np.array([-1, 1, 1]) / np.sqrt(3),
    'B': np.array([1, -1, 1]) / np.sqrt(3),
    'W': np.array([-1, -1, -1]) / np.sqrt(3)  # Color singlet direction
}

# Physical constants (from Section 13)
f_pi = 92.1  # MeV, pion decay constant
m_pi = 139.57  # MeV, pion mass
Lambda_QCD = 200  # MeV

def pressure(x, vertex, epsilon=0.5):
    """
    Pressure function P_c(x) = 1/(|x - x_c|² + ε²)

    Parameters:
        x: position (3D array or arrays for vectorized)
        vertex: vertex position (3D array)
        epsilon: regularization parameter
    """
    diff = x - vertex
    dist_sq = np.sum(diff**2, axis=-1)
    return 1.0 / (dist_sq + epsilon**2)

def vev_magnitude_squared(x, epsilon=0.5):
    """
    VEV magnitude squared from Theorem 3.0.1, Section 3.4:
    v²_χ = (a₀²/2)[(P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)²]

    Returns normalized (a₀ = 1) value.
    """
    P_R = pressure(x, vertices['R'], epsilon)
    P_G = pressure(x, vertices['G'], epsilon)
    P_B = pressure(x, vertices['B'], epsilon)

    return 0.5 * ((P_R - P_G)**2 + (P_G - P_B)**2 + (P_B - P_R)**2)

def vev_magnitude(x, epsilon=0.5):
    """VEV magnitude v_χ(x)"""
    return np.sqrt(vev_magnitude_squared(x, epsilon))

def is_on_w_axis(x, tol=1e-6):
    """
    Check if point is on W-axis: x₁ = x₂ = -x₃
    (The nodal line from Section 4.2)
    """
    return (np.abs(x[..., 0] - x[..., 1]) < tol) & (np.abs(x[..., 0] + x[..., 2]) < tol)


# =============================================================================
# FIGURE 1: VEV Magnitude Heatmap with Nodal Line
# =============================================================================
def plot_vev_heatmap():
    """
    2D slice showing VEV magnitude and the nodal line (W-axis intersection).
    Slice through the x₃ = 0 plane and x₁ = x₂ plane.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    # Panel A: x₃ = 0 slice
    n = 200
    x = np.linspace(-1.5, 1.5, n)
    y = np.linspace(-1.5, 1.5, n)
    X, Y = np.meshgrid(x, y)

    # Points in x₃ = 0 plane
    points = np.stack([X, Y, np.zeros_like(X)], axis=-1)
    V = vev_magnitude(points, epsilon=0.5)

    ax = axes[0]
    im = ax.contourf(X, Y, V, levels=50, cmap='plasma')
    plt.colorbar(im, ax=ax, label=r'$v_\chi(x)$ (normalized)')

    # Mark the center
    ax.plot(0, 0, 'w*', markersize=15, markeredgecolor='black', label='Center')

    # Project vertices onto x₃=0 plane
    for name, v in vertices.items():
        if name != 'W':
            ax.plot(v[0], v[1], 'o', markersize=10, label=f'{name} vertex')

    # Note: W-axis only intersects x₃=0 at origin (since on W-axis: x₁=x₂=-x₃, so x₃=0 → all=0)
    ax.axhline(0, color='cyan', linestyle='--', alpha=0.5)
    ax.axvline(0, color='cyan', linestyle='--', alpha=0.5)
    ax.text(0.1, 0.1, 'W-axis\n(nodal)', color='white', fontsize=10,
            bbox=dict(boxstyle='round', facecolor='black', alpha=0.5))

    # Add ARROW OF TIME - W-axis points INTO the page (toward -x₃, toward W vertex)
    # Draw a symbol at origin showing time flows perpendicular to this slice
    # Use ⊗ symbol (circle with X) to indicate "into page"
    ax.plot(0, 0, 'o', markersize=25, color='yellow', markeredgecolor='black', markeredgewidth=2)
    ax.plot(0, 0, 'x', markersize=15, color='black', markeredgewidth=3)
    ax.text(-0.45, -0.35, r'$\lambda$ (into page)', fontsize=10, color='yellow', fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='black', alpha=0.7))

    ax.set_xlabel(r'$x_1$', fontsize=12)
    ax.set_ylabel(r'$x_2$', fontsize=12)
    ax.set_title(r'VEV Magnitude in $x_3 = 0$ Plane', fontsize=14)
    ax.set_aspect('equal')
    ax.legend(loc='upper right')

    # Panel B: Slice containing W-axis (x₁ = x₂ plane)
    # In this plane, points are (t, t, s) for parameters t, s
    # W-axis: t = -s, so it's the diagonal
    t = np.linspace(-1.5, 1.5, n)
    s = np.linspace(-1.5, 1.5, n)
    T, S = np.meshgrid(t, s)

    # Points in x₁ = x₂ plane: (t, t, s)
    points2 = np.stack([T, T, S], axis=-1)
    V2 = vev_magnitude(points2, epsilon=0.5)

    ax2 = axes[1]
    im2 = ax2.contourf(T, S, V2, levels=50, cmap='plasma')
    plt.colorbar(im2, ax=ax2, label=r'$v_\chi(x)$ (normalized)')

    # Draw W-axis: x₁ = x₂ = -x₃ → t = -s
    w_line = np.linspace(-1.2, 1.2, 100)
    ax2.plot(w_line, -w_line, 'c-', linewidth=3, label='W-axis (nodal line)')

    # Add ARROW OF TIME along W-axis (toward W vertex = increasing λ)
    # In the (t, x₃) plane where x₁=x₂=t, W-axis is t = -x₃
    # W vertex direction: t decreases, x₃ decreases (toward W at (-1,-1,-1)/√3)
    arrow_start_t, arrow_start_s = 0.6, -0.6  # Start point
    arrow_end_t, arrow_end_s = -0.6, 0.6      # End point (toward W)
    ax2.annotate('', xy=(arrow_end_t, arrow_end_s), xytext=(arrow_start_t, arrow_start_s),
                 arrowprops=dict(arrowstyle='->', color='yellow', lw=3, mutation_scale=20))
    ax2.text(-0.1, 0.5, r'$\lambda$ (time)', fontsize=12, color='yellow', fontweight='bold',
             rotation=-45, ha='center',
             bbox=dict(boxstyle='round', facecolor='black', alpha=0.7))

    # Mark center
    ax2.plot(0, 0, 'w*', markersize=15, markeredgecolor='black', label='Center')

    ax2.set_xlabel(r'$t$ (where $x_1 = x_2 = t$)', fontsize=12)
    ax2.set_ylabel(r'$x_3$', fontsize=12)
    ax2.set_title(r'VEV Magnitude in $x_1 = x_2$ Plane (W-axis visible)', fontsize=14)
    ax2.set_aspect('equal')
    ax2.legend(loc='upper right')

    plt.tight_layout()
    plt.savefig('theorem_3_0_1_fig1_vev_heatmap.png', dpi=150, bbox_inches='tight')
    plt.show()
    print("Saved: theorem_3_0_1_fig1_vev_heatmap.png")


# =============================================================================
# FIGURE 2: 3D Surface of Pressure Equality
# =============================================================================
def plot_pressure_equality_3d():
    """
    3D visualization showing the W-axis where P_R = P_G = P_B.
    """
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')

    # Draw tetrahedron edges
    edge_pairs = [
        ('R', 'G'), ('G', 'B'), ('B', 'R'),  # RGB face
        ('R', 'W'), ('G', 'W'), ('B', 'W')   # Edges to W
    ]
    for v1, v2 in edge_pairs:
        pts = np.array([vertices[v1], vertices[v2]])
        ax.plot3D(pts[:, 0], pts[:, 1], pts[:, 2], 'k-', alpha=0.3, linewidth=1)

    # Plot vertices
    colors = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'gray'}
    for name, v in vertices.items():
        ax.scatter(*v, color=colors[name], s=200, label=f'{name}', edgecolors='black')

    # Draw W-axis (nodal line)
    w_dir = vertices['W'] / np.linalg.norm(vertices['W'])
    t_vals = np.linspace(-1.5, 1.5, 100)
    w_axis = np.outer(t_vals, w_dir)
    ax.plot3D(w_axis[:, 0], w_axis[:, 1], w_axis[:, 2], 'c-', linewidth=4,
              label='W-axis (nodal line)')

    # Add ARROW OF TIME along W-axis
    # Time flows toward W vertex (color singlet direction)
    arrow_start = 0.5 * (-w_dir)  # Start from anti-W direction
    arrow_end = 0.8 * w_dir       # End toward W
    time_arrow = Arrow3D([arrow_start[0], arrow_end[0]],
                         [arrow_start[1], arrow_end[1]],
                         [arrow_start[2], arrow_end[2]],
                         mutation_scale=20, lw=3, arrowstyle='-|>',
                         color='yellow', zorder=100)
    ax.add_artist(time_arrow)

    # Label the time arrow
    label_pos = 0.6 * w_dir
    ax.text(label_pos[0] + 0.15, label_pos[1] + 0.15, label_pos[2],
            r'$\lambda$ (time)', fontsize=12, color='yellow', fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='black', alpha=0.7))

    # Create a sphere of sample points and color by VEV
    u = np.linspace(0, 2*np.pi, 50)
    v_ang = np.linspace(0, np.pi, 30)
    r = 0.8  # radius

    x_sph = r * np.outer(np.cos(u), np.sin(v_ang))
    y_sph = r * np.outer(np.sin(u), np.sin(v_ang))
    z_sph = r * np.outer(np.ones(np.size(u)), np.cos(v_ang))

    # Compute VEV on sphere
    points_sph = np.stack([x_sph, y_sph, z_sph], axis=-1)
    V_sph = vev_magnitude(points_sph, epsilon=0.5)

    # Plot sphere colored by VEV
    norm = Normalize(vmin=0, vmax=V_sph.max())
    ax.plot_surface(x_sph, y_sph, z_sph, facecolors=cm.plasma(norm(V_sph)),
                    alpha=0.6, rstride=1, cstride=1, linewidth=0, antialiased=False)

    # Mark where W-axis intersects the sphere (should be dark/low VEV)
    for sign in [-1, 1]:
        pt = sign * r * w_dir
        ax.scatter(*pt, color='cyan', s=100, marker='o', edgecolors='white', linewidths=2)

    ax.set_xlabel(r'$x_1$', fontsize=12)
    ax.set_ylabel(r'$x_2$', fontsize=12)
    ax.set_zlabel(r'$x_3$', fontsize=12)
    ax.set_title('VEV on Sphere (dark = low VEV)\nW-axis is the nodal line', fontsize=14)
    ax.legend(loc='upper left')

    # Add colorbar
    mappable = cm.ScalarMappable(norm=norm, cmap='plasma')
    mappable.set_array(V_sph)
    plt.colorbar(mappable, ax=ax, shrink=0.6, label=r'$v_\chi$')

    plt.tight_layout()
    plt.savefig('theorem_3_0_1_fig2_pressure_3d.png', dpi=150, bbox_inches='tight')
    plt.show()
    print("Saved: theorem_3_0_1_fig2_pressure_3d.png")


# =============================================================================
# FIGURE 3: VEV Profile Comparison
# =============================================================================
def plot_vev_profiles():
    """
    Compare VEV profile:
    - Along a generic radial direction (VEV > 0 away from origin)
    - Along the W-axis (VEV = 0 everywhere on axis)
    - Along direction toward R vertex
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Distances from center
    r = np.linspace(0, 1.2, 200)

    # Direction vectors
    radial_generic = np.array([1, 0, 0])  # x-axis (not W-axis)
    radial_to_R = vertices['R'] / np.linalg.norm(vertices['R'])
    w_axis_dir = vertices['W'] / np.linalg.norm(vertices['W'])

    # Panel A: VEV magnitude along different directions
    ax1 = axes[0]

    for direction, label, color, style in [
        (radial_generic, r'Generic ($x_1$-axis)', 'blue', '-'),
        (radial_to_R, 'Toward R vertex', 'red', '--'),
        (w_axis_dir, 'W-axis (nodal line)', 'cyan', '-.')
    ]:
        # Points along this direction
        points = np.outer(r, direction)
        V = vev_magnitude(points, epsilon=0.5)
        ax1.plot(r, V, color=color, linestyle=style, linewidth=2, label=label)

    ax1.axhline(0, color='gray', linestyle=':', alpha=0.5)
    ax1.set_xlabel(r'Distance from center $|x|$', fontsize=12)
    ax1.set_ylabel(r'VEV magnitude $v_\chi$', fontsize=12)
    ax1.set_title('VEV Profile Along Different Directions', fontsize=14)
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Annotate the key result
    ax1.annotate('W-axis: VEV = 0\n(nodal line)', xy=(0.5, 0.01), fontsize=10,
                 color='cyan', bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    # Panel B: Pressure comparison along W-axis vs off W-axis
    ax2 = axes[1]

    # Along W-axis
    points_w = np.outer(r, w_axis_dir)
    P_R_w = pressure(points_w, vertices['R'], epsilon=0.5)
    P_G_w = pressure(points_w, vertices['G'], epsilon=0.5)
    P_B_w = pressure(points_w, vertices['B'], epsilon=0.5)

    ax2.plot(r, P_R_w, 'r-', linewidth=2, label=r'$P_R$ on W-axis')
    ax2.plot(r, P_G_w, 'g--', linewidth=2, label=r'$P_G$ on W-axis')
    ax2.plot(r, P_B_w, 'b:', linewidth=2, label=r'$P_B$ on W-axis')

    # Along x-axis for comparison
    points_x = np.outer(r, radial_generic)
    P_R_x = pressure(points_x, vertices['R'], epsilon=0.5)
    P_G_x = pressure(points_x, vertices['G'], epsilon=0.5)

    ax2.plot(r, P_R_x, 'r-', linewidth=1, alpha=0.4, label=r'$P_R$ on $x_1$-axis')
    ax2.plot(r, P_G_x, 'g-', linewidth=1, alpha=0.4, label=r'$P_G$ on $x_1$-axis')

    ax2.set_xlabel(r'Distance from center $|x|$', fontsize=12)
    ax2.set_ylabel(r'Pressure $P_c$', fontsize=12)
    ax2.set_title('Pressure Functions: Equal on W-axis, Unequal Otherwise', fontsize=14)
    ax2.legend(loc='upper right', fontsize=9)
    ax2.grid(True, alpha=0.3)

    # Annotate
    ax2.annotate('All three pressures\nequal on W-axis!', xy=(0.3, 2.5), fontsize=10,
                 bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.8))

    plt.tight_layout()
    plt.savefig('theorem_3_0_1_fig3_vev_profiles.png', dpi=150, bbox_inches='tight')
    plt.show()
    print("Saved: theorem_3_0_1_fig3_vev_profiles.png")


# =============================================================================
# FIGURE 4: GMOR Relation and ChPT Parameters
# =============================================================================
def plot_gmor_relation():
    """
    Visualize the Gell-Mann–Oakes–Renner relation and parameter matching.
    From Section 5.4 and Section 13.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Panel A: GMOR relation
    ax1 = axes[0]

    # m_π² f_π² = -m_q <q̄q>
    # Plot m_π as function of m_q
    m_q_range = np.linspace(0, 10, 100)  # MeV
    condensate = -(272)**3  # MeV³ (FLAG 2021)

    # From GMOR: m_π² = -m_q <q̄q> / f_π²
    m_pi_sq = -m_q_range * condensate / f_pi**2
    m_pi_gmor = np.sqrt(np.maximum(m_pi_sq, 0))

    ax1.plot(m_q_range, m_pi_gmor, 'b-', linewidth=2, label='GMOR prediction')
    ax1.axhline(m_pi, color='r', linestyle='--', linewidth=1.5, label=f'Observed $m_\pi$ = {m_pi} MeV')
    ax1.axvline(3.43, color='g', linestyle=':', linewidth=1.5, label=r'$m_q$ = 3.43 MeV (PDG)')

    # Mark intersection
    ax1.plot(3.43, m_pi, 'ko', markersize=10)

    ax1.set_xlabel(r'Average quark mass $m_q$ (MeV)', fontsize=12)
    ax1.set_ylabel(r'Pion mass $m_\pi$ (MeV)', fontsize=12)
    ax1.set_title('GMOR Relation: $m_\pi^2 f_\pi^2 = -m_q\\langle\\bar{q}q\\rangle$', fontsize=14)
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 10)
    ax1.set_ylim(0, 250)

    # Add numerical check annotation
    lhs = m_pi**2 * f_pi**2
    rhs = 3.43 * (272)**3
    ax1.annotate(f'LHS: $m_\pi^2 f_\pi^2$ = {lhs/1e8:.2f}×10⁸ MeV⁴\n'
                 f'RHS: $m_q|⟨q̄q⟩|$ = {rhs/1e8:.2f}×10⁸ MeV⁴\n'
                 f'Ratio: {lhs/rhs:.2f} (O(1) as expected)',
                 xy=(5.5, 80), fontsize=10,
                 bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))

    # Panel B: Parameter summary bar chart
    ax2 = axes[1]

    params = ['$v_0 = f_\pi$', '$\\omega_0 = m_\pi$', '$\\Lambda_{QCD}$', '$\\Lambda$ (NDA)']
    values = [f_pi, m_pi, Lambda_QCD, 4*np.pi*f_pi]
    colors = ['steelblue', 'coral', 'forestgreen', 'purple']

    bars = ax2.bar(params, values, color=colors, edgecolor='black', linewidth=1.5)

    # Add value labels
    for bar, val in zip(bars, values):
        ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 20,
                 f'{val:.0f} MeV', ha='center', fontsize=11, fontweight='bold')

    ax2.set_ylabel('Energy Scale (MeV)', fontsize=12)
    ax2.set_title('Physical Parameters from QCD Phenomenology\n(Section 13)', fontsize=14)
    ax2.set_ylim(0, max(values) * 1.2)
    ax2.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig('theorem_3_0_1_fig4_gmor.png', dpi=150, bbox_inches='tight')
    plt.show()
    print("Saved: theorem_3_0_1_fig4_gmor.png")


# =============================================================================
# FIGURE 5: W-axis Physical Significance
# =============================================================================
def plot_w_axis_significance():
    """
    Illustrate the physical significance of the W-axis as nodal line.
    From Section 4.2.
    """
    fig = plt.figure(figsize=(14, 6))

    # Panel A: Geometry - W-axis equidistant from R, G, B
    ax1 = fig.add_subplot(121, projection='3d')

    # Plot tetrahedron
    for name, v in vertices.items():
        color = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'gray'}[name]
        ax1.scatter(*v, color=color, s=300, label=name, edgecolors='black', linewidths=2)

    # Draw RGB triangle
    rgb_verts = np.array([vertices['R'], vertices['G'], vertices['B'], vertices['R']])
    ax1.plot3D(rgb_verts[:, 0], rgb_verts[:, 1], rgb_verts[:, 2], 'k-', linewidth=2)

    # Draw W-axis
    w_dir = vertices['W'] / np.linalg.norm(vertices['W'])
    t_line = np.linspace(-1.2, 0.5, 100)
    w_line = np.outer(t_line, w_dir)
    ax1.plot3D(w_line[:, 0], w_line[:, 1], w_line[:, 2], 'c-', linewidth=4,
               label='W-axis\n(nodal line)')

    # Add ARROW OF TIME along W-axis
    arrow_start = 0.3 * (-w_dir)
    arrow_end = 0.5 * w_dir
    time_arrow = Arrow3D([arrow_start[0], arrow_end[0]],
                         [arrow_start[1], arrow_end[1]],
                         [arrow_start[2], arrow_end[2]],
                         mutation_scale=15, lw=3, arrowstyle='-|>',
                         color='yellow', zorder=100)
    ax1.add_artist(time_arrow)
    ax1.text(0.4 * w_dir[0], 0.4 * w_dir[1] + 0.2, 0.4 * w_dir[2],
             r'$\lambda$', fontsize=14, color='yellow', fontweight='bold')

    # Show equidistance: draw lines from a point on W-axis to R, G, B
    w_point = 0.3 * w_dir
    for name in ['R', 'G', 'B']:
        line = np.array([w_point, vertices[name]])
        ax1.plot3D(line[:, 0], line[:, 1], line[:, 2], '--',
                   color={'R': 'red', 'G': 'green', 'B': 'blue'}[name], alpha=0.6)
    ax1.scatter(*w_point, color='cyan', s=150, marker='D', edgecolors='black')

    ax1.set_xlabel('$x_1$')
    ax1.set_ylabel('$x_2$')
    ax1.set_zlabel('$x_3$')
    ax1.set_title('W-axis: Equidistant from R, G, B\n(Color Singlet Direction)', fontsize=12)
    ax1.legend(loc='upper left')

    # Panel B: Conceptual diagram
    ax2 = fig.add_subplot(122)
    ax2.set_xlim(-1, 3)
    ax2.set_ylim(-0.5, 3.5)
    ax2.axis('off')

    # Draw a summary box
    box_text = """
    W-Axis = Nodal Line (v_χ = 0)
    ══════════════════════════════

    ★ GEOMETRIC: W is 4th tetrahedron vertex,
       equidistant from R, G, B

    ★ ALGEBRAIC: W direction corresponds to
       Cartan subalgebra (color singlet)

    ★ DYNAMIC: Internal time λ may propagate
       along W-axis (orthogonal to "color space")

    ★ PHYSICAL: Matter (v_χ ≠ 0) exists OFF axis
       VEV = 0 ON axis (pure phase, no amplitude)

    ══════════════════════════════

    On W-axis: P_R = P_G = P_B
    => Perfect cancellation of 120-offset phases
    => v_chi = |Sum P_c exp(i*phi_c)| = 0
    """

    ax2.text(0, 3, box_text, fontsize=11, family='monospace',
             verticalalignment='top',
             bbox=dict(boxstyle='round,pad=0.5', facecolor='lightcyan',
                       edgecolor='darkcyan', linewidth=2))

    ax2.set_title('Physical Significance of Nodal Line\n(Theorem 3.0.1 v2.1)', fontsize=14)

    plt.tight_layout()
    plt.savefig('theorem_3_0_1_fig5_w_axis.png', dpi=150, bbox_inches='tight')
    plt.show()
    print("Saved: theorem_3_0_1_fig5_w_axis.png")


# =============================================================================
# FIGURE 6: Phase Evolution with Internal Time λ
# =============================================================================
def plot_phase_evolution():
    """
    Show how the chiral field phase evolves with internal time λ.
    From Section 5: χ(x,λ) = v_χ(x) exp(i[Φ_spatial(x) + λ])
    """
    fig, axes = plt.subplots(1, 3, figsize=(16, 5))

    # Internal time parameter
    lambda_vals = np.linspace(0, 4*np.pi, 200)
    omega_0 = m_pi  # MeV, from Section 5.4

    # Panel A: Phase evolution at a fixed spatial point
    ax1 = axes[0]

    # At a point off the W-axis (non-zero VEV)
    x_off_axis = np.array([0.3, 0.0, 0.0])  # On x₁-axis
    v_chi = vev_magnitude(x_off_axis, epsilon=0.5)

    # Spatial phase
    P_R = pressure(x_off_axis, vertices['R'], epsilon=0.5)
    P_G = pressure(x_off_axis, vertices['G'], epsilon=0.5)
    P_B = pressure(x_off_axis, vertices['B'], epsilon=0.5)

    chi_complex = P_R * 1 + P_G * np.exp(1j * 2*np.pi/3) + P_B * np.exp(1j * 4*np.pi/3)
    Phi_spatial = np.angle(chi_complex)

    # Total phase = Φ_spatial + λ
    Phi_total = Phi_spatial + lambda_vals

    # Real and imaginary parts of χ
    chi_real = v_chi * np.cos(Phi_total)
    chi_imag = v_chi * np.sin(Phi_total)

    ax1.plot(lambda_vals / np.pi, chi_real, 'b-', linewidth=2, label=r'Re[$\chi$]')
    ax1.plot(lambda_vals / np.pi, chi_imag, 'r--', linewidth=2, label=r'Im[$\chi$]')
    ax1.axhline(0, color='gray', linestyle=':', alpha=0.5)

    # Add arrow showing time direction
    ax1.annotate('', xy=(3.5, 0), xytext=(0.5, 0),
                 arrowprops=dict(arrowstyle='->', color='yellow', lw=2))
    ax1.text(2.0, -0.15, r'$\lambda$ (internal time)', fontsize=11, color='orange',
             ha='center', fontweight='bold')

    ax1.set_xlabel(r'Internal time $\lambda/\pi$', fontsize=12)
    ax1.set_ylabel(r'Field amplitude', fontsize=12)
    ax1.set_title(f'Chiral Field Oscillation\n(off W-axis, $v_\\chi$ = {v_chi:.2f})', fontsize=13)
    ax1.legend(loc='upper right')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 4)

    # Panel B: Phase portrait (Re vs Im)
    ax2 = axes[1]

    # Draw the circular trajectory
    theta = np.linspace(0, 2*np.pi, 100)
    ax2.plot(v_chi * np.cos(theta), v_chi * np.sin(theta), 'c-', linewidth=1, alpha=0.5)

    # Show a portion of the evolution with color gradient for time
    n_points = 50
    lambda_subset = lambda_vals[:n_points]
    Phi_subset = Phi_spatial + lambda_subset
    colors = plt.cm.viridis(np.linspace(0, 1, n_points))

    for i in range(n_points - 1):
        ax2.plot([v_chi * np.cos(Phi_subset[i]), v_chi * np.cos(Phi_subset[i+1])],
                 [v_chi * np.sin(Phi_subset[i]), v_chi * np.sin(Phi_subset[i+1])],
                 color=colors[i], linewidth=3)

    # Arrow showing direction of time
    i_arrow = n_points // 2
    dx = v_chi * (np.cos(Phi_subset[i_arrow+1]) - np.cos(Phi_subset[i_arrow]))
    dy = v_chi * (np.sin(Phi_subset[i_arrow+1]) - np.sin(Phi_subset[i_arrow]))
    ax2.annotate('', xy=(v_chi * np.cos(Phi_subset[i_arrow]) + 2*dx,
                         v_chi * np.sin(Phi_subset[i_arrow]) + 2*dy),
                 xytext=(v_chi * np.cos(Phi_subset[i_arrow]),
                         v_chi * np.sin(Phi_subset[i_arrow])),
                 arrowprops=dict(arrowstyle='->', color='yellow', lw=3))

    ax2.plot(0, 0, 'ko', markersize=8)
    ax2.text(0.05, 0.05, 'Origin', fontsize=10)

    ax2.set_xlabel(r'Re[$\chi$]', fontsize=12)
    ax2.set_ylabel(r'Im[$\chi$]', fontsize=12)
    ax2.set_title('Phase Portrait: $\\chi$ rotates in complex plane\n(arrow = direction of time)', fontsize=13)
    ax2.set_aspect('equal')
    ax2.grid(True, alpha=0.3)

    # Add colorbar for time
    sm = plt.cm.ScalarMappable(cmap='viridis', norm=plt.Normalize(0, lambda_subset[-1]/np.pi))
    sm.set_array([])
    cbar = plt.colorbar(sm, ax=ax2)
    cbar.set_label(r'$\lambda/\pi$', fontsize=11)

    # Panel C: Frequency and period
    ax3 = axes[2]

    # Show relationship between ω₀, m_π, and oscillation period
    # Period T = 2π/ω₀, with ω₀ = m_π
    T_osc = 2 * np.pi / omega_0  # in MeV⁻¹
    # Convert to fm/c: ℏc ≈ 197 MeV·fm
    hbar_c = 197  # MeV·fm
    T_fm = T_osc * hbar_c  # fm/c

    # Bar chart of time scales
    categories = [r'$\omega_0 = m_\pi$', r'$T = 2\pi/\omega_0$', r'$T$ (fm/c)']
    values_display = [omega_0, 2*np.pi/omega_0 * 1000, T_fm]  # middle one scaled for display
    colors = ['coral', 'steelblue', 'forestgreen']

    # Since values span different scales, use text annotations
    ax3.axis('off')

    # Draw a timeline
    ax3.annotate('', xy=(0.9, 0.5), xytext=(0.1, 0.5),
                 arrowprops=dict(arrowstyle='->', color='yellow', lw=4),
                 xycoords='axes fraction')
    ax3.text(0.5, 0.55, r'Internal Time $\lambda$', fontsize=14, ha='center',
             transform=ax3.transAxes, fontweight='bold')

    # Key values
    info_text = f"""
    OSCILLATION PARAMETERS
    ══════════════════════════════

    Frequency:   $\\omega_0 = m_\\pi = {omega_0:.1f}$ MeV

    Period:      $T = 2\\pi/\\omega_0 = {2*np.pi/omega_0:.3f}$ MeV$^{{-1}}$

    In natural units:  $T \\approx {T_fm:.1f}$ fm/c

    ══════════════════════════════

    PHYSICAL INTERPRETATION

    $\\bullet$ Phase advances by $2\\pi$ every period
    $\\bullet$ $\\omega_0$ set by pion mass (Goldstone)
    $\\bullet$ Time flows along W-axis (nodal line)
    $\\bullet$ Matter oscillates OFF the W-axis
    """

    ax3.text(0.5, 0.4, info_text, fontsize=11, family='monospace',
             ha='center', va='top', transform=ax3.transAxes,
             bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow',
                       edgecolor='orange', linewidth=2))

    ax3.set_title('Time Scale from QCD\n(Section 5.4)', fontsize=14)

    plt.tight_layout()
    plt.savefig('theorem_3_0_1_fig6_time_evolution.png', dpi=150, bbox_inches='tight')
    plt.show()
    print("Saved: theorem_3_0_1_fig6_time_evolution.png")


# =============================================================================
# MAIN EXECUTION
# =============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Theorem 3.0.1: Pressure-Modulated Superposition")
    print("Visualization Script (Version 2.1 - Nodal Line Discovery)")
    print("=" * 60)
    print()

    print("Creating Figure 1: VEV Magnitude Heatmap...")
    plot_vev_heatmap()
    print()

    print("Creating Figure 2: 3D Pressure Visualization...")
    plot_pressure_equality_3d()
    print()

    print("Creating Figure 3: VEV Profile Comparison...")
    plot_vev_profiles()
    print()

    print("Creating Figure 4: GMOR Relation...")
    plot_gmor_relation()
    print()

    print("Creating Figure 5: W-Axis Physical Significance...")
    plot_w_axis_significance()
    print()

    print("Creating Figure 6: Phase Evolution with Time...")
    plot_phase_evolution()
    print()

    print("=" * 60)
    print("All figures saved in current directory.")
    print("=" * 60)
