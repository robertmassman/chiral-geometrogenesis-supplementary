#!/usr/bin/env python3
"""
Figure: Definition 0.1.4 - Color Field Domains Visualization

Generates the main visualization for Definition 0.1.4 showing:
1. Vertex coloring (color sources in SU(3) weight diagram)
2. Color domains (Voronoi tessellation)
3. Vertex-face duality (source to depression mapping)
4. Pressure distribution (z=0 slice)
5. Depression ratio heatmap
6. Domain boundaries (SU(3) root perpendicularity)

Output: fig_definition_0_1_4_visualization.pdf, fig_definition_0_1_4_visualization.png

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap, LinearSegmentedColormap
import os

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05

# Stella octangula vertices (two interlocked tetrahedra)
VERTICES = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

# SU(3) Weight vectors
WEIGHTS_2D = {
    'R': np.array([1/2, 1/(2*np.sqrt(3))]),
    'G': np.array([-1/2, 1/(2*np.sqrt(3))]),
    'B': np.array([0, -1/np.sqrt(3)]),
}

# SU(3) Root vectors
ROOTS = {
    'RG': WEIGHTS_2D['R'] - WEIGHTS_2D['G'],
    'GB': WEIGHTS_2D['G'] - WEIGHTS_2D['B'],
    'BR': WEIGHTS_2D['B'] - WEIGHTS_2D['R'],
}

# Color palette
COLORS = {
    'R': '#FF0000',
    'G': '#00AA00',
    'B': '#0000FF',
    'W': '#888888',
}


# =============================================================================
# CORE FUNCTIONS
# =============================================================================

def pressure(x, x_c, eps=EPSILON):
    """Pressure function P_c(x)."""
    r_sq = np.sum((x - x_c)**2)
    return 1.0 / (r_sq + eps**2)


def depression_ratio(x, color, eps=EPSILON):
    """Depression ratio D_c(x)."""
    p_c = pressure(x, VERTICES[color], eps)
    p_other = sum(pressure(x, VERTICES[c], eps) for c in ['R', 'G', 'B'] if c != color)
    return p_other / p_c if p_c > 1e-10 else float('inf')


def dominant_color(x, eps=EPSILON):
    """Return dominant color at position x."""
    pressures = {c: pressure(x, VERTICES[c], eps) for c in ['R', 'G', 'B', 'W']}
    return max(pressures, key=pressures.get)


def get_face_center(vertex_name):
    """Get face center opposite to vertex."""
    return -VERTICES[vertex_name] / 3


# =============================================================================
# PANEL FUNCTIONS
# =============================================================================

def create_vertex_diagram(ax):
    """Panel 1: SU(3) weight diagram with vertex coloring."""

    # Plot weight vectors
    for name, w in WEIGHTS_2D.items():
        ax.scatter(*w, c=COLORS[name], s=200, zorder=5, edgecolors='black', linewidths=1.5)
        offset_x = 0.12 if name == 'B' else 0.08
        offset_y = 0.08 if name != 'B' else -0.12
        ax.annotate(f'$x_{name}$', (w[0]+offset_x, w[1]+offset_y), fontsize=12,
                   fontweight='bold', color=COLORS[name])

    # Draw triangle
    triangle = np.array([WEIGHTS_2D['R'], WEIGHTS_2D['G'], WEIGHTS_2D['B'], WEIGHTS_2D['R']])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=1.5, alpha=0.5)
    ax.fill(triangle[:-1, 0], triangle[:-1, 1], alpha=0.05, color='gray')

    # Draw arrows from center to vertices
    for name, w in WEIGHTS_2D.items():
        ax.annotate('', xy=(w[0]*0.85, w[1]*0.85), xytext=(0, 0),
                   arrowprops=dict(arrowstyle='->', color=COLORS[name], lw=2, alpha=0.6))

    # Center point
    ax.scatter(0, 0, c='black', s=50, zorder=10)
    ax.annotate('O', (0.05, -0.08), fontsize=10)

    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)
    ax.set_xlim(-0.75, 0.75)
    ax.set_ylim(-0.75, 0.75)
    ax.set_aspect('equal')
    ax.set_xlabel('$T_3$', fontsize=10)
    ax.set_ylabel('$T_8$', fontsize=10)
    ax.grid(True, alpha=0.2)


def create_domain_diagram(ax):
    """Panel 2: Color domains as sectors."""

    # Draw domain sectors
    theta_offset = np.pi/6  # Rotate to align with weights
    r = 0.65

    for i, (name, color) in enumerate([('R', COLORS['R']), ('G', COLORS['G']), ('B', COLORS['B'])]):
        start_angle = theta_offset + i * 2*np.pi/3
        angles = np.linspace(start_angle, start_angle + 2*np.pi/3, 50)
        x = np.concatenate([[0], r * np.cos(angles), [0]])
        y = np.concatenate([[0], r * np.sin(angles), [0]])
        ax.fill(x, y, color=color, alpha=0.3, edgecolor=color, linewidth=2)

        # Label domain
        mid_angle = start_angle + np.pi/3
        ax.annotate(f'$D_{name}$', (0.4*np.cos(mid_angle), 0.4*np.sin(mid_angle)),
                   fontsize=12, ha='center', va='center', fontweight='bold', color=color)

    # Draw weight triangle overlay
    triangle = np.array([WEIGHTS_2D['R'], WEIGHTS_2D['G'], WEIGHTS_2D['B'], WEIGHTS_2D['R']])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=2, alpha=0.7)

    # Mark face centers (depression zones)
    for name in ['R', 'G', 'B']:
        w = WEIGHTS_2D[name]
        # Face center in 2D (average of other two)
        other_weights = [WEIGHTS_2D[c] for c in ['R', 'G', 'B'] if c != name]
        face_2d = np.mean(other_weights, axis=0)
        ax.scatter(*face_2d, c=COLORS[name], s=80, marker='s', alpha=0.6,
                  edgecolors='black', linewidths=1)

    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)
    ax.scatter(0, 0, c='black', s=50, zorder=10)
    ax.set_xlim(-0.75, 0.75)
    ax.set_ylim(-0.75, 0.75)
    ax.set_aspect('equal')
    ax.set_xlabel('$T_3$', fontsize=10)
    ax.set_ylabel('$T_8$', fontsize=10)
    ax.grid(True, alpha=0.2)


def create_duality_diagram(ax):
    """Panel 3: Vertex-face duality with connecting arrows."""

    # Draw triangle
    triangle = np.array([WEIGHTS_2D['R'], WEIGHTS_2D['G'], WEIGHTS_2D['B'], WEIGHTS_2D['R']])
    ax.plot(triangle[:, 0], triangle[:, 1], 'k-', linewidth=1.5)
    ax.fill(triangle[:-1, 0], triangle[:-1, 1], alpha=0.05, color='gray')

    for name in ['R', 'G', 'B']:
        w = WEIGHTS_2D[name]

        # Vertex (source)
        ax.scatter(*w, c=COLORS[name], s=180, zorder=5, edgecolors='black', linewidths=1.5)

        # Face center (depression) - opposite to vertex
        other_weights = [WEIGHTS_2D[c] for c in ['R', 'G', 'B'] if c != name]
        face_2d = np.mean(other_weights, axis=0)
        ax.scatter(*face_2d, c=COLORS[name], s=100, marker='s', alpha=0.5,
                  edgecolors='black', linewidths=1.5, zorder=4)

        # Duality arrow (through center)
        ax.annotate('', xy=(face_2d[0]*0.85, face_2d[1]*0.85),
                   xytext=(w[0]*0.7, w[1]*0.7),
                   arrowprops=dict(arrowstyle='->', color=COLORS[name],
                                  lw=2, ls='--', alpha=0.7))

        # Labels
        offset = 0.12
        y_offset = -0.12 if name == 'B' else 0.06  # Move B label down
        ax.annotate(f'$x_{name}$', (w[0]+offset*np.sign(w[0]) if name != 'B' else w[0], w[1]+y_offset),
                   fontsize=10, fontweight='bold', color=COLORS[name])
        e_x_offset = 0.02 if name == 'G' else -0.08  # Move E_G to the right
        ax.annotate(f'$E_{name}$', (face_2d[0]+e_x_offset, face_2d[1]-0.08),
                   fontsize=9, color='gray')

    # Center point
    ax.scatter(0, 0, c='black', s=60, zorder=10)
    ax.annotate('O\n(balance)', (0.015, -0.17), fontsize=8, ha='left')

    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)
    ax.set_xlim(-0.75, 0.75)
    ax.set_ylim(-0.75, 0.75)
    ax.set_aspect('equal')
    ax.set_xlabel('$T_3$', fontsize=10)
    ax.set_ylabel('$T_8$', fontsize=10)
    ax.grid(True, alpha=0.2)


def create_pressure_heatmap(ax):
    """Panel 4: Total pressure heatmap in z=0 slice."""

    x = np.linspace(-1.3, 1.3, 100)
    y = np.linspace(-1.3, 1.3, 100)
    X, Y = np.meshgrid(x, y)

    P_total = np.zeros_like(X)
    for i in range(len(x)):
        for j in range(len(y)):
            pt = np.array([X[i, j], Y[i, j], 0])
            P_total[i, j] = sum(pressure(pt, VERTICES[c]) for c in ['R', 'G', 'B'])

    im = ax.contourf(X, Y, P_total, levels=25, cmap='hot')
    plt.colorbar(im, ax=ax, label='$\\Sigma P_c(x)$', shrink=0.8)

    # Mark vertices
    for name in ['R', 'G', 'B']:
        v = VERTICES[name]
        ax.scatter(v[0], v[1], c='white', s=120, edgecolors='black', linewidths=2, zorder=5)
        ax.annotate(f'$x_{name}$', (v[0]+0.12, v[1]+0.05), color='black', fontsize=10,
                   fontweight='bold')

    ax.scatter(0, 0, c='cyan', s=80, marker='x', linewidths=3, zorder=5)
    ax.set_xlabel('$x$', fontsize=10)
    ax.set_ylabel('$y$', fontsize=10)
    ax.set_aspect('equal')


def create_depression_heatmap(ax):
    """Panel 5: Depression ratio heatmap for red."""

    x = np.linspace(-1.3, 1.3, 100)
    y = np.linspace(-1.3, 1.3, 100)
    X, Y = np.meshgrid(x, y)

    D_R = np.zeros_like(X)
    for i in range(len(x)):
        for j in range(len(y)):
            pt = np.array([X[i, j], Y[i, j], 0])
            D_R[i, j] = depression_ratio(pt, 'R')

    # Clip for visualization
    D_R = np.clip(D_R, 0, 8)

    im = ax.contourf(X, Y, D_R, levels=25, cmap='coolwarm')
    plt.colorbar(im, ax=ax, label='$D_R(x)$', shrink=0.8)

    # Mark vertex R and its opposite face center
    v_R = VERTICES['R']
    f_R = get_face_center('R')

    ax.scatter(v_R[0], v_R[1], c='red', s=150, edgecolors='white', linewidths=2, zorder=5)
    ax.annotate('$x_R$\n($D_R$→0)', (v_R[0]+0.12, v_R[1]), color='black', fontsize=9,
               fontweight='bold')

    ax.scatter(f_R[0], f_R[1], c='blue', s=150, marker='s', edgecolors='white',
              linewidths=2, zorder=5)
    ax.annotate('$E_R$\n($D_R$ max)', (f_R[0]+0.12, f_R[1]-0.1), color='black', fontsize=9)

    ax.scatter(0, 0, c='cyan', s=80, marker='x', linewidths=3, zorder=5)
    ax.annotate('$D_R=2$', (0.1, 0.1), fontsize=9)

    ax.set_xlabel('$x$', fontsize=10)
    ax.set_ylabel('$y$', fontsize=10)
    ax.set_aspect('equal')


def create_boundary_diagram(ax):
    """Panel 6: Domain boundaries with SU(3) root vectors."""

    # Draw domain sectors (background)
    theta_offset = np.pi/6
    r = 0.65

    for i, (name, color) in enumerate([('R', COLORS['R']), ('G', COLORS['G']), ('B', COLORS['B'])]):
        start_angle = theta_offset + i * 2*np.pi/3
        angles = np.linspace(start_angle, start_angle + 2*np.pi/3, 50)
        x = np.concatenate([[0], r * np.cos(angles), [0]])
        y = np.concatenate([[0], r * np.sin(angles), [0]])
        ax.fill(x, y, color=color, alpha=0.15)

    # Draw boundary lines (perpendicular to roots)
    boundary_colors = {'RG': '#9400D3', 'GB': '#FF8C00', 'BR': '#00CED1'}

    for root_name, root in ROOTS.items():
        # Line perpendicular to root
        line_dir = np.array([-root[1], root[0]])
        line_dir = line_dir / np.linalg.norm(line_dir)

        t = np.linspace(-0.7, 0.7, 100)
        line_x = t * line_dir[0]
        line_y = t * line_dir[1]

        ax.plot(line_x, line_y, '--', color=boundary_colors[root_name],
               linewidth=2.5, label=f'$\\partial D \\perp \\alpha_{{{root_name}}}$')

    # Draw root vectors as arrows
    for root_name, root in ROOTS.items():
        c1, c2 = root_name[0], root_name[1]
        midpoint = (WEIGHTS_2D[c1] + WEIGHTS_2D[c2]) / 2
        scale = 0.15
        ax.annotate('', xy=midpoint + scale*root, xytext=midpoint,
                   arrowprops=dict(arrowstyle='->', color='black', lw=2.5))
        ax.text(midpoint[0] + 0.18*root[0], midpoint[1] + 0.18*root[1],
               f'$\\alpha_{{{root_name}}}$', fontsize=10, fontweight='bold')

    # Mark weights
    for name, w in WEIGHTS_2D.items():
        ax.scatter(*w, c=COLORS[name], s=150, zorder=5, edgecolors='black', linewidths=1.5)

    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.2)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.2)
    ax.scatter(0, 0, c='black', s=50, zorder=10, marker='x')
    ax.set_xlim(-0.75, 0.75)
    ax.set_ylim(-0.75, 0.75)
    ax.set_aspect('equal')
    ax.set_xlabel('$T_3$', fontsize=10)
    ax.set_ylabel('$T_8$', fontsize=10)
    ax.legend(fontsize=8, loc='lower right')
    ax.grid(True, alpha=0.2)


# =============================================================================
# MAIN FIGURE GENERATION
# =============================================================================

def create_figure():
    """Create comprehensive 6-panel visualization."""

    fig = plt.figure(figsize=(16, 11))
    fig.suptitle('Definition 0.1.4: Color Field Domains\nVertex-Face Duality and SU(3) Structure',
                 fontsize=14, fontweight='bold', y=0.98)

    # Panel 1: Vertex Coloring (Weight Diagram Style)
    ax1 = fig.add_subplot(2, 3, 1)
    create_vertex_diagram(ax1)
    ax1.set_title('(a) Vertex Coloring\n(Color Sources)', fontsize=11)

    # Panel 2: Face Coloring (Domain Representation)
    ax2 = fig.add_subplot(2, 3, 2)
    create_domain_diagram(ax2)
    ax2.set_title('(b) Color Domains D_c\n(Voronoi Tessellation)', fontsize=11)

    # Panel 3: Vertex-Face Duality
    ax3 = fig.add_subplot(2, 3, 3)
    create_duality_diagram(ax3)
    ax3.set_title('(c) Vertex-Face Duality\n(Source ↔ Depression)', fontsize=11)

    # Panel 4: Pressure Heatmap
    ax4 = fig.add_subplot(2, 3, 4)
    create_pressure_heatmap(ax4)
    ax4.set_title('(d) Pressure Distribution\n(z=0 slice)', fontsize=11)

    # Panel 5: Depression Ratio Heatmap
    ax5 = fig.add_subplot(2, 3, 5)
    create_depression_heatmap(ax5)
    ax5.set_title('(e) Depression Ratio D_R(x)\n(Red suppression zone)', fontsize=11)

    # Panel 6: Domain Boundaries
    ax6 = fig.add_subplot(2, 3, 6)
    create_boundary_diagram(ax6)
    ax6.set_title('(f) Domain Boundaries\n(SU(3) Root Perpendicularity)', fontsize=11)

    plt.tight_layout(rect=[0, 0.02, 1, 0.95])

    # Get script directory for output
    script_dir = os.path.dirname(os.path.abspath(__file__))
    figures_dir = os.path.dirname(script_dir)

    # Save as both PDF and PNG
    pdf_path = os.path.join(figures_dir, 'fig_definition_0_1_4_visualization.pdf')
    png_path = os.path.join(figures_dir, 'fig_definition_0_1_4_visualization.png')

    plt.savefig(pdf_path, dpi=300, bbox_inches='tight', facecolor='white')
    plt.savefig(png_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()

    print(f"Figure saved:")
    print(f"  PDF: {pdf_path}")
    print(f"  PNG: {png_path}")


if __name__ == "__main__":
    create_figure()
