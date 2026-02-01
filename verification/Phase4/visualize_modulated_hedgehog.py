#!/usr/bin/env python3
"""
3D Visualization: Modulated Hedgehog - Isosurface-Shaped Skyrmion
==================================================================

Shows how the hedgehog (skyrmion) profile is modulated by the chiral field
structure |χ_total|. Instead of perfect spheres, the f(r) shells follow
the isosurface contours - bulging toward R, G, B vertices where |χ_total|
is high, and pinching toward W where |χ_total| is low (vortex tubes).

This demonstrates the interaction between:
- Theorem 0.2.1: Total field superposition |χ_total|
- Theorem 4.1.1: Hedgehog ansatz for skyrmions

Reference:
- Definition 0.1.1 (Stella Octangula Boundary Topology)
"""

import numpy as np
import plotly.graph_objects as go

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05  # Regularization for pressure function
A0 = 1.0        # Field amplitude

# Color field phases
EXP_PHASES = {
    'R': np.exp(1j * 0.0),
    'G': np.exp(1j * 2 * np.pi / 3),
    'B': np.exp(1j * 4 * np.pi / 3),
}

# Vertex labels
T_PLUS_LABELS = ['R', 'G', 'B', 'W']
T_MINUS_LABELS = ['R̄', 'Ḡ', 'B̄', 'W̄']


def create_tetrahedron_vertices(scale=1.0):
    """Create vertices of T₊ tetrahedron per Definition 0.1.1."""
    vertices = np.array([
        [1, 1, 1],      # R
        [1, -1, -1],    # G
        [-1, 1, -1],    # B
        [-1, -1, 1]     # W
    ]) * scale / np.sqrt(3)
    return vertices


def pressure_function(x, y, z, vertex, epsilon=EPSILON):
    """Pressure function P_c(x) = 1/(|x - x_c|² + ε²)."""
    dist_sq = (x - vertex[0])**2 + (y - vertex[1])**2 + (z - vertex[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field_magnitude(x, y, z, vertices):
    """Compute |χ_total| at a point."""
    total = 0j
    for i, c in enumerate(['R', 'G', 'B']):
        P_c = pressure_function(x, y, z, vertices[i])
        total += A0 * P_c * EXP_PHASES[c]
    return np.abs(total)


def get_dominant_color(x, y, z, vertices):
    """Return RGB tuple based on which color field dominates."""
    pressures = []
    for i in range(3):
        pressures.append(pressure_function(x, y, z, vertices[i]))

    total = sum(pressures)
    if total < 1e-10:
        return (0.5, 0.5, 0.5)

    r = pressures[0] / total
    g = pressures[1] / total
    b = pressures[2] / total

    return (r, g, b)


def profile_function(r, r0=0.6):
    """Skyrmion profile f(r): f(0) = π, f(∞) = 0."""
    r_safe = np.maximum(r, 1e-10)
    return 2 * np.arctan(r0 / r_safe)


def create_modulated_shell(base_radius, vertices, n_theta=40, n_phi=60,
                           modulation_strength=0.5):
    """
    Create a shell that follows the |χ_total| isosurface shape.

    The shell radius is modulated by the local field magnitude:
    r(θ,φ) = base_radius * (1 + modulation * normalized_field_mag)
    """
    theta = np.linspace(0, np.pi, n_theta)
    phi = np.linspace(0, 2 * np.pi, n_phi)
    THETA, PHI = np.meshgrid(theta, phi)

    # Unit sphere coordinates
    x_unit = np.sin(THETA) * np.cos(PHI)
    y_unit = np.sin(THETA) * np.sin(PHI)
    z_unit = np.cos(THETA)

    # Sample field magnitude at unit sphere, then modulate radius
    X = np.zeros_like(THETA)
    Y = np.zeros_like(THETA)
    Z = np.zeros_like(THETA)
    colors = []

    # Compute field magnitudes for normalization
    mags = np.zeros_like(THETA)
    for i in range(n_phi):
        for j in range(n_theta):
            # Sample at base_radius to get local field structure
            x_sample = base_radius * x_unit[i, j]
            y_sample = base_radius * y_unit[i, j]
            z_sample = base_radius * z_unit[i, j]
            mags[i, j] = total_chiral_field_magnitude(x_sample, y_sample, z_sample, vertices)

    # Normalize magnitudes
    mag_min, mag_max = mags.min(), mags.max()
    if mag_max > mag_min:
        mags_norm = (mags - mag_min) / (mag_max - mag_min)
    else:
        mags_norm = np.ones_like(mags) * 0.5

    # Modulate radius: bulge where field is high, pinch where low
    for i in range(n_phi):
        row_colors = []
        for j in range(n_theta):
            # Radius modulation
            r_mod = base_radius * (1 + modulation_strength * (mags_norm[i, j] - 0.5))

            X[i, j] = r_mod * x_unit[i, j]
            Y[i, j] = r_mod * y_unit[i, j]
            Z[i, j] = r_mod * z_unit[i, j]

            # Get color based on dominant field
            rgb = get_dominant_color(X[i, j], Y[i, j], Z[i, j], vertices)
            row_colors.append(rgb)
        colors.append(row_colors)

    return X, Y, Z, colors, mags_norm


def main():
    fig = go.Figure()

    scale = 2.0
    t_plus = create_tetrahedron_vertices(scale)
    t_minus = -t_plus

    # =========================================================================
    # STELLA OCTANGULA WIREFRAME
    # =========================================================================

    edges = [[0,1], [0,2], [0,3], [1,2], [1,3], [2,3]]

    for edge in edges:
        v = t_plus[edge]
        fig.add_trace(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines', line=dict(color='orange', width=4),
            showlegend=False, hoverinfo='skip',
        ))

    for edge in edges:
        v = t_minus[edge]
        fig.add_trace(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines', line=dict(color='cornflowerblue', width=4),
            showlegend=False, hoverinfo='skip',
        ))

    # Vertex labels
    vertex_colors_plus = ['red', 'green', 'blue', 'white']
    for i, (label, color) in enumerate(zip(T_PLUS_LABELS, vertex_colors_plus)):
        fig.add_trace(go.Scatter3d(
            x=[t_plus[i, 0]], y=[t_plus[i, 1]], z=[t_plus[i, 2]],
            mode='markers+text',
            marker=dict(size=12, color=color, line=dict(color='black', width=2)),
            text=[label], textposition='top center',
            textfont=dict(size=14, color='black', family='Arial Black'),
            showlegend=False,
            hovertemplate=f'T₊: {label}<extra></extra>',
        ))

    vertex_colors_minus = ['darkred', 'darkgreen', 'darkblue', 'gray']
    for i, (label, color) in enumerate(zip(T_MINUS_LABELS, vertex_colors_minus)):
        fig.add_trace(go.Scatter3d(
            x=[t_minus[i, 0]], y=[t_minus[i, 1]], z=[t_minus[i, 2]],
            mode='markers+text',
            marker=dict(size=12, color=color, line=dict(color='black', width=2)),
            text=[label], textposition='bottom center',
            textfont=dict(size=14, color='black', family='Arial Black'),
            showlegend=False,
            hovertemplate=f'T₋: {label}<extra></extra>',
        ))

    # =========================================================================
    # MODULATED HEDGEHOG SHELLS
    # Shells that bulge toward R,G,B and pinch toward W
    # =========================================================================

    shell_configs = [
        (0.25, 0.6, 0.5, 'Inner shell (f≈π)'),    # base_radius, modulation, opacity
        (0.50, 0.5, 0.35, 'Middle shell (f≈π/2)'),
        (0.80, 0.4, 0.2, 'Outer shell (f→0)'),
    ]

    for base_r, mod_strength, opacity, name in shell_configs:
        X, Y, Z, colors, mags = create_modulated_shell(
            base_r, t_plus,
            n_theta=35, n_phi=50,
            modulation_strength=mod_strength
        )

        # Convert colors to plotly format
        # Use field magnitude for colorscale
        fig.add_trace(go.Surface(
            x=X, y=Y, z=Z,
            surfacecolor=mags,
            colorscale='RdYlBu_r',
            cmin=0, cmax=1,
            opacity=opacity,
            showscale=False,
            name=name,
            hovertemplate=f'{name}<br>|χ| modulation shown<extra></extra>',
        ))

    # =========================================================================
    # HEDGEHOG CONES - pointing radially outward
    # =========================================================================

    # W axis for cone distribution poles
    w_axis = np.array([-1, -1, 1]) / np.sqrt(3)
    e1 = np.array([1, -1, 0]) / np.sqrt(2)
    e2 = np.cross(w_axis, e1)

    n_theta, n_phi = 6, 10
    cone_radius = 0.55  # Place cones on middle shell

    all_x, all_y, all_z = [], [], []
    all_u, all_v, all_w = [], [], []
    all_colors = []

    r0 = 0.6

    for i in range(n_theta):
        theta = np.pi * (i + 0.5) / n_theta
        for j in range(n_phi):
            phi = 2 * np.pi * j / n_phi

            # Position with W-axis poles
            pos = cone_radius * (np.sin(theta) * np.cos(phi) * e1 +
                                 np.sin(theta) * np.sin(phi) * e2 +
                                 np.cos(theta) * w_axis)

            # Modulate position by field magnitude
            mag = total_chiral_field_magnitude(pos[0], pos[1], pos[2], t_plus)
            # Normalize roughly
            mag_norm = min(mag / 500, 1.0)

            # Stretch position toward high-field regions
            r_actual = cone_radius * (1 + 0.4 * (mag_norm - 0.5))
            pos_mod = pos * (r_actual / cone_radius)

            x, y, z = pos_mod

            # Hedgehog: radially outward
            f_r = profile_function(np.linalg.norm(pos_mod), r0)
            magnitude = 0.08

            r_hat = pos_mod / np.linalg.norm(pos_mod)
            vec = magnitude * r_hat

            all_x.append(x)
            all_y.append(y)
            all_z.append(z)
            all_u.append(vec[0])
            all_v.append(vec[1])
            all_w.append(vec[2])
            all_colors.append(f_r / np.pi)

    fig.add_trace(go.Cone(
        x=all_x, y=all_y, z=all_z,
        u=all_u, v=all_v, w=all_w,
        colorscale='RdYlBu_r',
        cmin=0, cmax=1,
        sizemode='absolute',
        sizeref=0.08,
        anchor='tail',
        showscale=True,
        colorbar=dict(
            title=dict(text='f(r)/π', font=dict(size=12)),
            tickvals=[0, 0.5, 1],
            ticktext=['0', 'π/2', 'π'],
            len=0.4, y=0.8,
        ),
        name='Hedgehog (n̂ = r̂)',
    ))

    # =========================================================================
    # CENTER MARKER
    # =========================================================================

    fig.add_trace(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=15, color='red', symbol='diamond',
                    line=dict(color='darkred', width=2)),
        name='Baryon center (Q=1)',
    ))

    # =========================================================================
    # LAYOUT
    # =========================================================================

    fig.update_layout(
        title=dict(
            text='Modulated Hedgehog: f(r) Shells Follow |χ_total| Contours',
            font=dict(size=14),
            x=0.5,
        ),
        scene=dict(
            xaxis=dict(title='', showticklabels=False, showgrid=False,
                       zeroline=False, showbackground=False),
            yaxis=dict(title='', showticklabels=False, showgrid=False,
                       zeroline=False, showbackground=False),
            zaxis=dict(title='', showticklabels=False, showgrid=False,
                       zeroline=False, showbackground=False),
            camera=dict(eye=dict(x=1.6, y=1.6, z=1.2)),
            aspectmode='cube',
            bgcolor='rgba(255,255,255,1)',
        ),
        legend=dict(
            x=0.02, y=0.98,
            bgcolor='rgba(255,255,255,0.9)',
            bordercolor='gray', borderwidth=1,
            font=dict(size=10),
        ),
        margin=dict(l=0, r=0, t=50, b=0),
        annotations=[
            dict(
                text='<b>Modulated Hedgehog:</b><br>'
                     'Shells bulge toward R,G,B (high |χ|)<br>'
                     'Shells pinch toward W (low |χ|, vortex)<br>'
                     'Color = local field magnitude',
                x=0.98, y=0.98,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=10),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=6,
                align='left', xanchor='right',
            ),
        ],
    )

    # Save
    fig.write_html('plots/modulated_hedgehog.html')
    fig.write_image('plots/modulated_hedgehog.png', width=1200, height=900, scale=2)
    fig.write_image('plots/modulated_hedgehog.pdf', width=1200, height=900)

    print("Saved: plots/modulated_hedgehog.html (interactive)")
    print("Saved: plots/modulated_hedgehog.png")
    print("Saved: plots/modulated_hedgehog.pdf")


if __name__ == '__main__':
    main()
