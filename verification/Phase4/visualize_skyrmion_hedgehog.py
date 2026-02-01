#!/usr/bin/env python3
"""
3D Visualization: Skyrmion (Baryon) as Hedgehog in Stella Octangula
====================================================================

Shows the hedgehog ansatz for a skyrmion (baryon) within the stella octangula.

The hedgehog ansatz (Theorem 4.1.1):
- Isospin direction follows spatial direction: n̂(x) = r̂ = x/|x|
- Profile function f(r): f(0) = π (max twist), f(∞) = 0 (vacuum)
- U(x) = exp(i f(r) r̂ · τ)
- Topological charge Q = 1 for a single baryon

In CG terms:
- Isospin direction from amplitude differences: n̂ ∝ (a_R - a_G, a_G - a_B, a_B - a_R)
- One color maximally dominant at center → baryon
- Matter stability from topological protection (Q cannot change continuously)

Reference:
- Theorem 4.1.1 (Existence of Solitons) §3.4.2
- Definition 0.1.1 (Stella Octangula Boundary Topology)
"""

import numpy as np
import plotly.graph_objects as go
from skimage import measure

# =============================================================================
# CONSTANTS FOR CHIRAL FIELD (Theorem 0.2.1)
# =============================================================================

EPSILON = 0.05  # Regularization for pressure function
A0 = 1.0        # Field amplitude

# Color field phases
PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

EXP_PHASES = {
    'R': np.exp(1j * PHASES['R']),
    'G': np.exp(1j * PHASES['G']),
    'B': np.exp(1j * PHASES['B']),
}

# Vertex labels per Definition 0.1.1
T_PLUS_LABELS = ['R', 'G', 'B', 'W']
T_MINUS_LABELS = ['R̄', 'Ḡ', 'B̄', 'W̄']

def create_tetrahedron_vertices(scale=1.0):
    """Create vertices of T₊ tetrahedron per Definition 0.1.1."""
    vertices = np.array([
        [1, 1, 1],      # R (Red)
        [1, -1, -1],    # G (Green)
        [-1, 1, -1],    # B (Blue)
        [-1, -1, 1]     # W (White/singlet)
    ]) * scale / np.sqrt(3)
    return vertices

def profile_function(r, r0=0.8):
    """
    Skyrmion profile function f(r).
    f(0) = π, f(∞) = 0
    Using a standard ansatz: f(r) = π * (1 - tanh(r/r0)) / (1 + tanh(r/r0))
    Simplified: f(r) = 2 * arctan(r0/r) for r > 0
    """
    # Avoid division by zero
    r_safe = np.maximum(r, 1e-10)
    # Standard skyrmion profile
    f = 2 * np.arctan(r0 / r_safe)
    return f


# =============================================================================
# CHIRAL FIELD FUNCTIONS (Theorem 0.2.1)
# =============================================================================

def pressure_function_grid(X, Y, Z, x_c, epsilon=EPSILON):
    """Vectorized pressure function for grids."""
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field_grid(X, Y, Z, vertices, a0=A0, epsilon=EPSILON):
    """Vectorized total chiral field χ_total = Σ_c a₀ P_c exp(iφ_c)."""
    total = np.zeros_like(X, dtype=complex)
    for c in ['R', 'G', 'B']:
        idx = {'R': 0, 'G': 1, 'B': 2}[c]
        P_c = pressure_function_grid(X, Y, Z, vertices[idx], epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def compute_rgb_colors(X, Y, Z, vertices, a0=A0, epsilon=EPSILON):
    """Compute RGB colors based on which field dominates at each point."""
    mags = {}
    for c in ['R', 'G', 'B']:
        idx = {'R': 0, 'G': 1, 'B': 2}[c]
        P_c = pressure_function_grid(X, Y, Z, vertices[idx], epsilon)
        mags[c] = a0 * P_c

    # Local normalization
    local_max = np.maximum(np.maximum(mags['R'], mags['G']), mags['B'])
    local_max = np.maximum(local_max, 1e-10)

    return mags['R'] / local_max, mags['G'] / local_max, mags['B'] / local_max


def rotation_matrix_axis_angle(axis, angle):
    """Rotation matrix for rotation around axis by angle (radians)."""
    axis = axis / np.linalg.norm(axis)
    K = np.array([
        [0, -axis[2], axis[1]],
        [axis[2], 0, -axis[0]],
        [-axis[1], axis[0], 0]
    ])
    return np.eye(3) + np.sin(angle) * K + (1 - np.cos(angle)) * (K @ K)


def create_isosurface_trace(mag_3d, r_frac, g_frac, b_frac, x_iso, y_iso, z_iso,
                            level, opacity, name, rotation_angle=0.0):
    """Create a Plotly mesh trace for an isosurface with RGB vertex colors."""
    try:
        verts, faces, _, _ = measure.marching_cubes(mag_3d, level=level)

        # Scale vertices to real coordinates
        n_iso = len(x_iso)
        verts_scaled = np.zeros_like(verts)
        verts_scaled[:, 0] = x_iso[0] + verts[:, 0] * (x_iso[-1] - x_iso[0]) / (n_iso - 1)
        verts_scaled[:, 1] = y_iso[0] + verts[:, 1] * (y_iso[-1] - y_iso[0]) / (n_iso - 1)
        verts_scaled[:, 2] = z_iso[0] + verts[:, 2] * (z_iso[-1] - z_iso[0]) / (n_iso - 1)

        # Apply rotation around (1,1,1) axis to align with tetrahedra edges
        if rotation_angle != 0.0:
            R_mat = rotation_matrix_axis_angle(np.array([1, 1, 1]), rotation_angle)
            verts_scaled = np.array([R_mat @ v for v in verts_scaled])

        # Interpolate RGB at vertex positions
        from scipy.interpolate import RegularGridInterpolator

        r_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), r_frac,
                                           method='linear', bounds_error=False, fill_value=0.33)
        g_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), g_frac,
                                           method='linear', bounds_error=False, fill_value=0.33)
        b_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), b_frac,
                                           method='linear', bounds_error=False, fill_value=0.33)

        r_vals = r_interp(verts_scaled)
        g_vals = g_interp(verts_scaled)
        b_vals = b_interp(verts_scaled)

        # Convert to RGB color strings
        r_255 = np.clip(r_vals * 255, 0, 255).astype(int)
        g_255 = np.clip(g_vals * 255, 0, 255).astype(int)
        b_255 = np.clip(b_vals * 255, 0, 255).astype(int)

        vertex_colors = [f'rgb({r},{g},{b})' for r, g, b in zip(r_255, g_255, b_255)]

        return go.Mesh3d(
            x=verts_scaled[:, 0],
            y=verts_scaled[:, 1],
            z=verts_scaled[:, 2],
            i=faces[:, 0],
            j=faces[:, 1],
            k=faces[:, 2],
            vertexcolor=vertex_colors,
            opacity=opacity,
            name=name,
            showlegend=True
        )
    except ValueError:
        return None

def main():
    fig = go.Figure()

    scale = 2.0
    t_plus = create_tetrahedron_vertices(scale)
    t_minus = -t_plus  # Dual tetrahedron

    # =========================================================================
    # STELLA OCTANGULA - Two interpenetrating tetrahedra
    # =========================================================================

    faces = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]
    edges = [[0,1], [0,2], [0,3], [1,2], [1,3], [2,3]]

    # T₊ faces and edges (very translucent)
    for face in faces:
        v = t_plus[face]
        fig.add_trace(go.Mesh3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            i=[0], j=[1], k=[2],
            color='rgba(100, 149, 237, 0.05)',
            flatshading=True, showlegend=False, hoverinfo='skip',
        ))

    for edge in edges:
        v = t_plus[edge]
        fig.add_trace(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines', line=dict(color='cornflowerblue', width=3),
            showlegend=False, hoverinfo='skip',
        ))

    # T₋ faces and edges (very translucent)
    for face in faces:
        v = t_minus[face]
        fig.add_trace(go.Mesh3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            i=[0], j=[1], k=[2],
            color='rgba(255, 140, 0, 0.05)',
            flatshading=True, showlegend=False, hoverinfo='skip',
        ))

    for edge in edges:
        v = t_minus[edge]
        fig.add_trace(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines', line=dict(color='darkorange', width=3),
            showlegend=False, hoverinfo='skip',
        ))

    # Vertex labels
    vertex_colors_plus = ['red', 'green', 'blue', 'white']
    for i, (label, color) in enumerate(zip(T_PLUS_LABELS, vertex_colors_plus)):
        fig.add_trace(go.Scatter3d(
            x=[t_plus[i, 0]], y=[t_plus[i, 1]], z=[t_plus[i, 2]],
            mode='markers+text',
            marker=dict(size=10, color=color, line=dict(color='black', width=2)),
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
            marker=dict(size=10, color=color, line=dict(color='black', width=2)),
            text=[label], textposition='bottom center',
            textfont=dict(size=14, color='black', family='Arial Black'),
            showlegend=False,
            hovertemplate=f'T₋: {label}<extra></extra>',
        ))

    # =========================================================================
    # ISOSURFACES OF |χ_total| (Theorem 0.2.1)
    # Shows where the total chiral field has specific amplitude levels
    # The "tube" through center is the vortex core where |χ_total| → 0
    # =========================================================================

    extent = 1.0  # Larger extent to reach edges
    n_iso = 55

    x_iso = np.linspace(-extent, extent, n_iso)
    y_iso = np.linspace(-extent, extent, n_iso)
    z_iso = np.linspace(-extent, extent, n_iso)
    X3d, Y3d, Z3d = np.meshgrid(x_iso, y_iso, z_iso, indexing='ij')

    # Compute total chiral field magnitude using stella vertices
    mag_3d = np.abs(total_chiral_field_grid(X3d, Y3d, Z3d, t_plus))
    vmax = mag_3d.max()

    # Compute RGB colors based on field mixing
    r_frac, g_frac, b_frac = compute_rgb_colors(X3d, Y3d, Z3d, t_plus)

    # Add isosurfaces - lower levels extend further toward edges
    iso_configs = [
        (0.08 * vmax, 0.15, '8% |χ|'),   # Extends further
        (0.20 * vmax, 0.12, '20% |χ|'),
    ]

    for level, opacity, name in iso_configs:
        trace = create_isosurface_trace(
            mag_3d, r_frac, g_frac, b_frac,
            x_iso, y_iso, z_iso, level, opacity, name
        )
        if trace:
            fig.add_trace(trace)

    # =========================================================================
    # HEDGEHOG (SKYRMION) - Vectors pointing radially outward
    # Poles aligned with W-W̄ axis per Definition 0.1.1
    # =========================================================================

    # W axis direction (poles of the hedgehog)
    w_axis = np.array([-1, -1, 1]) / np.sqrt(3)  # W vertex direction

    # Perpendicular basis vectors for the equatorial plane
    # e1 and e2 span the plane perpendicular to w_axis
    e1 = np.array([1, -1, 0]) / np.sqrt(2)       # Perpendicular to w_axis
    e2 = np.cross(w_axis, e1)                     # Complete the basis

    # Create a spherical grid with poles at W and W̄
    n_theta, n_phi = 6, 10  # Fewer cones for clarity
    radii = [0.19, 0.51, 0.91]  # Slightly outside shell radii so cones are visible

    # Color scale: red (f=π at center) to blue (f=0 at edge)
    r0 = 0.6  # Profile function scale

    all_x, all_y, all_z = [], [], []
    all_u, all_v, all_w = [], [], []
    all_colors = []

    for r in radii:
        for i in range(n_theta):
            theta = np.pi * (i + 0.5) / n_theta  # Angle from W axis (avoid poles)
            for j in range(n_phi):
                phi = 2 * np.pi * j / n_phi  # Azimuthal angle around W axis

                # Position in rotated coordinates (W-axis aligned)
                # r̂ = sin(θ)cos(φ)e1 + sin(θ)sin(φ)e2 + cos(θ)w_axis
                pos = r * (np.sin(theta) * np.cos(phi) * e1 +
                          np.sin(theta) * np.sin(phi) * e2 +
                          np.cos(theta) * w_axis)

                x, y, z = pos

                # Hedgehog: vector points radially outward
                # Direction = r̂, magnitude proportional to sin(f(r))
                f_r = profile_function(r, r0)
                magnitude = 0.10  # Cones sitting on shell surfaces

                # Unit radial vector (same direction as position)
                r_hat = pos / r
                vec = magnitude * r_hat

                all_x.append(x)
                all_y.append(y)
                all_z.append(z)
                all_u.append(vec[0])
                all_v.append(vec[1])
                all_w.append(vec[2])
                all_colors.append(f_r / np.pi)

    # Add hedgehog vectors as cones
    fig.add_trace(go.Cone(
        x=all_x, y=all_y, z=all_z,
        u=all_u, v=all_v, w=all_w,
        colorscale='RdYlBu_r',  # Red (high f) to blue (low f)
        cmin=0, cmax=1,
        sizemode='absolute',
        sizeref=0.10,
        anchor='tail',
        showscale=True,
        colorbar=dict(
            title=dict(text='f(r)/π', font=dict(size=12)),
            tickvals=[0, 0.5, 1],
            ticktext=['0', 'π/2', 'π'],
            len=0.4, y=0.8,
        ),
        name='Hedgehog (n̂ = r̂)',
        hovertemplate='Isospin direction = radial<br>f(r)/π = %{u:.2f}<extra></extra>',
    ))

    # =========================================================================
    # SPHERICAL SHELLS to show f(r) profile throughout the volume
    # =========================================================================

    theta_shell = np.linspace(0, np.pi, 25)
    phi_shell = np.linspace(0, 2*np.pi, 35)
    THETA, PHI = np.meshgrid(theta_shell, phi_shell)

    # Three distinct shells: Red (center), Yellow (middle), Blue (outer)
    shell_configs = [
        (0.18, 'rgba(220, 50, 50, 0.4)', 'Inner (f≈π): Red'),
        (0.50, 'rgba(255, 210, 60, 0.2)', 'Middle (f≈π/2): Yellow'),
        (0.90, 'rgba(70, 140, 255, 0.1)', 'Outer (f→0): Blue'),
    ]

    for r_shell, color_str, name in shell_configs:
        X_shell = r_shell * np.sin(THETA) * np.cos(PHI)
        Y_shell = r_shell * np.sin(THETA) * np.sin(PHI)
        Z_shell = r_shell * np.cos(THETA)

        f_shell = profile_function(r_shell, r0)
        f_norm = f_shell / np.pi

        fig.add_trace(go.Surface(
            x=X_shell, y=Y_shell, z=Z_shell,
            colorscale=[[0, color_str], [1, color_str]],
            showscale=False,
            name=f'{name}',
            hovertemplate=f'r={r_shell:.2f}<br>f(r)/π ≈ {f_norm:.2f}<extra></extra>',
        ))

    # Center point (baryon location)
    fig.add_trace(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=15, color='red', symbol='diamond',
                    line=dict(color='darkred', width=2)),
        name='Baryon center (Q=1)',
        hovertemplate='Skyrmion center<br>f(0) = π<br>Topological charge Q = 1<extra></extra>',
    ))

    # =========================================================================
    # COLOR FIELD INDICATORS - Show which color dominates where
    # =========================================================================

    # Lines from center toward R, G, B vertices (showing color field directions)
    colors_rgb = ['red', 'green', 'blue']
    for i, (label, color) in enumerate(zip(['R', 'G', 'B'], colors_rgb)):
        # Direction toward color vertex
        direction = t_plus[i] / np.linalg.norm(t_plus[i])
        # Line from center partway toward vertex
        t_vals = np.linspace(0.15, 0.7, 10)
        x_line = t_vals * direction[0]
        y_line = t_vals * direction[1]
        z_line = t_vals * direction[2]

        fig.add_trace(go.Scatter3d(
            x=x_line, y=y_line, z=z_line,
            mode='lines',
            line=dict(color=color, width=6, dash='dot'),
            name=f'→ {label} (color field)',
            hovertemplate=f'Direction toward {label} vertex<br>Color field χ_{label} dominates here<extra></extra>',
        ))

    # =========================================================================
    # Layout
    # =========================================================================

    fig.update_layout(
        title=dict(
            text='Skyrmion (Baryon) as Hedgehog: n̂ = r̂, Q = 1',
            font=dict(size=14),
            x=0.5,
        ),
        scene=dict(
            xaxis=dict(title='', showticklabels=False, showgrid=False, zeroline=False,
                       showbackground=False),
            yaxis=dict(title='', showticklabels=False, showgrid=False, zeroline=False,
                       showbackground=False),
            zaxis=dict(title='', showticklabels=False, showgrid=False, zeroline=False,
                       showbackground=False),
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
                text='<b>Hedgehog Ansatz (Thm 4.1.1):</b><br>'
                     'n̂(x) = r̂ (isospin = radial)<br>'
                     'f(0) = π, f(∞) = 0<br>'
                     'Baryon = skyrmion with Q = 1',
                x=0.98, y=0.98,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=10),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=6,
                align='left', xanchor='right',
            ),
            dict(
                text='<b>Color fields:</b><br>'
                     'χ_R, χ_G, χ_B peak at vertices<br>'
                     'Amplitude differences → isospin<br>'
                     'Dotted lines show color directions',
                x=0.02, y=0.15,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=10),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=6,
                align='left',
            ),
        ],
    )

    # Save
    fig.write_html('plots/skyrmion_hedgehog.html')
    fig.write_image('plots/skyrmion_hedgehog.png', width=1200, height=900, scale=2)
    fig.write_image('plots/skyrmion_hedgehog.pdf', width=1200, height=900)

    print("Saved: plots/skyrmion_hedgehog.html (interactive)")
    print("Saved: plots/skyrmion_hedgehog.png")
    print("Saved: plots/skyrmion_hedgehog.pdf")

if __name__ == '__main__':
    main()
