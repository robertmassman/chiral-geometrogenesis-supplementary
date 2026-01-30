#!/usr/bin/env python3
"""
Interactive 3D Visualization for Proposition 0.0.17k4: Z3 Phase Structure

Visualizes the phase gradients described in Prop 0.0.17k4:
1. The three color fields (R, G, B) with RGB mixing on isosurfaces
2. The W-face as the color singlet (where sum of phases = 0)
3. Phase gradient field showing direction of field increase
4. The inter-tetrahedral overlap region

Based on the working theorem_0_2_1_interactive_3d.py visualization.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import plotly.graph_objects as go
from skimage import measure
from scipy.interpolate import RegularGridInterpolator

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05
A0 = 1.0

# Z3 phases: 0, 2π/3, 4π/3 (120° separation)
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

# Stella octangula vertices (two interpenetrating tetrahedra)
# T+ tetrahedron
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),  # White vertex (color singlet)
}

# T- tetrahedron (dual)
VERTICES_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}


# =============================================================================
# FIELD FUNCTIONS (matching theorem_0_2_1)
# =============================================================================

def pressure_function_grid(X, Y, Z, x_c, epsilon=EPSILON):
    """Vectorized pressure function for grids."""
    dist_sq = (X - x_c[0])**2 + (Y - x_c[1])**2 + (Z - x_c[2])**2
    return 1.0 / (dist_sq + epsilon**2)


def total_chiral_field_grid(X, Y, Z, a0=A0, epsilon=EPSILON):
    """Vectorized total chiral field for grids."""
    total = np.zeros_like(X, dtype=complex)
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        total += a0 * P_c * EXP_PHASES[c]
    return total


def individual_field_magnitudes(X, Y, Z, a0=A0, epsilon=EPSILON):
    """Compute magnitude of each color field separately."""
    mags = {}
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        mags[c] = a0 * P_c
    return mags


def compute_rgb_colors(X, Y, Z, a0=A0, epsilon=EPSILON):
    """
    Compute RGB colors based on field strengths at each point.
    Uses local normalization so colors are vivid everywhere.
    """
    mags = individual_field_magnitudes(X, Y, Z, a0, epsilon)

    r_mag = mags['R']
    g_mag = mags['G']
    b_mag = mags['B']

    # Local normalization
    local_max = np.maximum(np.maximum(r_mag, g_mag), b_mag)
    local_max = np.maximum(local_max, 1e-10)

    r_frac = r_mag / local_max
    g_frac = g_mag / local_max
    b_frac = b_mag / local_max

    return r_frac, g_frac, b_frac


def compute_phase_gradient_field(X, Y, Z, a0=A0, epsilon=EPSILON):
    """
    Compute the gradient of the total field's phase.
    This is what vector excitations couple to (phase-gradient mass mechanism).
    Returns gradient components (grad_x, grad_y, grad_z) and magnitude.
    """
    chi_total = total_chiral_field_grid(X, Y, Z, a0, epsilon)
    phase = np.angle(chi_total)

    # Grid spacing
    if X.ndim == 3:
        hx = X[1, 0, 0] - X[0, 0, 0] if X.shape[0] > 1 else 0.01
        hy = Y[0, 1, 0] - Y[0, 0, 0] if Y.shape[1] > 1 else 0.01
        hz = Z[0, 0, 1] - Z[0, 0, 0] if Z.shape[2] > 1 else 0.01
    else:
        hx = hy = hz = 0.01

    # Numerical gradient with phase unwrapping consideration
    grad_x = np.gradient(phase, hx, axis=0)
    grad_y = np.gradient(phase, hy, axis=1)
    grad_z = np.gradient(phase, hz, axis=2)

    # Magnitude of gradient
    grad_mag = np.sqrt(grad_x**2 + grad_y**2 + grad_z**2)

    return grad_x, grad_y, grad_z, grad_mag


# =============================================================================
# VISUALIZATION FUNCTIONS
# =============================================================================

def create_stella_traces():
    """Create Plotly traces for stella octangula wireframe."""
    traces = []

    # T+ tetrahedron (blue)
    t_plus = [VERTICES_PLUS[k] for k in ['R', 'G', 'B', 'W']]
    edges_plus = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

    for i, j in edges_plus:
        traces.append(go.Scatter3d(
            x=[t_plus[i][0], t_plus[j][0]],
            y=[t_plus[i][1], t_plus[j][1]],
            z=[t_plus[i][2], t_plus[j][2]],
            mode='lines',
            line=dict(color='blue', width=3),
            showlegend=False,
            hoverinfo='skip'
        ))

    # T- tetrahedron (red/purple)
    t_minus = [VERTICES_MINUS[k] for k in ['R_bar', 'G_bar', 'B_bar', 'W_bar']]
    edges_minus = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

    for i, j in edges_minus:
        traces.append(go.Scatter3d(
            x=[t_minus[i][0], t_minus[j][0]],
            y=[t_minus[i][1], t_minus[j][1]],
            z=[t_minus[i][2], t_minus[j][2]],
            mode='lines',
            line=dict(color='red', width=3),
            showlegend=False,
            hoverinfo='skip'
        ))

    # Color vertices (small markers)
    colors_map = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'gray'}
    for name, v in VERTICES_PLUS.items():
        traces.append(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers',
            marker=dict(size=8, color=colors_map[name],
                       line=dict(color='black', width=1)),
            name=f'{name} vertex',
            hoverinfo='name'
        ))

    # Origin marker
    traces.append(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=10, color='white',
                   line=dict(color='black', width=2)),
        name='Origin (χ=0)',
        hoverinfo='name'
    ))

    return traces


def create_rgb_isosurface_trace(mag_3d, r_frac, g_frac, b_frac, x_iso, y_iso, z_iso, level, opacity, name):
    """Create a Plotly mesh trace for an isosurface with RGB vertex colors."""
    try:
        verts, faces, _, _ = measure.marching_cubes(mag_3d, level=level)

        # Scale vertices to real coordinates
        n_iso = len(x_iso)
        verts_scaled = np.zeros_like(verts)
        verts_scaled[:, 0] = x_iso[0] + verts[:, 0] * (x_iso[-1] - x_iso[0]) / (n_iso - 1)
        verts_scaled[:, 1] = y_iso[0] + verts[:, 1] * (y_iso[-1] - y_iso[0]) / (n_iso - 1)
        verts_scaled[:, 2] = z_iso[0] + verts[:, 2] * (z_iso[-1] - z_iso[0]) / (n_iso - 1)

        # Interpolate RGB fractions at vertex positions
        r_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), r_frac,
                                           method='linear', bounds_error=False, fill_value=0.33)
        g_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), g_frac,
                                           method='linear', bounds_error=False, fill_value=0.33)
        b_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), b_frac,
                                           method='linear', bounds_error=False, fill_value=0.33)

        r_vals = r_interp(verts_scaled)
        g_vals = g_interp(verts_scaled)
        b_vals = b_interp(verts_scaled)

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


def create_w_face_surface():
    """
    Create a surface for the W-face (color singlet face).
    This is where sum of phases = 0 (destructive interference).
    """
    # W-face vertices are R, G, B (the face opposite to W vertex)
    verts = np.array([VERTICES_PLUS['R'], VERTICES_PLUS['G'], VERTICES_PLUS['B']])

    return go.Mesh3d(
        x=verts[:, 0],
        y=verts[:, 1],
        z=verts[:, 2],
        i=[0],
        j=[1],
        k=[2],
        color='rgba(255, 255, 255, 0.4)',
        name='W-face (color singlet)',
        showlegend=True,
        hoverinfo='name'
    )


def create_gradient_streamlines(X3d, Y3d, Z3d, grad_x, grad_y, grad_z, n_lines=12):
    """
    Create streamline traces showing the phase gradient field.
    Streamlines start from points distributed around the stella.
    """
    traces = []

    # Create interpolators for gradient components
    x_iso = X3d[:, 0, 0]
    y_iso = Y3d[0, :, 0]
    z_iso = Z3d[0, 0, :]

    gx_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), grad_x,
                                        method='linear', bounds_error=False, fill_value=0)
    gy_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), grad_y,
                                        method='linear', bounds_error=False, fill_value=0)
    gz_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), grad_z,
                                        method='linear', bounds_error=False, fill_value=0)

    # Starting points: distributed on sphere around origin
    np.random.seed(42)
    r_start = 0.35
    theta = np.random.uniform(0, 2*np.pi, n_lines)
    phi = np.random.uniform(0, np.pi, n_lines)

    start_points = np.column_stack([
        r_start * np.sin(phi) * np.cos(theta),
        r_start * np.sin(phi) * np.sin(theta),
        r_start * np.cos(phi)
    ])

    # Integrate streamlines
    dt = 0.02
    n_steps = 30

    for i, start in enumerate(start_points):
        line_x, line_y, line_z = [start[0]], [start[1]], [start[2]]
        pos = start.copy()

        for _ in range(n_steps):
            try:
                gx = gx_interp(pos)[0] if gx_interp(pos).size == 1 else gx_interp(pos)
                gy = gy_interp(pos)[0] if gy_interp(pos).size == 1 else gy_interp(pos)
                gz = gz_interp(pos)[0] if gz_interp(pos).size == 1 else gz_interp(pos)
            except:
                break

            # Normalize and step
            mag = np.sqrt(gx**2 + gy**2 + gz**2)
            if mag < 1e-6:
                break

            pos = pos + dt * np.array([gx, gy, gz]) / mag

            # Check bounds
            if np.any(np.abs(pos) > 0.65):
                break

            line_x.append(pos[0])
            line_y.append(pos[1])
            line_z.append(pos[2])

        if len(line_x) > 2:
            # Color based on direction (roughly)
            traces.append(go.Scatter3d(
                x=line_x, y=line_y, z=line_z,
                mode='lines',
                line=dict(color='cyan', width=2),
                showlegend=(i == 0),
                name='Phase gradient flow' if i == 0 else None,
                hoverinfo='skip'
            ))

    return traces


def create_gradient_cones(X3d, Y3d, Z3d, grad_x, grad_y, grad_z, spacing=6):
    """
    Create cone glyphs showing the phase gradient direction.
    """
    # Subsample the grid
    x_sub = X3d[::spacing, ::spacing, ::spacing]
    y_sub = Y3d[::spacing, ::spacing, ::spacing]
    z_sub = Z3d[::spacing, ::spacing, ::spacing]
    gx_sub = grad_x[::spacing, ::spacing, ::spacing]
    gy_sub = grad_y[::spacing, ::spacing, ::spacing]
    gz_sub = grad_z[::spacing, ::spacing, ::spacing]

    # Flatten
    x_flat = x_sub.flatten()
    y_flat = y_sub.flatten()
    z_flat = z_sub.flatten()
    gx_flat = gx_sub.flatten()
    gy_flat = gy_sub.flatten()
    gz_flat = gz_sub.flatten()

    # Filter to region of interest (inside stella)
    r = np.sqrt(x_flat**2 + y_flat**2 + z_flat**2)
    mask = (r < 0.55) & (r > 0.15)

    # Normalize gradients
    mag = np.sqrt(gx_flat**2 + gy_flat**2 + gz_flat**2)
    mag = np.maximum(mag, 1e-10)

    return go.Cone(
        x=x_flat[mask],
        y=y_flat[mask],
        z=z_flat[mask],
        u=gx_flat[mask] / mag[mask],
        v=gy_flat[mask] / mag[mask],
        w=gz_flat[mask] / mag[mask],
        sizemode='absolute',
        sizeref=0.06,
        anchor='center',
        colorscale=[[0, 'cyan'], [0.5, 'white'], [1, 'magenta']],
        showscale=False,
        name='Phase gradient',
        opacity=0.7
    )


# =============================================================================
# MAIN VISUALIZATION
# =============================================================================

def create_phase_gradient_visualization():
    """Create the full interactive visualization for Prop 0.0.17k4."""

    extent = 0.7

    # Compute vmax from 2D slices (matching theorem_0_2_1)
    n_points = 80
    coords = np.linspace(-extent, extent, n_points)

    Xz, Yz = np.meshgrid(coords, coords)
    Zz = np.zeros_like(Xz)
    mag_z = np.abs(total_chiral_field_grid(Xz, Yz, Zz))

    Xy, Zy = np.meshgrid(coords, coords)
    Yy = np.zeros_like(Xy)
    mag_y = np.abs(total_chiral_field_grid(Xy, Yy, Zy))

    Yx, Zx = np.meshgrid(coords, coords)
    Xx = np.zeros_like(Yx)
    mag_x = np.abs(total_chiral_field_grid(Xx, Yx, Zx))

    vmax = max(mag_z.max(), mag_y.max(), mag_x.max())

    # Create 3D grid for isosurfaces
    n_iso = 60
    x_iso = np.linspace(-extent, extent, n_iso)
    y_iso = np.linspace(-extent, extent, n_iso)
    z_iso = np.linspace(-extent, extent, n_iso)
    X3d, Y3d, Z3d = np.meshgrid(x_iso, y_iso, z_iso, indexing='ij')

    # Compute field magnitude and RGB colors
    mag_3d = np.abs(total_chiral_field_grid(X3d, Y3d, Z3d))
    r_frac, g_frac, b_frac = compute_rgb_colors(X3d, Y3d, Z3d)

    # Compute phase gradient
    grad_x, grad_y, grad_z, grad_mag = compute_phase_gradient_field(X3d, Y3d, Z3d)

    # Create figure
    fig = go.Figure()

    # Add RGB-colored isosurfaces
    iso_levels = [0.1 * vmax, 0.3 * vmax, 0.5 * vmax, 0.7 * vmax]
    opacities = [0.25, 0.35, 0.45, 0.55]
    names = ['10% level', '30% level', '50% level', '70% level']

    for level, opacity, name in zip(iso_levels, opacities, names):
        trace = create_rgb_isosurface_trace(
            mag_3d, r_frac, g_frac, b_frac,
            x_iso, y_iso, z_iso, level, opacity, name
        )
        if trace:
            fig.add_trace(trace)

    # Add W-face (color singlet surface)
    fig.add_trace(create_w_face_surface())

    # Add stella octangula wireframe
    for trace in create_stella_traces():
        fig.add_trace(trace)

    # Add phase gradient cones
    fig.add_trace(create_gradient_cones(X3d, Y3d, Z3d, grad_x, grad_y, grad_z, spacing=8))

    # Layout
    fig.update_layout(
        title=dict(
            text='Prop 0.0.17k4: Z₃ Phase Structure & Gradients<br>'
                 '<sub>RGB color mixing | Cones show phase gradient direction | White triangle = W-face (color singlet)</sub>',
            x=0.5,
            font=dict(size=16)
        ),
        scene=dict(
            xaxis=dict(title='x', range=[-extent, extent]),
            yaxis=dict(title='y', range=[-extent, extent]),
            zaxis=dict(title='z', range=[-extent, extent]),
            aspectmode='cube',
            camera=dict(
                eye=dict(x=-1.8, y=-1.8, z=1.5),
                up=dict(x=0, y=0, z=1)
            )
        ),
        legend=dict(
            x=0.02,
            y=0.98,
            bgcolor='rgba(255,255,255,0.9)'
        ),
        margin=dict(l=0, r=0, t=80, b=0),
        width=1000,
        height=800
    )

    return fig


def main():
    """Main entry point."""
    import webbrowser
    import plotly.io as pio

    print("Creating phase gradient visualization for Prop 0.0.17k4...")

    fig = create_phase_gradient_visualization()

    # Save as HTML
    html_content = pio.to_html(fig, include_plotlyjs=True, full_html=True)

    # Add camera position display (same as theorem_0_2_1)
    camera_script = """
    <div id="camera-info" style="position: fixed; top: 10px; right: 10px; background: rgba(255,255,255,0.9);
         padding: 10px; border: 1px solid #ccc; border-radius: 5px; font-family: monospace; font-size: 12px; z-index: 1000;">
        <strong>Camera Position:</strong><br>
        <span id="camera-values">Rotate to see values</span>
    </div>
    <script>
    document.addEventListener('DOMContentLoaded', function() {
        var plotDiv = document.getElementsByClassName('plotly-graph-div')[0];
        if (plotDiv) {
            plotDiv.on('plotly_relayout', function(eventData) {
                if (eventData['scene.camera']) {
                    var cam = eventData['scene.camera'];
                    var eye = cam.eye || {x: 0, y: 0, z: 0};
                    var r = Math.sqrt(eye.x*eye.x + eye.y*eye.y + eye.z*eye.z);
                    var elev = Math.asin(eye.z / r) * 180 / Math.PI;
                    var azim = Math.atan2(eye.y, eye.x) * 180 / Math.PI;
                    var info = 'eye: (' + eye.x.toFixed(2) + ', ' + eye.y.toFixed(2) + ', ' + eye.z.toFixed(2) + ')<br>';
                    info += '<strong>elev: ' + elev.toFixed(1) + ', azim: ' + azim.toFixed(1) + '</strong>';
                    document.getElementById('camera-values').innerHTML = info;
                }
            });
        }
    });
    </script>
    """
    html_content = html_content.replace('</body>', camera_script + '</body>')

    html_path = '/tmp/prop_0_0_17k4_phase_gradients.html'
    with open(html_path, 'w') as f:
        f.write(html_content)

    print(f"Opening {html_path} in browser...")
    webbrowser.open(f'file://{html_path}')

    print("\nVisualization shows:")
    print("  - RGB-colored isosurfaces (color mixing based on field strengths)")
    print("  - W-face (white triangle) = color singlet where phases cancel")
    print("  - Cone glyphs = phase gradient direction (what vector excitations couple to)")
    print("  - Blue wireframe = T+ tetrahedron")
    print("  - Red wireframe = T- tetrahedron")
    print("Done!")


if __name__ == "__main__":
    main()
