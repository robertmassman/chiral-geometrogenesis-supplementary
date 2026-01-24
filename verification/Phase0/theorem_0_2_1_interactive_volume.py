#!/usr/bin/env python3
"""
Interactive 3D Volume Rendering for Theorem 0.2.1: Total Chiral Field

Uses Plotly's Volume trace to render the full 3D field |χ_total| with
color-mapped transparency throughout the volume.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import plotly.graph_objects as go

# =============================================================================
# CONSTANTS
# =============================================================================

EPSILON = 0.05
A0 = 1.0

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

# Stella octangula vertices
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

VERTICES_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}


# =============================================================================
# CORE FUNCTIONS
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


def create_stella_traces():
    """Create Plotly traces for stella octangula wireframe."""
    traces = []

    # T+ tetrahedron (blue)
    t_plus = [VERTICES_PLUS[k] for k in ['R', 'G', 'B', 'W']]
    edges_plus = [
        (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)
    ]

    for i, j in edges_plus:
        traces.append(go.Scatter3d(
            x=[t_plus[i][0], t_plus[j][0]],
            y=[t_plus[i][1], t_plus[j][1]],
            z=[t_plus[i][2], t_plus[j][2]],
            mode='lines',
            line=dict(color='blue', width=5),
            showlegend=False,
            hoverinfo='skip'
        ))

    # T- tetrahedron (red)
    t_minus = [VERTICES_MINUS[k] for k in ['R_bar', 'G_bar', 'B_bar', 'W_bar']]
    edges_minus = [
        (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)
    ]

    for i, j in edges_minus:
        traces.append(go.Scatter3d(
            x=[t_minus[i][0], t_minus[j][0]],
            y=[t_minus[i][1], t_minus[j][1]],
            z=[t_minus[i][2], t_minus[j][2]],
            mode='lines',
            line=dict(color='red', width=5),
            showlegend=False,
            hoverinfo='skip'
        ))

    # Color vertices
    colors_map = {'R': 'red', 'G': 'green', 'B': 'blue', 'W': 'gray'}
    for name, v in VERTICES_PLUS.items():
        traces.append(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers',
            marker=dict(size=10, color=colors_map[name],
                       line=dict(color='black', width=1)),
            name=f'{name} vertex',
            hoverinfo='name'
        ))

    # Origin marker
    traces.append(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=14, color='white',
                   line=dict(color='black', width=2)),
        name='Origin (χ=0)',
        hoverinfo='name'
    ))

    return traces


def create_volume_visualization():
    """Create 3D volume by stacking many parallel 2D slices."""

    extent = 0.7
    n_points = 50  # Resolution of each slice
    n_slices = 25  # Number of slices in each direction

    # Compute vmax from a sample slice for consistent colormap
    coords = np.linspace(-extent, extent, n_points)
    Xz, Yz = np.meshgrid(coords, coords)
    Zz = np.zeros_like(Xz)
    mag_sample = np.abs(total_chiral_field_grid(Xz, Yz, Zz))
    vmax = mag_sample.max() * 1.2  # Slightly higher to account for all slices

    # Create figure
    fig = go.Figure()

    # Custom colorscale with transparency for low values (blue regions)
    # Format: [position, 'rgba(r,g,b,a)']
    # Viridis-like but with alpha channel: low values are more transparent
    custom_colorscale = [
        [0.0, 'rgba(68, 1, 84, 0.02)'],     # Dark purple, nearly invisible
        [0.15, 'rgba(70, 50, 127, 0.05)'],  # Purple, very transparent
        [0.3, 'rgba(54, 92, 141, 0.1)'],    # Blue, very transparent
        [0.45, 'rgba(39, 127, 142, 0.2)'],  # Teal, mostly transparent
        [0.6, 'rgba(31, 161, 135, 0.4)'],   # Green-teal, semi-transparent
        [0.75, 'rgba(74, 194, 109, 0.6)'],  # Green, less transparent
        [0.9, 'rgba(159, 218, 58, 0.85)'],  # Yellow-green, mostly opaque
        [1.0, 'rgba(253, 231, 37, 1.0)'],   # Yellow, fully opaque
    ]

    # Stack of Z slices (horizontal planes at different heights)
    z_positions = np.linspace(-extent, extent, n_slices)
    for i, z_val in enumerate(z_positions):
        X, Y = np.meshgrid(coords, coords)
        Z = np.full_like(X, z_val)
        mag = np.abs(total_chiral_field_grid(X, Y, Z))

        # Only show colorbar for first slice
        show_colorbar = (i == 0)

        fig.add_trace(go.Surface(
            x=X, y=Y, z=Z,
            surfacecolor=mag,
            colorscale=custom_colorscale,
            cmin=0, cmax=vmax,
            opacity=1.0,
            showscale=show_colorbar,
            colorbar=dict(
                title='|χ_total|',
                x=1.02,
                len=0.8
            ) if show_colorbar else None,
            name=f'z={z_val:.2f}',
            hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>|χ|: %{surfacecolor:.2f}<extra></extra>',
            showlegend=False
        ))

    # Stack of Y slices (vertical planes, front-to-back)
    y_positions = np.linspace(-extent, extent, n_slices)
    for i, y_val in enumerate(y_positions):
        X, Z = np.meshgrid(coords, coords)
        Y = np.full_like(X, y_val)
        mag = np.abs(total_chiral_field_grid(X, Y, Z))

        fig.add_trace(go.Surface(
            x=X, y=Y, z=Z,
            surfacecolor=mag,
            colorscale=custom_colorscale,
            cmin=0, cmax=vmax,
            opacity=1.0,
            showscale=False,
            name=f'y={y_val:.2f}',
            hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>|χ|: %{surfacecolor:.2f}<extra></extra>',
            showlegend=False
        ))

    # Stack of X slices (vertical planes, left-to-right)
    x_positions = np.linspace(-extent, extent, n_slices)
    for i, x_val in enumerate(x_positions):
        Y, Z = np.meshgrid(coords, coords)
        X = np.full_like(Y, x_val)
        mag = np.abs(total_chiral_field_grid(X, Y, Z))

        fig.add_trace(go.Surface(
            x=X, y=Y, z=Z,
            surfacecolor=mag,
            colorscale=custom_colorscale,
            cmin=0, cmax=vmax,
            opacity=1.0,
            showscale=False,
            name=f'x={x_val:.2f}',
            hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>|χ|: %{surfacecolor:.2f}<extra></extra>',
            showlegend=False
        ))

    # Add stella octangula wireframe
    for trace in create_stella_traces():
        fig.add_trace(trace)

    # Layout
    fig.update_layout(
        title=dict(
            text='Theorem 0.2.1: Volume Rendering of |χ_total|<br><sub>Full 3D field structure - darker regions have higher field magnitude</sub>',
            x=0.5,
            font=dict(size=18)
        ),
        scene=dict(
            xaxis=dict(title='x', range=[-extent, extent]),
            yaxis=dict(title='y', range=[-extent, extent]),
            zaxis=dict(title='z', range=[-extent, extent]),
            aspectmode='cube',
            camera=dict(
                eye=dict(x=1.5, y=1.5, z=1.2),
                up=dict(x=0, y=0, z=1)
            )
        ),
        legend=dict(
            x=0.02,
            y=0.98,
            bgcolor='rgba(255,255,255,0.8)'
        ),
        margin=dict(l=0, r=0, t=60, b=0),
        width=900,
        height=700
    )

    return fig


def main():
    """Main entry point."""
    print("Creating interactive 3D volume rendering...")
    fig = create_volume_visualization()

    # Save as HTML
    import plotly.io as pio

    html_content = pio.to_html(fig, include_plotlyjs=True, full_html=True)

    # Inject JavaScript to display camera position
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

    html_path = '/tmp/theorem_0_2_1_interactive_volume.html'
    with open(html_path, 'w') as f:
        f.write(html_content)

    import webbrowser
    print(f"Opening {html_path} in browser...")
    webbrowser.open(f'file://{html_path}')

    print("Done! Rotate to explore the full 3D volume rendering.")


if __name__ == "__main__":
    main()
