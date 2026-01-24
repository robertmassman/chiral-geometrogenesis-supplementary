#!/usr/bin/env python3
"""
Interactive 3D Visualization for Theorem 0.2.1: Combined Orthogonal Slices

Uses Plotly to show the three orthogonal planes (x=0, y=0, z=0) with
|χ_total| field values, plus stella octangula wireframe.

This corresponds to Panel A of the combined visualization.

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
            line=dict(color='blue', width=4),
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
            line=dict(color='red', width=4),
            showlegend=False,
            hoverinfo='skip'
        ))

    # Color vertices
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
        marker=dict(size=12, color='white',
                   line=dict(color='black', width=2)),
        name='Origin (χ=0)',
        hoverinfo='name'
    ))

    return traces


def create_slice_surface(plane='z', offset=0, n_points=80, extent=0.7, vmax=None):
    """
    Create a Plotly Surface trace for a slice plane.

    Parameters:
    -----------
    plane : str
        Which plane: 'x', 'y', or 'z'
    offset : float
        The coordinate value where the plane is located
    n_points : int
        Grid resolution
    extent : float
        Spatial extent of the domain
    vmax : float
        Maximum value for colorscale normalization
    """
    coords = np.linspace(-extent, extent, n_points)

    if plane == 'z':
        # z = offset plane (horizontal)
        X, Y = np.meshgrid(coords, coords)
        Z = np.full_like(X, offset)
        mag = np.abs(total_chiral_field_grid(X, Y, Z))
        surface = go.Surface(
            x=X, y=Y, z=Z,
            surfacecolor=mag,
            colorscale='Viridis',
            cmin=0, cmax=vmax,
            opacity=0.85,
            showscale=True,
            colorbar=dict(
                title='|χ_total|',
                x=1.02,
                len=0.8
            ),
            name=f'z={offset} plane',
            hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>|χ|: %{surfacecolor:.2f}<extra>z=0 plane</extra>'
        )
    elif plane == 'y':
        # y = offset plane (vertical, front-back)
        X, Z = np.meshgrid(coords, coords)
        Y = np.full_like(X, offset)
        mag = np.abs(total_chiral_field_grid(X, Y, Z))
        surface = go.Surface(
            x=X, y=Y, z=Z,
            surfacecolor=mag,
            colorscale='Viridis',
            cmin=0, cmax=vmax,
            opacity=0.85,
            showscale=False,
            name=f'y={offset} plane',
            hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>|χ|: %{surfacecolor:.2f}<extra>y=0 plane</extra>'
        )
    elif plane == 'x':
        # x = offset plane (vertical, left-right)
        Y, Z = np.meshgrid(coords, coords)
        X = np.full_like(Y, offset)
        mag = np.abs(total_chiral_field_grid(X, Y, Z))
        surface = go.Surface(
            x=X, y=Y, z=Z,
            surfacecolor=mag,
            colorscale='Viridis',
            cmin=0, cmax=vmax,
            opacity=0.85,
            showscale=False,
            name=f'x={offset} plane',
            hovertemplate='x: %{x:.2f}<br>y: %{y:.2f}<br>z: %{z:.2f}<br>|χ|: %{surfacecolor:.2f}<extra>x=0 plane</extra>'
        )

    return surface


def create_interactive_slices_visualization():
    """Create the interactive 3D visualization with orthogonal slices."""

    extent = 0.7
    n_points = 80

    # Compute vmax from all three slices for consistent colormap
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

    # Create figure
    fig = go.Figure()

    # Add the three orthogonal slices
    fig.add_trace(create_slice_surface('z', 0, n_points, extent, vmax))
    fig.add_trace(create_slice_surface('y', 0, n_points, extent, vmax))
    fig.add_trace(create_slice_surface('x', 0, n_points, extent, vmax))

    # Add stella octangula wireframe
    for trace in create_stella_traces():
        fig.add_trace(trace)

    # Add plane labels as text annotations
    fig.add_trace(go.Scatter3d(
        x=[extent * 0.75], y=[extent * 0.75], z=[0.08],
        mode='text',
        text=['z=0'],
        textfont=dict(size=14, color='black'),
        showlegend=False,
        hoverinfo='skip'
    ))
    fig.add_trace(go.Scatter3d(
        x=[extent * 0.75], y=[0.08], z=[extent * 0.75],
        mode='text',
        text=['y=0'],
        textfont=dict(size=14, color='black'),
        showlegend=False,
        hoverinfo='skip'
    ))
    fig.add_trace(go.Scatter3d(
        x=[0.08], y=[extent * 0.75], z=[extent * 0.75],
        mode='text',
        text=['x=0'],
        textfont=dict(size=14, color='black'),
        showlegend=False,
        hoverinfo='skip'
    ))

    # Layout
    fig.update_layout(
        title=dict(
            text='Theorem 0.2.1: Combined Orthogonal Slices of |χ_total|<br><sub>Field vanishes at origin where three planes intersect</sub>',
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
    import sys

    print("Creating interactive 3D slices visualization...")
    fig = create_interactive_slices_visualization()

    # Save as HTML with camera position display
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

                    // Convert to spherical coordinates (approximate elev/azim)
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

    # Insert before closing body tag
    html_content = html_content.replace('</body>', camera_script + '</body>')

    # Write to file and open
    html_path = '/tmp/theorem_0_2_1_interactive_slices.html'
    with open(html_path, 'w') as f:
        f.write(html_content)

    import webbrowser
    print(f"Opening {html_path} in browser...")
    webbrowser.open(f'file://{html_path}')

    print("Done! Rotate the view to explore the combined orthogonal slices.")
    print("The camera position is displayed in the top-right corner.")


if __name__ == "__main__":
    main()
