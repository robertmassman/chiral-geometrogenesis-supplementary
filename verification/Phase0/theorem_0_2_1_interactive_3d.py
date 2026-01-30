#!/usr/bin/env python3
"""
Interactive 3D Visualization for Theorem 0.2.1: Total Field Isosurfaces

Uses Plotly for interactive rotation, zoom, and exploration.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import plotly.graph_objects as go
from skimage import measure

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


def individual_field_magnitudes(X, Y, Z, a0=A0, epsilon=EPSILON):
    """Compute magnitude of each color field separately."""
    mags = {}
    for c in ['R', 'G', 'B']:
        P_c = pressure_function_grid(X, Y, Z, VERTICES_PLUS[c], epsilon)
        mags[c] = a0 * P_c  # Magnitude (pressure function is real and positive)
    return mags


def compute_rgb_colors(X, Y, Z, a0=A0, epsilon=EPSILON):
    """
    Compute RGB colors based on field strengths at each point.
    Uses local normalization so colors are vivid everywhere.

    Returns arrays of R, G, B values in [0, 1].
    """
    mags = individual_field_magnitudes(X, Y, Z, a0, epsilon)

    r_mag = mags['R']
    g_mag = mags['G']
    b_mag = mags['B']

    # Local normalization: at each point, normalize by the LOCAL max of the three channels
    # This ensures vivid colors everywhere - the dominant field is always bright
    local_max = np.maximum(np.maximum(r_mag, g_mag), b_mag)
    local_max = np.maximum(local_max, 1e-10)  # Avoid division by zero

    r_frac = r_mag / local_max
    g_frac = g_mag / local_max
    b_frac = b_mag / local_max

    return r_frac, g_frac, b_frac


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
            line=dict(color='blue', width=3),
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
            line=dict(color='red', width=3),
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
        marker=dict(size=10, color='white',
                   line=dict(color='black', width=2)),
        name='Origin (χ=0)',
        hoverinfo='name'
    ))

    return traces


def create_isosurface_trace(mag_3d, x_iso, y_iso, z_iso, level, color, opacity, name):
    """Create a Plotly mesh trace for an isosurface with single color."""
    try:
        verts, faces, _, _ = measure.marching_cubes(mag_3d, level=level)

        # Scale vertices
        verts_scaled = np.zeros_like(verts)
        n_iso = len(x_iso)
        verts_scaled[:, 0] = x_iso[0] + verts[:, 0] * (x_iso[-1] - x_iso[0]) / (n_iso - 1)
        verts_scaled[:, 1] = y_iso[0] + verts[:, 1] * (y_iso[-1] - y_iso[0]) / (n_iso - 1)
        verts_scaled[:, 2] = z_iso[0] + verts[:, 2] * (z_iso[-1] - z_iso[0]) / (n_iso - 1)

        return go.Mesh3d(
            x=verts_scaled[:, 0],
            y=verts_scaled[:, 1],
            z=verts_scaled[:, 2],
            i=faces[:, 0],
            j=faces[:, 1],
            k=faces[:, 2],
            color=color,
            opacity=opacity,
            name=name,
            showlegend=True
        )
    except ValueError:
        return None


def create_rgb_isosurface_trace(mag_3d, r_frac, g_frac, b_frac, x_iso, y_iso, z_iso, level, opacity, name):
    """
    Create a Plotly mesh trace for an isosurface with RGB vertex colors
    based on field mixing at each vertex position.
    """
    try:
        verts, faces, _, _ = measure.marching_cubes(mag_3d, level=level)

        # Scale vertices to real coordinates
        verts_scaled = np.zeros_like(verts)
        n_iso = len(x_iso)
        verts_scaled[:, 0] = x_iso[0] + verts[:, 0] * (x_iso[-1] - x_iso[0]) / (n_iso - 1)
        verts_scaled[:, 1] = y_iso[0] + verts[:, 1] * (y_iso[-1] - y_iso[0]) / (n_iso - 1)
        verts_scaled[:, 2] = z_iso[0] + verts[:, 2] * (z_iso[-1] - z_iso[0]) / (n_iso - 1)

        # Interpolate RGB fractions at vertex positions
        # verts contains indices into the grid, use them to interpolate
        from scipy.interpolate import RegularGridInterpolator

        # Create interpolators for each color channel
        r_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), r_frac, method='linear', bounds_error=False, fill_value=0.33)
        g_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), g_frac, method='linear', bounds_error=False, fill_value=0.33)
        b_interp = RegularGridInterpolator((x_iso, y_iso, z_iso), b_frac, method='linear', bounds_error=False, fill_value=0.33)

        # Get RGB values at each vertex
        r_vals = r_interp(verts_scaled)
        g_vals = g_interp(verts_scaled)
        b_vals = b_interp(verts_scaled)

        # Convert to RGB color strings for each vertex
        # Scale to 0-255 range
        r_255 = np.clip(r_vals * 255, 0, 255).astype(int)
        g_255 = np.clip(g_vals * 255, 0, 255).astype(int)
        b_255 = np.clip(b_vals * 255, 0, 255).astype(int)

        # Create color array for vertices
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


def create_interactive_visualization():
    """Create the full interactive 3D visualization with RGB color mixing."""

    extent = 0.7

    # Compute vmax from 2D slices (matching static version)
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

    mag_3d = np.abs(total_chiral_field_grid(X3d, Y3d, Z3d))

    # Compute RGB color fractions based on field mixing
    r_frac, g_frac, b_frac = compute_rgb_colors(X3d, Y3d, Z3d)

    # Create figure
    fig = go.Figure()

    # Add isosurfaces with RGB coloring based on field mixing
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

    # Add stella octangula
    for trace in create_stella_traces():
        fig.add_trace(trace)

    # Layout
    fig.update_layout(
        title=dict(
            text='Theorem 0.2.1: Isosurfaces of |χ_total|<br><sub>Rotate, zoom, and explore the 3D structure</sub>',
            x=0.5,
            font=dict(size=18)
        ),
        scene=dict(
            xaxis=dict(title='x', range=[-extent, extent]),
            yaxis=dict(title='y', range=[-extent, extent]),
            zaxis=dict(title='z', range=[-extent, extent]),
            aspectmode='cube',
            camera=dict(
                # W vertex at (-1,-1,1)/sqrt(3) points toward camera
                # Camera looks from W direction toward origin
                eye=dict(x=-1.8, y=-1.8, z=1.5),
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


def export_two_panel_figure():
    """
    Export two static images from different camera angles and combine into a two-panel figure.
    Uses Plotly's kaleido backend for high-quality PNG export.
    """
    import os
    from PIL import Image

    print("Creating figure for export...")
    fig = create_interactive_visualization()

    # Remove the title for cleaner panel images
    fig.update_layout(title=None, margin=dict(l=0, r=0, t=0, b=0))

    # Define camera positions (matching the matplotlib version)
    # View 1: W vertex toward viewer (eye at roughly elev=25, azim=225)
    camera_view1 = dict(
        eye=dict(x=-1.8, y=-1.8, z=1.5),
        up=dict(x=0, y=0, z=1)
    )

    # View 2: View from below (eye at roughly elev=-20, azim=-136)
    camera_view2 = dict(
        eye=dict(x=-1.87, y=-1.83, z=-1.38),
        up=dict(x=0, y=0, z=1)
    )

    views = [
        (camera_view1, '(a) W vertex toward viewer'),
        (camera_view2, '(b) Profile view'),
    ]

    # Output directory
    plots_dir = os.path.join(os.path.dirname(__file__), '..', '..', 'verification', 'plots')
    plots_dir = os.path.normpath(plots_dir)
    os.makedirs(plots_dir, exist_ok=True)

    panel_images = []
    panel_width = 800
    panel_height = 700

    for i, (camera, title) in enumerate(views):
        # Update camera position
        fig.update_layout(
            scene_camera=camera,
            width=panel_width,
            height=panel_height
        )

        # Export to PNG
        temp_path = f'/tmp/theorem_0_2_1_panel_{i}.png'
        print(f"Exporting {title}...")
        fig.write_image(temp_path, scale=2)  # scale=2 for higher resolution
        panel_images.append(temp_path)

    # Combine into two-panel figure using PIL
    print("Combining panels...")
    img1 = Image.open(panel_images[0])
    img2 = Image.open(panel_images[1])

    # Create combined image with space for titles
    title_height = 60
    combined_width = img1.width + img2.width + 40  # 40px gap
    combined_height = max(img1.height, img2.height) + title_height + 80  # space for suptitle

    from PIL import ImageDraw, ImageFont

    combined = Image.new('RGB', (combined_width, combined_height), 'white')

    # Paste images
    combined.paste(img1, (0, title_height + 40))
    combined.paste(img2, (img1.width + 40, title_height + 40))

    # Add titles
    draw = ImageDraw.Draw(combined)

    # Try to use a nice font, fall back to default
    try:
        title_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 36)
        subtitle_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 28)
    except (IOError, OSError):
        title_font = ImageFont.load_default()
        subtitle_font = ImageFont.load_default()

    # Main title
    main_title = "Isosurfaces of |χ_total| - Two Orientations"
    bbox = draw.textbbox((0, 0), main_title, font=title_font)
    title_x = (combined_width - (bbox[2] - bbox[0])) // 2
    draw.text((title_x, 15), main_title, fill='black', font=title_font)

    # Panel titles
    draw.text((img1.width // 2 - 150, title_height + 10), "(a) W vertex toward viewer",
              fill='black', font=subtitle_font)
    draw.text((img1.width + 40 + img2.width // 2 - 100, title_height + 10), "(b) View from below",
              fill='black', font=subtitle_font)

    # Save combined figure
    output_path = os.path.join(plots_dir, 'theorem_0_2_1_isosurface_two_views_plotly.png')
    combined.save(output_path, dpi=(150, 150))
    print(f"Saved combined figure to {output_path}")

    # Clean up temp files
    for path in panel_images:
        os.remove(path)

    return output_path


def main():
    """Main entry point."""
    import sys

    # Check for --export flag
    if '--export' in sys.argv:
        export_two_panel_figure()
        return

    print("Creating interactive 3D visualization...")
    fig = create_interactive_visualization()

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
    html_path = '/tmp/theorem_0_2_1_interactive_3d.html'
    with open(html_path, 'w') as f:
        f.write(html_content)

    import webbrowser
    print(f"Opening {html_path} in browser...")
    webbrowser.open(f'file://{html_path}')

    print("Done! Rotate the view and check the camera position display in the top-right corner.")


if __name__ == "__main__":
    main()
