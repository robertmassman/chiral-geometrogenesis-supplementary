#!/usr/bin/env python3
"""
Isosurface Visualization for Theorem 0.2.1: Total Field Superposition

Shows isosurfaces of |χ_total| demonstrating the 3D structure of the
pressure-modulated chiral field superposition. The field vanishes at
the origin (color-neutral point) and peaks near each color vertex.

Uses Plotly for true 3D rendering with proper depth compositing, then
exports to high-quality static images.

Output: fig_thm_0_2_1_isosurface.pdf and fig_thm_0_2_1_isosurface.png

Usage:
    python fig_thm_0_2_1_isosurface.py
"""

import numpy as np
import plotly.graph_objects as go
from skimage import measure
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

# Output directory
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

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
    """Create a Plotly mesh trace for an isosurface."""
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


def create_visualization():
    """Create the 3D visualization figure."""

    extent = 0.7

    # Compute vmax from 2D slices
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

    # Create figure
    fig = go.Figure()

    # Add isosurfaces (including 10% outermost shell)
    iso_levels = [0.1 * vmax, 0.3 * vmax, 0.5 * vmax, 0.7 * vmax]
    colors = ['#053061', '#2166ac', '#92c5de', '#f4a582']  # Dark blue for 10%
    opacities = [0.2, 0.3, 0.4, 0.5]
    names = ['10% level', '30% level', '50% level', '70% level']

    for level, color, opacity, name in zip(iso_levels, colors, opacities, names):
        trace = create_isosurface_trace(mag_3d, x_iso, y_iso, z_iso, level, color, opacity, name)
        if trace:
            fig.add_trace(trace)

    # Add stella octangula
    for trace in create_stella_traces():
        fig.add_trace(trace)

    # Layout (no title for paper figure - caption handles that)
    fig.update_layout(
        scene=dict(
            xaxis=dict(title='x', range=[-extent, extent]),
            yaxis=dict(title='y', range=[-extent, extent]),
            zaxis=dict(title='z', range=[-extent, extent]),
            aspectmode='cube',
        ),
        legend=dict(
            x=0.02,
            y=0.98,
            bgcolor='rgba(255,255,255,0.8)'
        ),
        margin=dict(l=0, r=0, t=0, b=0),
    )

    return fig


def export_two_panel_figure():
    """
    Export two static images from different camera angles and combine into a two-panel figure.
    Uses Plotly's kaleido backend for high-quality PNG export.
    """
    import tempfile

    print("Creating figure for export...")
    fig = create_visualization()

    # Define camera positions
    # View 1: W vertex toward viewer (eye at roughly elev=25, azim=225)
    camera_view1 = dict(
        eye=dict(x=-1.8, y=-1.8, z=1.5),
        up=dict(x=0, y=0, z=1)
    )

    # View 2: Profile view (eye at roughly elev=-20, azim=-136)
    camera_view2 = dict(
        eye=dict(x=-1.87, y=-1.83, z=-1.38),
        up=dict(x=0, y=0, z=1)
    )

    views = [
        (camera_view1, '(a) W vertex toward viewer'),
        (camera_view2, '(b) Profile view'),
    ]

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
        temp_path = tempfile.mktemp(suffix=f'_panel_{i}.png')
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
    combined_height = max(img1.height, img2.height) + title_height + 20

    combined = Image.new('RGB', (combined_width, combined_height), 'white')

    # Paste images
    combined.paste(img1, (0, title_height + 10))
    combined.paste(img2, (img1.width + 40, title_height + 10))

    # Add titles
    draw = ImageDraw.Draw(combined)

    # Try to use a nice font, fall back to default
    try:
        subtitle_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 28)
    except (IOError, OSError):
        try:
            subtitle_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 28)
        except (IOError, OSError):
            subtitle_font = ImageFont.load_default()

    # Panel titles (no main title - LaTeX caption handles that)
    draw.text((img1.width // 2 - 150, 15), "(a) W vertex toward viewer",
              fill='black', font=subtitle_font)
    draw.text((img1.width + 40 + img2.width // 2 - 100, 15), "(b) Profile view",
              fill='black', font=subtitle_font)

    # Save combined figure as PNG
    png_path = output_dir / 'fig_thm_0_2_1_isosurface.png'
    combined.save(str(png_path), dpi=(300, 300))
    print(f"Saved PNG to {png_path}")

    # Convert to PDF for LaTeX
    pdf_path = output_dir / 'fig_thm_0_2_1_isosurface.pdf'
    # Use RGB mode for PDF
    combined_rgb = combined.convert('RGB')
    combined_rgb.save(str(pdf_path), 'PDF', resolution=300)
    print(f"Saved PDF to {pdf_path}")

    # Clean up temp files
    import os
    for path in panel_images:
        os.remove(path)

    return png_path, pdf_path


def main():
    """Main entry point."""
    print("=" * 70)
    print("Theorem 0.2.1: Total Field Isosurface Visualization")
    print("=" * 70)

    png_path, pdf_path = export_two_panel_figure()

    print("\nDone!")
    print(f"PNG: {png_path}")
    print(f"PDF: {pdf_path}")


if __name__ == "__main__":
    main()
